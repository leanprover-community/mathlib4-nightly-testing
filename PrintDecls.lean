import Lean

/-!
# `printDecls` — list the declarations a module adds

A standalone CLI tool. Given a module name, it imports that module and prints the name
and pretty-printed type of every declaration the module added to the environment — i.e.
every constant stored in the module's `.olean`, which is exactly what its commands
produced via `addDecl`, including auxiliary and compiler-generated declarations.

Usage:
```
lake exe printDecls Mathlib.My.Module.Path
```

The target module must already be built (its `.olean` must exist). `lake exe` sets up
`LEAN_PATH` so the import resolves against the package's build output.
-/

open Lean

/-- Import `modName` and print `name : type` for every constant it defines. -/
def printModuleDecls (modName : Name) : IO Unit := unsafe do
  initSearchPath (← findSysroot)
  -- Extension initializers must be runnable before we can load extension state.
  enableInitializersExecution
  -- `loadExts := true` is required so that environment-extension state (e.g. the
  -- `@[app_unexpander]` table) is populated; without it the pretty printer cannot
  -- recover notation such as `=`, `≤`, `∧` and prints raw application form instead.
  let env ← importModules #[{ module := modName }] (opts := {}) (trustLevel := 1024)
    (loadExts := true)
  try
    let some modIdx := env.getModuleIdx? modName
      | throw <| IO.userError s!"module '{modName}' is not present in the imported environment"
    let mod := env.header.moduleData[modIdx.toNat]!
    let ctx : Core.Context := { fileName := "<printDecls>", fileMap := default }
    let state : Core.State := { env }
    -- Delaborate each type in `MetaM` to get its pretty-printed form.
    let act : CoreM Unit := Meta.MetaM.run' do
      for ci in mod.constants do
        -- Skip private declarations and compiler/elaborator-internal ones
        -- (`.match_1`, equation lemmas, `._simp_1`, etc.).
        if isPrivateName ci.name || ci.name.isInternalDetail then continue
        let fmt ← Meta.ppExpr ci.type
        IO.println s!"{ci.name} : {fmt.pretty}"
    discard <| act.toIO ctx state
  finally
    env.freeRegions

def main (args : List String) : IO UInt32 := do
  match args with
  | [modStr] =>
    printModuleDecls modStr.toName
    return 0
  | _ =>
    IO.eprintln "usage: lake exe printDecls Module.Name"
    return 1
