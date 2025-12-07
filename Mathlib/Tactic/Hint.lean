/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean.Meta.Tactic.TryThis
public meta import Batteries.Linter.UnreachableTactic
public meta import Batteries.Control.Nondet.Basic
public import Mathlib.Init
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Mathlib.Tactic.Basic

/-!
# The `hint` tactic (deprecated).

The `hint` tactic is deprecated in favor of `try?`, which is built into Lean 4.26.0+.

Use `register_try?_tactic (priority := N) <tactic>` to register tactics with `try?`.

The `hint` tactic and `register_hint` command are kept for backward compatibility
but will be removed in a future release.
-/

public meta section

open Lean Elab Tactic

open Lean.Meta.Tactic.TryThis

namespace Mathlib.Tactic.Hint

/-- An environment extension for registering hint tactics with priorities. (Deprecated) -/
@[deprecated "Use `register_try?_tactic` instead" (since := "2025-12-08")]
initialize hintExtension :
    SimplePersistentEnvExtension (Nat × TSyntax `tactic) (List (Nat × TSyntax `tactic)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/-- Register a new hint tactic. (Deprecated) -/
@[deprecated "Use `register_try?_tactic` instead" (since := "2025-12-08")]
def addHint (prio : Nat) (stx : TSyntax `tactic) : CoreM Unit := do
  modifyEnv fun env => hintExtension.addEntry env (prio, stx)

/-- Return the list of registered hint tactics. (Deprecated) -/
@[deprecated "Use `register_try?_tactic` instead" (since := "2025-12-08")]
def getHints : CoreM (List (Nat × TSyntax `tactic)) :=
  return hintExtension.getState (← getEnv)

open Lean.Elab.Command in
/--
Register a tactic for use with the `hint` tactic, e.g. `register_hint 1000 simp_all`.
(Deprecated: use `register_try?_tactic (priority := N) <tactic>` instead)

The numeric argument specifies the priority: tactics with larger priorities run before
those with smaller priorities. The priority must be provided explicitly.
-/
@[deprecated "Use `register_try?_tactic` instead" (since := "2025-12-08")]
elab (name := registerHintStx)
    "register_hint" prio:num tac:tactic : command =>
    liftTermElabM do
  let tac : TSyntax `tactic := ⟨tac.raw.copyHeadTailInfoFrom .missing⟩
  let some prio := prio.raw.isNatLit?
    | throwError "expected a numeric literal for priority"
  addHint prio tac

initialize
  Batteries.Linter.UnreachableTactic.ignoreTacticKindsRef.modify fun s => s.insert ``registerHintStx

/--
Construct a suggestion for a tactic.
* Check the passed `MessageLog` for an info message beginning with "Try this: ".
* If found, use that as the suggestion.
* Otherwise use the provided syntax.
* Also, look for remaining goals and pretty print them after the suggestion.
(Deprecated)
-/
@[deprecated "Use `try?` instead" (since := "2025-12-08")]
def suggestion (tac : TSyntax `tactic) (trees : PersistentArray InfoTree) : TacticM Suggestion := do
  -- TODO `addExactSuggestion` has an option to construct `postInfo?`
  -- Factor that out so we can use it here instead of copying and pasting?
  let goals ← getGoals
  let postInfo? ← if goals.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in goals do
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure (some str)
  /-
  #adaptation_note 2025-08-27
  Suggestion styling was deprecated in lean4#9966.
  We use emojis for now instead.
  -/
  -- let style? := if goals.isEmpty then some .success else none
  let preInfo? := if goals.isEmpty then some "🎉 " else none
  let suggestions := collectTryThisSuggestions trees
  let suggestion := match suggestions[0]? with
  | some s => s.suggestion
  | none => SuggestionText.tsyntax tac
  return { preInfo?, suggestion, postInfo? }

/--
The `hint` tactic is deprecated in favor of `try?`.

The `try?` tactic provides similar functionality by trying multiple tactics
and reporting successes. Register tactics using:
`register_try?_tactic (priority := N) <tactic>`

Note: User-registered tactics run after built-in `try?` strategies.
-/
@[deprecated "Use `try?` instead" (since := "2025-12-08")]
syntax (name := hintStx) "hint" : tactic

elab_rules : tactic
  | `(tactic| hint) => do
    logWarning "The `hint` tactic is deprecated. Use `try?` instead."
    evalTactic (← `(tactic| try?))

end Mathlib.Tactic.Hint
