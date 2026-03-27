import Lake

open Lake DSL

/-!
## Mathlib dependencies on upstream projects
-/

require "leanprover-community" / "batteries" from git "https://github.com/leanprover-community/batteries" @ "bump_to_v4.29.0"
require "leanprover-community" / "Qq" @ git "master"
require "leanprover-community" / "aesop" @ git "master"
require "leanprover-community" / "proofwidgets" @ git "v0.0.94" -- ProofWidgets should always be pinned to a specific version
  with NameMap.empty.insert `errorOnBuild
    "ProofWidgets not up-to-date. \
    Please run `lake exe cache get` to fetch the latest ProofWidgets. \
    If this does not work, report your issue on the Lean Zulip."
require "leanprover-community" / "importGraph" @ git "main"
require "leanprover-community" / "LeanSearchClient" @ git "main"
require "leanprover-community" / "plausible" @ git "main"


/-!
## Options for building mathlib
-/

/-- These options are used as `leanOptions`, prefixed by `` `weak``, so that
`lake build` uses them, as well as `Archive` and `Counterexamples`. -/
abbrev mathlibOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  -- Explicitly enable the header linter, since the standard set is defined in `Mathlib.Init`
  -- but we want to run this linter in files imported by `Mathlib.Init`.
  ⟨`linter.style.header, true⟩,
  ⟨`linter.checkInitImports, true⟩,
  ⟨`linter.allScriptsDocumented, true⟩,
  ⟨`linter.pythonStyle, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  -- ⟨`linter.nightlyRegressionSet, true⟩,
  -- `latest_import.yml` uses this comment: if you edit it, make sure that the workflow still works
]

/-- These options are passed as `leanOptions` to building mathlib, as well as the
`Archive` and `Counterexamples`. (`tests` omits the first two options.) -/
abbrev mathlibLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
  ] ++ -- options that are used in `lake build`
    mathlibOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package mathlib where
  testDriver := "MathlibTest"
  -- These are additional settings which do not affect the lake hash,
  -- so they can be enabled in CI and disabled locally or vice versa.
  -- Warning: Do not put any options here that actually change the olean files,
  -- or inconsistent behavior may result
  -- weakLeanArgs := #[]

/-!
## Mathlib libraries
-/

@[default_target]
lean_lib Mathlib where
  -- Enforce Mathlib's default linters and style options.
  leanOptions := mathlibLeanOptions

-- NB. When adding further libraries, check if they should be excluded from `getLeanLibs` in
-- `scripts/mk_all.lean`.
lean_lib Cache where
  globs := #[`Cache.+]

lean_lib MathlibTest where
  globs := #[`MathlibTest.+]

lean_lib Archive where
  leanOptions := mathlibLeanOptions

lean_lib Counterexamples where
  leanOptions := mathlibLeanOptions

/-- Additional documentation in the form of modules that only contain module docstrings. -/
lean_lib docs where
  roots := #[`docs]

/-!
## Executables provided by Mathlib
-/

/--
`lake exe autolabel 150100` adds a topic label to PR `150100` if there is a unique choice.
This requires GitHub CLI `gh` to be installed!

Calling `lake exe autolabel` without a PR number will print the result without applying
any labels online.
-/
lean_exe autolabel where
  srcDir := "scripts"

/-- `lake exe cache get` retrieves precompiled `.olean` files from a central server. -/
lean_exe cache where
  root := `Cache.Main

/-- `lake exe check-yaml` verifies that all declarations referred to in `docs/*.yaml` files exist. -/
lean_exe «check-yaml» where
  srcDir := "scripts"
  supportInterpreter := true

/-- `lake exe mk_all` constructs the files containing all imports for a project. -/
lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/-- `lake exe lint-style` runs text-based style linters. -/
lean_exe «lint-style» where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/-- `lake exe check-title-labels` checks if a PR title obeys some basic formatting requirements.
Currently, these checks are quite lenient, but could be made stricter in the future. -/
lean_exe «check_title_labels» where
  srcDir := "scripts"

/-- `lake exe nightly-testing-checklist` reports nightly-testing branch status. -/
lean_exe «nightly-testing-checklist» where
  srcDir := "scripts"

lean_exe mathlib_test_executable where
  root := `MathlibTest.MathlibTestExecutable

/-!
## Other configuration
-/

/--
When a package depending on Mathlib updates its dependencies,
update its toolchain to match Mathlib's and fetch the new cache.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.baseName = pkg.baseName then
    return -- do not run in Mathlib itself
  if (← IO.getEnv "MATHLIB_NO_CACHE_ON_UPDATE") != some "1" then
    -- Check if Lake version matches toolchain version
    let toolchainFile := rootPkg.dir / "lean-toolchain"
    let toolchainContent ← IO.FS.readFile toolchainFile
    let toolchainVersion := match toolchainContent.trimAscii.copy.splitOn ":" with
      | [_, version] => version
      | _ => toolchainContent.trimAscii.copy  -- fallback to full content if format is unexpected
    -- Lean.versionString does not start with a `v`, while the `lean-toolchain` file is flexible.
    let toolchainVersion := (toolchainVersion.dropPrefix "v").copy
    if Lean.versionString ≠ toolchainVersion then
      IO.println s!"Not running `lake exe cache get` yet, as \
        the `lake` version ({Lean.versionString}) does not match \
        the toolchain version ({toolchainVersion}) in the project.\n\
        You should run `lake exe cache get` manually."
      return
    let exeFile ← runBuild cache.fetch
    -- Run the command in the root package directory,
    -- which is the one that holds the .lake folder and lean-toolchain file.
    let cwd ← IO.Process.getCurrentDir
    let exitCode ← try
      IO.Process.setCurrentDir rootPkg.dir
      env exeFile.toString #["get"]
    finally
      IO.Process.setCurrentDir cwd
    if exitCode ≠ 0 then
      error s!"{pkg.baseName}: failed to fetch cache"
