module

import MathlibTest.UnusedInstancesInType.Basic
import Mathlib.Data.Fintype.EquivFin

set_option linter.mathlibStandardset true

section unused

/--
warning: `foo` has the hypothesis:
  • [Fintype α] (#2)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo {α} [Fintype α] : True := True.intro

def Foo (α) [Fintype α] := Unit

#guard_msgs in
theorem bar {α} [Fintype α] (s : Foo α) : s = s := rfl

/--
warning: `foo₂` has the hypotheses:
  • [(α : Type) → Fintype α] (#2)
  • [Fintype a] (#4)
which are not used in the remainder of the type.

Consider replacing these hypotheses with the corresponding instances of `Finite` and using `Fintype.ofFinite` in the proof, or removing them entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo₂ (a : Type) [∀ α : Type, Fintype α] (_ : Unit) [Fintype a] : True :=
  trivial

/--
warning: `foo₃` has the hypotheses:
  • [(α : Type) → Fintype α] (#2)
  • [Fintype β] (#3)
which are not used in the remainder of the type.

Consider replacing these hypotheses with the corresponding instances of `Finite` and using `Fintype.ofFinite` in the proof, or removing them entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo₃ {β} [∀ α : Type, Fintype α] [Fintype β] : True := trivial

-- See through `let`, don't count it as an index
/--
warning: `foo₄` has the hypothesis:
  • [Fintype β] (#2)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo₄ {β} : let _ := 2; ∀ [Fintype β], True := trivial

-- Linter should not fire when `sorry` appears in the type, even though the instances are unused
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem fooSorry {β} [∀ α : Type, Fintype α] [Fintype β] (b : sorry) : True :=
  trivial

end unused

section used

/- The linter either should not fire on these declarations because the instance hypotheses are used
in the type, or not fire on *every* instance in these declarations. -/

theorem fooUsing [Fintype (Nat → Nat)] : Uses (Fintype (Nat → Nat)) := trivial

theorem fooUsing₁ [Fintype (Nat → Nat)] : Uses (Fintype (Nat → Nat)) → True :=
  fun _ => trivial

-- Should fire on parameter #1 but not parameter #2
/--
warning: `fooUsing₂` has the hypothesis:
  • [Fintype Bool] (#1)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem fooUsing₂ [Fintype Bool] [Fintype (Nat → Nat)] :
    Uses (Fintype (Nat → Nat)) → True :=
  fun _ => trivial

-- Note `optParam` test
theorem fooUsing₃ [Fintype Bool] [Fintype (Nat → Nat)]
    (_ : Uses (Fintype Bool) := trivial) : Uses (Fintype (Nat → Nat)) → True :=
  fun _ => trivial

set_option linter.unusedFintypeInType false in
theorem fooUsing₂' [Fintype Bool] [Fintype (Nat → Nat)] :
    Uses (Fintype (Nat → Nat)) → True :=
  fun _ => trivial

end used

section importFintypeOfFinite

/-!
Checks that `Fintype.ofFinite` is located in `Mathlib.Data.Fintype.EquivFin`, which is relevant for the message displayed in `MathlibTest.UnusedInstancesInType.Fintype.NeedingImport`.

If this changes, the message should be updated to point to the correct module.
-/

open Lean in
/-- info: Module of `Fintype.ofFinite`: `Mathlib.Data.Fintype.EquivFin` -/
#guard_msgs in
run_cmd do
  let some modName := (← getEnv).getModuleFor? `Fintype.ofFinite
    | throwError "Could not find `Fintype.ofFinite`"
  logInfo m!"Module of `Fintype.ofFinite`: `{modName}`"

end importFintypeOfFinite
