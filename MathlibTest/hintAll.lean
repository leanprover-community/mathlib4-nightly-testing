import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Common
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.TautoSet

/--
info: Try these:
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example (h : 1 < 0) : False := by try?

/--
info: Try these:
  [apply] solve_by_elim
  [apply] simp [*]
  [apply] simp only [p, f]
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example {P Q : Prop} (p : P) (f : P → Q) : Q := by try?

/--
info: Try these:
  [apply] simp [*]
  [apply] simp only [and_self, x]
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example {P Q R : Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by try?

/--
info: Try these:
  [apply] grind
  [apply] grind only
-/
#guard_msgs in
example {a b : ℚ} (h : a < b) : ¬ b < a := by try?

/--
info: Try these:
  [apply] rfl
  [apply] simp
  [apply] simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul]
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by try?

/--
info: Try this:
  [apply] exact of_decide_eq_true rfl
-/
#guard_msgs in
example : Nat.Prime 37 := by try?

/--
info: Try these:
  [apply] grind
  [apply] grind only [#734e]
  [apply] grind only
  [apply] grind => instantiate only [#734e]
-/
#guard_msgs in
example {P : Nat → Prop} (h : { x // P x }) : ∃ x, P x ∧ 0 ≤ x := by try?

def f (p : Nat × Nat) := (p.fst, p.snd)
/--
info: Try these:
  [apply] rfl
  [apply] grind [= f.eq_def]
  [apply] grind only [= f.eq_def, = id.eq_1, #be54]
  [apply] grind only [= f.eq_def, = id.eq_1]
  [apply] grind => cases #be54 <;> instantiate only [= f.eq_def, = id.eq_1]
-/
#guard_msgs in
example : f = id := by try?

section multiline_hint

local macro "this_is_a_multiline_exact" ppLine t:term : tactic => `(tactic| exact $t)

local elab tk:"long_trivial" : tactic => do
  let triv := Lean.mkIdent ``trivial
  let actual ← `(tactic| this_is_a_multiline_exact $triv)
  Lean.Meta.Tactic.TryThis.addSuggestion tk { suggestion := .tsyntax actual}
  Lean.Elab.Tactic.evalTactic actual

register_try?_tactic (priority := 1000) long_trivial

/--
info: Try these:
  [apply] solve_by_elim
  [apply] simp
  [apply] simp only
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example : True := by
  try?

end multiline_hint

section finiteness
/--
info: Try these:
  [apply] solve_by_elim
  [apply] simp
  [apply] simp only [one_lt_top]
  [apply] simp_all
-/
#guard_msgs in
open ENNReal in
example : (1 : ℝ≥0∞) < ∞ := by try?
end finiteness

section tauto_set

register_try?_tactic (priority := 1000) tauto_set

/--
info: Try these:
  [apply] grind
  [apply] grind only [= Set.subset_def, = Set.mem_union, = Set.mem_inter_iff, #8366, #0c26, #982d]
  [apply] grind only [= Set.subset_def, = Set.mem_union, = Set.mem_inter_iff]
  [apply] grind =>
    instantiate only [= Set.subset_def]
    cases #8366 <;>
      instantiate only [#0c26, = Set.mem_union] <;>
        instantiate only [= Set.mem_inter_iff, = Set.mem_union] <;> cases #982d
-/
#guard_msgs in
example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by try?

/--
info: Try this:
  [apply] tauto_set
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 1 := by try?

section compute_degree
/--
info: Try these:
  [apply] tauto_set
  [apply] compute_degree
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
open Polynomial in
example : natDegree ((X + 1) : Nat[X]) ≤ 1 := by try?
end compute_degree

section field_simp
#adaptation_note
/--
As of nightly-2025-08-27,
this test no longer reports `field_simp` amongst the successful tactics.
-/

/--
info: Try this:
  [apply] · expose_names; exact Units.divp_add_divp_same a b u₁
-/
#guard_msgs in
example (R : Type) (a b : R) [CommRing R] (u₁ : Rˣ) : a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁ := by try?
end field_simp

-- This test was originally here to ensure `finiteness` closed the goal,
-- but apparently `tauto_set` also works.
/--
info: Try these:
  [apply] solve_by_elim
  [apply] simp
  [apply] simp only [one_lt_top]
  [apply] simp_all
-/
#guard_msgs in
open ENNReal in
example : (1 : ℝ≥0∞) < ∞ := by try?
