/-
Second, independent regression in leanprover/lean4#14473.
Needs Mathlib (`Set.Icc`, `Function.Embedding`); I could not take it to core.

`lia` loses the `Fin (N + 1)` range fact for a value produced by a bundled
`Embedding` whose domain is the coe-sort of a `Set.Icc` with a `Fin.mk` bound.
All three ingredients are required.
-/
import Mathlib

-- ✅ nightly-2026-08-06   ❌ pr-release-14473-e72cf05
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by lia

-- bounds as variables: ✅ both
example {N : ℕ} (a b : Fin (N + 2)) (m : (Set.Icc a b : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a b : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by lia

-- plain function instead of an embedding: ✅ both
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) → Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by lia

-- bare Subtype with the same Fin.mk bound: ✅ both
example {N : ℕ} (a : Fin (N + 2))
    (m : Subtype (fun y : Fin (N + 2) ↦ a ≤ y ∧ y ≤ ⟨N, by lia⟩) ↪ Fin (N + 1))
    (r : Subtype (fun y : Fin (N + 2) ↦ a ≤ y ∧ y ≤ ⟨N, by lia⟩)) : (m r : ℕ) < N + 1 := by lia
