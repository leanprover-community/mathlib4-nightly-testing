import Mathlib
-- 1: the failing case
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by lia

-- 2: split the subtype by hand first
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by
  obtain ⟨v, hv⟩ := r
  lia

-- 3: generalise `m r` to an opaque Fin first
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by
  generalize m r = z
  lia

-- 4: `grind` instead of `lia`
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by grind
