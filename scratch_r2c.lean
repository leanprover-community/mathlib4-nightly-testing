import Mathlib
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by lia
