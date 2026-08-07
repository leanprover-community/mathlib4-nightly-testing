import Mathlib
set_option pp.explicit true in
set_option pp.proofs true in
set_option trace.grind.assert true in
example {N : ℕ} (a : Fin (N + 2)) (m : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a ⟨N, by lia⟩ : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by lia
