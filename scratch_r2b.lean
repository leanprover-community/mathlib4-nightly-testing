import Mathlib
set_option trace.grind.assert true in
example {N : ℕ} (a b : Fin (N + 2)) (m : (Set.Icc a b : Set (Fin (N + 2))) ↪ Fin (N + 1))
    (r : (Set.Icc a b : Set (Fin (N + 2)))) : (m r : ℕ) < N + 1 := by lia
