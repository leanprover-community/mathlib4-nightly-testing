import Mathlib
-- fails on 14473
example (i : Fin 2) (a b : {x : Fin 2 // x ≠ i}) (h : a < b) : False := by grind
-- same, with the Fin equation supplied first
example (i : Fin 2) (a b : {x : Fin 2 // x ≠ i}) (h : a < b) : False := by
  have : (a : Fin 2) = (b : Fin 2) := by grind
  grind
