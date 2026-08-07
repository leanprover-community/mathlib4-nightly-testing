import Mathlib
-- A: minimal failing form
example (i : Fin 2) (a b : {x : Fin 2 // x ≠ i}) (h : a < b) : False := by grind
-- B: is subtype-equality lifting from val-equality the issue?
example (p : Fin 2 → Prop) (a b : Subtype p) (h : (a : Fin 2) = (b : Fin 2)) : a = b := by grind
-- C: ... and used to contradict a subtype `<`
example (p : Fin 2 → Prop) (a b : Subtype p) (h : (a : Fin 2) = (b : Fin 2)) (h2 : a < b) :
    False := by grind
-- D: subtype `<` unfolded to val `<`
example (p : Fin 2 → Prop) (a b : Subtype p) (h : a < b) : (a : Fin 2) < (b : Fin 2) := by grind
