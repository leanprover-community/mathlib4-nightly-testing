import Mathlib
-- 1: subtype order on a Set complement, two spellings of Fin 2
example (i : Fin (0 + 2)) (a b : ↑({i}ᶜ : Set (Fin (0 + 1 + 1)))) (h : a < b) : False := by grind
-- 2: same spelling throughout
example (i : Fin 2) (a b : ↑({i}ᶜ : Set (Fin 2))) (h : a < b) : False := by grind
-- 3: order taken on the underlying values instead
example (i : Fin 2) (a b : ↑({i}ᶜ : Set (Fin 2))) (h : a.1 < b.1) : False := by grind
-- 4: plain Subtype rather than a Set coe-sort
example (i : Fin 2) (a b : {x : Fin 2 // x ≠ i}) (h : a < b) : False := by grind
