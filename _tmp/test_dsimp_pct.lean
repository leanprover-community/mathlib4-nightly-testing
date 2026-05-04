import Mathlib.CategoryTheory.Monoidal.Types.Basic
open CategoryTheory MonoidalCategory

example : (dsimp% ((↾fun _ : PUnit ↦ PUnit.unit) ▷ PUnit) (PUnit.unit, PUnit.unit)) =
    (PUnit.unit, PUnit.unit) := rfl

#print whiskerRight_apply
