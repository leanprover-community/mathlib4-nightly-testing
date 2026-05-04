import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.Tactic.DSimpPercent

namespace CategoryTheory.MonoidalCategory

example {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
    (ConcreteCategory.hom (f ⊗ₘ g)) p = (f p.1, g p.2) := by
  rfl

end CategoryTheory.MonoidalCategory
