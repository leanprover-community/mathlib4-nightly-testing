import Mathlib.CategoryTheory.Monoidal.Types.Basic

namespace CategoryTheory
open MonoidalCategory

example (W X Y Z : Type u) (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
    (ConcreteCategory.hom (f ⊗ₘ g)) p = ((ConcreteCategory.hom f) p.1, (ConcreteCategory.hom g) p.2) := by
  simp only [hom_tensor_apply]

end CategoryTheory
