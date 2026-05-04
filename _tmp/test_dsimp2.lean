import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.Tactic.DSimpPercent

namespace CategoryTheory.MonoidalCategory

private theorem hom_tensor_apply_aux {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
    (ConcreteCategory.hom (f ⊗ₘ g)) p = (f p.1, g p.2) := rfl

example (X Y Z : Type u) (f : X) (g : Y) (h : Z) :
    ((ConcreteCategory.hom ((↾fun p : X × Y ↦ p.1) ⊗ₘ 𝟙 Z)) ((f, g), h)).1 = f := by
  simp only [hom_tensor_apply_aux]

end CategoryTheory.MonoidalCategory
