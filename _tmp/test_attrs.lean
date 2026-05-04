import Mathlib.CategoryTheory.Monoidal.Types.Basic

open CategoryTheory MonoidalCategory

example (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (X Y : C) (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ Y) (h : 𝟙_ C ⟶ X) :
    ((ConcreteCategory.hom ((↾fun p : (𝟙_ C ⟶ X) ⊗ (𝟙_ C ⟶ Y) ↦ (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ₘ p.2))
        ⊗ₘ 𝟙 (𝟙_ C ⟶ X))) ((f, g), h)).1 = (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) := by
  simp
