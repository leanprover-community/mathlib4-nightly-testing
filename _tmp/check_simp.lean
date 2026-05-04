import Mathlib.CategoryTheory.Monoidal.Types.Basic

open CategoryTheory MonoidalCategory

set_option trace.Meta.Tactic.simp.rewrite true in
example (W X Y Z : Type u) (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
    (ConcreteCategory.hom (f ⊗ₘ g)) p = ((ConcreteCategory.hom f) p.1, (ConcreteCategory.hom g) p.2) := by
  simp
