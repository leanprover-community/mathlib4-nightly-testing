/-
import Mathlib.Tactic.CategoryTheory.Slice

open CategoryTheory

variable (C : Type) [Category C] (X Y Z W U : C)
variable (f₁ f₂ : X ⟶ Y) (g g₁ g₂ : Y ⟶ Z) (h : Z ⟶ W) (l : W ⟶ U)

set_option linter.unusedTactic false in
example (hyp : f₁ ≫ g₁ = f₂ ≫ g₂) : f₁ ≫ g₁ ≫ h ≫ l = (f₂ ≫ g₂) ≫ (h ≫ l) := by
  conv =>
    rhs
    slice 2 3
  show f₁ ≫ g₁ ≫ h ≫ l = f₂ ≫ (g₂ ≫ h) ≫ l
  conv =>
    lhs
    slice 1 2
    rw [hyp]
  show ((f₂ ≫ g₂) ≫ h) ≫ l = f₂ ≫ (g₂ ≫ h) ≫ l
  conv =>
    lhs
    slice 2 3

example (hyp : f₁ ≫ g₁ = f₂ ≫ g₂) : f₁ ≫ g₁ ≫ h ≫ l = (f₂ ≫ g₂) ≫ (h ≫ l) := by
  slice_lhs 1 2 => { rw [hyp] }; slice_rhs 1 2 => skip

example (h₁ : f₁ = f₂) : f₁ ≫ g ≫ h ≫ l = ((f₂ ≫ g) ≫ h) ≫ l := by
  slice_lhs 1 1 => rw [h₁]

example (h₁ : f₁ = f₂) : ((f₂ ≫ g) ≫ h) ≫ l = f₁ ≫ g ≫ h ≫ l := by
  slice_rhs 1 1 => rw [h₁]

-/
