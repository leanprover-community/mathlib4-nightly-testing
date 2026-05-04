import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

@[expose] public section

namespace CategoryTheory
open Opposite MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] types_tensorObj_def types_tensorUnit_def in
set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.unify true in
example (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    (coyoneda.obj (op (𝟙_ C))).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := ↾fun _ ↦ 𝟙 _)
    (μ := fun X Y ↦ ↾fun p ↦ (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ₘ p.2))
    (μ_natural := by cat_disch)
    (associativity := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩; dsimp at f g h
      dsimp
      sorry)
    (right_unitality := fun X => by ext ⟨f, ⟨⟩⟩; simp [unitors_inv_equal])

end CategoryTheory
