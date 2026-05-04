import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

@[expose] public section

namespace CategoryTheory
open Opposite MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] types_tensorObj_def types_tensorUnit_def in
example (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    (coyoneda.obj (op (𝟙_ C))).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := ↾fun _ ↦ 𝟙 _)
    (μ := fun X Y ↦ ↾fun p ↦ (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ₘ p.2))
    (μ_natural := by cat_disch)
    (associativity := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩
      simp only [hom_tensor_apply, hom_whiskerLeft_apply, hom_whiskerRight_apply, comp_apply,
        TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply, id_apply]
      conv_lhs =>
        rw [← Category.id_comp h, ← tensorHom_comp_tensorHom, Category.assoc, associator_naturality,
          ← Category.assoc, unitors_inv_equal, tensorHom_id, triangle_assoc_comp_right_inv]
      conv_rhs => rw [← Category.id_comp f, ← tensorHom_comp_tensorHom]
      simp)
    (right_unitality := fun X => by ext ⟨f, ⟨⟩⟩; simp [unitors_inv_equal])

end CategoryTheory
