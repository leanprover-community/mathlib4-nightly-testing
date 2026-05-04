/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monad.Adjunction
/-!

# Adjoint triples

This file concerns adjoint triples `F ⊣ G ⊣ H` of functors `F H : C ⥤ D`, `G : D ⥤ C`. We first
prove that `F` is fully faithful iff `H` is, and then prove results about the two special cases
where `G` is fully faithful or `F` and `H` are.

## Main results

All results are about an adjoint triple `F ⊣ G ⊣ H` where `adj₁ : F ⊣ G` and `adj₂ : G ⊣ H`. We
bundle the adjunctions in a structure `Triple F G H`.
* `fullyFaithfulEquiv`: `F` is fully faithful iff `H` is.
* `rightToLeft`: the canonical natural transformation `H ⟶ F` that exists whenever `G` is fully
  faithful. This is defined as the preimage of `adj₂.counit ≫ adj₁.unit` under whiskering with `G`,
  but formulas in terms of the units resp. counits of the adjunctions are also given.
* `whiskerRight_rightToLeft`: whiskering `rightToLeft : H ⟶ F` with `G` yields
  `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G`.
* `epi_rightToLeft_app_iff_epi_map_adj₁_unit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₁.unit.app X` under `H` is.
* `epi_rightToLeft_app_iff_epi_map_adj₂_counit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₂.counit.app X` under `F` is.
* `epi_rightToLeft_app_iff`: when `H` preserves epimorphisms, `rightToLeft : H ⟶ F` is epic at `X`
  iff `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G` is.
* `leftToRight`: the canonical natural transformation `F ⟶ H` that exists whenever `F` and `H` are
  fully faithful. This is defined in terms of the units of the adjunctions, but a formula in terms
  of the counits is also given.
* `whiskerLeft_leftToRight`: whiskering `G` with `leftToRight : F ⟶ H` yields
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H`.
* `mono_leftToRight_app_iff_mono_adj₂_unit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₂.unit` is monic at `F.obj X`.
* `mono_leftToRight_app_iff_mono_adj₁_counit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₁.counit` is monic at `H.obj X`.
* `mono_leftToRight_app_iff`: `leftToRight : F ⟶ H` is componentwise monic iff
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H` is.
-/

@[expose] public section

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]
variable (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ D)

/-- Structure containing the two adjunctions of an adjoint triple `F ⊣ G ⊣ H`. -/
structure CategoryTheory.Adjunction.Triple where
  /-- Adjunction `F ⊣ G` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₁ : F ⊣ G
  /-- Adjunction `G ⊣ H` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₂ : G ⊣ H

namespace CategoryTheory.Adjunction.Triple

variable {F G H} (t : Triple F G H)

lemma isIso_unit_iff_isIso_counit : IsIso t.adj₁.unit ↔ IsIso t.adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := t.adj₁.comp t.adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso t.adj₁.unit).symm
    exact t.adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso t.adj₂.counit)
    exact t.adj₁.isIso_unit_of_iso (adjId.leftAdjointUniq id)

/--
Given an adjoint triple `F ⊣ G ⊣ H`, the left adjoint `F` is fully faithful if and only if the
right adjoint `H` is fully faithful.
-/
noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The adjoint triple `H.op ⊣ G.op ⊣ F.op` dual to an adjoint triple `F ⊣ G ⊣ H`. -/
@[simps]
protected def op : Triple H.op G.op F.op where
  adj₁ := t.adj₂.op
  adj₂ := t.adj₁.op

section InnerFullyFaithful

variable [G.Full] [G.Faithful]

/-- The natural transformation `H ⟶ F` that exists for every adjoint triple `F ⊣ G ⊣ H` where `G`
is fully faithful, given here as the preimage of `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G`
under whiskering with `G`. -/
noncomputable def rightToLeft : H ⟶ F :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimage (t.adj₂.counit ≫ t.adj₁.unit)

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, whiskering the natural
transformation `H ⟶ F` with `G` yields the composition of the counit of the second adjunction with
the unit of the first adjunction. -/
@[simp, reassoc]
lemma whiskerRight_rightToLeft : whiskerRight t.rightToLeft G = t.adj₂.counit ≫ t.adj₁.unit :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).map_preimage _

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the images of the components of
the natural transformation `H ⟶ F` under `G` are the components of the composition of counit of the
second adjunction with the unit of the first adjunction. -/
@[simp, reassoc]
lemma map_rightToLeft_app (X : C) :
    G.map (t.rightToLeft.app X) = t.adj₂.counit.app X ≫ t.adj₁.unit.app X :=
  congr_app t.whiskerRight_rightToLeft X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fully faithful
is also equal to the whiskered unit `H ⟶ F ⋙ G ⋙ H` of the first adjunction followed by the
inverse of the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second. -/
lemma rightToLeft_eq_units :
    t.rightToLeft = H.leftUnitor.inv ≫ whiskerRight t.adj₁.unit H ≫ (Functor.associator _ _ _).hom ≫
    inv (whiskerLeft F t.adj₂.unit) ≫ F.rightUnitor.hom := by
  ext X; apply G.map_injective; simp [rightToLeft]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fully faithful
is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first adjunction
followed by the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second. -/
lemma rightToLeft_eq_counits :
    t.rightToLeft = H.rightUnitor.inv ≫ inv (whiskerLeft H t.adj₁.counit) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight t.adj₂.counit F ≫ F.leftUnitor.hom := by
  ext X; apply G.map_injective; simp [rightToLeft]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma adj₁_counit_app_rightToLeft_app (X : C) :
    t.adj₁.counit.app (H.obj X) ≫ t.rightToLeft.app X = F.map (t.adj₂.counit.app X) :=
  G.map_injective (by simp [← cancel_epi (t.adj₁.unit.app _)])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma rightToLeft_app_adj₂_unit_app (X : C) :
    t.rightToLeft.app X ≫ t.adj₂.unit.app (F.obj X) = H.map (t.adj₁.unit.app X) :=
  G.map_injective (by simp [← cancel_mono (t.adj₂.counit.app _)])

set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`F.op ⟶ H.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op` is dual to the natural
transformation `H ⟶ F`. -/
@[simp]
lemma op_rightToLeft : t.op.rightToLeft = NatTrans.op t.rightToLeft := by
  ext
  rw [rightToLeft_eq_units, rightToLeft_eq_counits]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⟶ F` is epic at `X` iff the image of the unit of the adjunction `F ⊣ G` under `H` is. -/
lemma epi_rightToLeft_app_iff_epi_map_adj₁_unit_app {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (H.map (t.adj₁.unit.app X)) := by
  rw [← epi_comp_iff_of_isIso _ (t.adj₂.unit.app (F.obj X)), rightToLeft_app_adj₂_unit_app]

set_option backward.isDefEq.respectTransparency false in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⟶ F` is epic at `X` iff the image of the counit of the adjunction `G ⊣ H` under `F` is. -/
lemma epi_rightToLeft_app_iff_epi_map_adj₂_counit_app {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (F.map (t.adj₂.counit.app X)) := by
  rw [← epi_comp_iff_of_epi (t.adj₁.counit.app (H.obj X)), adj₁_counit_app_rightToLeft_app]

set_option backward.isDefEq.respectTransparency false in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful and `H` preserves epimorphisms
(which is for example the case if `H` has a further right adjoint), the components of the natural
transformation `H ⟶ F` are epic iff the respective components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are. -/
lemma epi_rightToLeft_app_iff [H.PreservesEpimorphisms] {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) := by
  have _ := t.adj₂.isLeftAdjoint
  refine ⟨fun h ↦ by rw [← map_rightToLeft_app]; exact G.map_epi _, fun h ↦ ?_⟩
  rw [epi_rightToLeft_app_iff_epi_map_adj₁_unit_app]
  simpa using epi_comp (t.adj₂.unit.app (H.obj X)) (H.map (t.adj₂.counit.app X ≫ t.adj₁.unit.app X))

end InnerFullyFaithful

section OuterFullyFaithful

variable [F.Full] [F.Faithful] [H.Full] [H.Faithful]

/-- The natural transformation `F ⟶ H` that exists for every adjoint triple `F ⊣ G ⊣ H` where `F`
and `H` are fully faithful, given here as the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second
adjunction followed by the inverse of the whiskered unit `F ⋙ G ⋙ H ⟶ H` of the first. -/
noncomputable def leftToRight : F ⟶ H :=
  F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight t.adj₁.unit H) ≫ H.leftUnitor.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [H.Full] [H.Faithful] in
lemma leftToRight_app {X : C} :
    t.leftToRight.app X = t.adj₂.unit.app (F.obj X) ≫ inv (H.map (t.adj₁.unit.app X)) := by
  simp [leftToRight]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `F ⟶ H` for an adjoint triple `F ⊣ G ⊣ H` with `F` and `H`
fully faithful is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second
adjunction followed by the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first. -/
lemma leftToRight_eq_counits :
    t.leftToRight = F.leftUnitor.inv ≫ inv (whiskerRight t.adj₂.counit F) ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft H t.adj₁.counit ≫ H.rightUnitor.hom := by
  ext X; dsimp [leftToRight]; simp only [Category.id_comp, Category.comp_id, NatIso.isIso_inv_app]
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  refine Eq.trans ?_ (t.adj₁.counit_naturality <| (whiskerRight t.adj₁.unit H).app X)
  rw [whiskerRight_app _ H, (asIso (t.adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (t.adj₂.counit_naturality (t.adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| t.adj₂.left_triangle_components (F.obj X)]
  simp

set_option backward.isDefEq.respectTransparency false in
omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `F ⟶ H` at `G` are precisely the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions. -/
@[simp, reassoc]
lemma leftToRight_app_obj {X : D} :
    dsimp% t.leftToRight.app (G.obj X) = t.adj₁.counit.app X ≫ t.adj₂.unit.app X := by
  refine (((t.adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_).symm
  rw [homEquiv_symm_apply, map_comp, Category.assoc, left_triangle_components,
    homEquiv_apply, leftToRight_app, ← H.map_inv]
  congr
  simpa using IsIso.eq_inv_of_hom_inv_id (t.adj₁.right_triangle_components _)

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, whiskering `G` with the
natural transformation `F ⟶ H` yields the composition of the counit of the first adjunction with
the unit of the second adjunction. -/
@[simp, reassoc]
lemma whiskerLeft_leftToRight : whiskerLeft G t.leftToRight = t.adj₁.counit ≫ t.adj₂.unit := by
  ext X; exact t.leftToRight_app_obj

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
lemma map_adj₂_counit_app_leftToRight_app (X : C) :
    F.map (t.adj₂.counit.app X) ≫ t.leftToRight.app X = t.adj₁.counit.app (H.obj X) := by
  simp

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
@[reassoc (attr := simp)]
lemma leftToRight_app_map_adj₁_unit_app (X : C) :
    t.leftToRight.app X ≫ H.map (t.adj₁.unit.app X) = t.adj₂.unit.app (F.obj X) := by
  simp [leftToRight_app]

set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `H.op ⟶ F.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op` is
dual to the natural transformation `F ⟶ H`. -/
@[simp]
lemma leftToRight_op : t.op.leftToRight = NatTrans.op t.leftToRight := by
  ext
  rw [leftToRight, leftToRight_eq_counits]
  simp

set_option backward.isDefEq.respectTransparency false in
omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is monic at `X` iff the unit of the adjunction `G ⊣ H` is monic
at `F.obj X`. -/
lemma mono_leftToRight_app_iff_mono_adj₂_unit_app {X : C} :
    Mono (t.leftToRight.app X) ↔ Mono (t.adj₂.unit.app (F.obj X)) := by
  rw [← leftToRight_app_map_adj₁_unit_app, mono_comp_iff_of_mono]

set_option backward.isDefEq.respectTransparency false in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is monic at `X` iff the counit of the adjunction `F ⊣ G` is monic
at `H.obj X`. -/
lemma mono_leftToRight_app_iff_mono_adj₁_counit_app {X : C} :
    Mono (t.leftToRight.app X) ↔ Mono (t.adj₁.counit.app (H.obj X)) := by
  rw [← map_adj₂_counit_app_leftToRight_app, mono_comp_iff_of_isIso]

set_option backward.isDefEq.respectTransparency false in
omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is componentwise monic iff the natural transformation `G ⋙ F ⟶ G ⋙ H`
obtained from the units and counits of the adjunctions is.
Note that unlike `epi_rightToLeft_app_iff`, this equivalence does not make sense
on a per-object basis because the components of the two natural transformations are indexed by
different categories. -/
lemma mono_leftToRight_app_iff :
    dsimp% (∀ X, Mono (t.leftToRight.app X)) ↔
      ∀ X, Mono (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) := by
  refine ⟨fun h X ↦ by rw [← leftToRight_app_obj]; exact h _, fun h X ↦ ?_⟩
  rw [mono_leftToRight_app_iff_mono_adj₂_unit_app]
  simpa using h (F.obj X)

end OuterFullyFaithful

end CategoryTheory.Adjunction.Triple
