/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Equalizer

/-!
# Adjoint lifting

This file gives two constructions for building right adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.

The adjoint triangle theorem concerns a functor `F : B ⥤ A` with a right adjoint `U` such
that `η_X : X ⟶ UFX` is a regular mono. Then for any category `C` with equalizers of coreflexive
pairs, a functor `L : C ⥤ B` has a right adjoint if (and only if) the composite `L ⋙ F` does.
Note that the condition on `F` regarding `η_X` is automatically satisfied in the case when `F` is
a comonadic functor, giving the corollary: `isLeftAdjoint_triangle_lift_comonadic`, i.e. if `F` is
comonadic, `C` has coreflexive equalizers then `L : C ⥤ B` has a right adjoint provided `L ⋙ F`
does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      L
```

where `V` is comonadic, `U` has a right adjoint, and `A` has coreflexive equalizers, then if `L` has
a right adjoint then `Q` has a right adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : L ⋙ F ⊣ U'`.

This file has been adapted from `Mathlib/CategoryTheory/Adjunction/Lifting/Left.lean`.
Please try to keep them in sync.

## TODO

- Dualise to lift left adjoints through comonads (by reversing 2-cells).
- Investigate whether it is possible to give a more explicit description of the lifted adjoint,
  especially in the case when the isomorphism `comm` is `Iso.refl _`

## References
* https://ncatlab.org/nlab/show/adjoint+triangle+theorem
* https://ncatlab.org/nlab/show/adjoint+lifting+theorem
* Adjoint Lifting Theorems for Categories of Algebras (PT Johnstone, 1975)
* A unified approach to the lifting of adjoints (AJ Power, 1988)
-/

@[expose] public section


namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

-- Hide implementation details in this namespace
namespace LiftRightAdjoint

variable {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (U' : A ⥤ C)
variable (adj₁ : F ⊣ U) (adj₂ : L ⋙ F ⊣ U')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- To show that `η_X` is an equalizer for `(UFη_X, η_UFX)`, it suffices to assume it's always an
equalizer of something (i.e. a regular mono).
-/
def unitEqualises (h : ∀ X : B, RegularMono (adj₁.unit.app X)) (X : B) :
    IsLimit (Fork.ofι (adj₁.unit.app X) (adj₁.unit_naturality _)) :=
  Fork.IsLimit.mk' _ fun s => by
    have := fun Y ↦ h Y |>.mono
    refine ⟨((h X).lift' s.ι ?_).1, ?_, ?_⟩
    · rw [← cancel_mono (adj₁.unit.app ((h X).Z)), assoc, ← adj₁.unit_naturality (h _).left]
      dsimp only [Functor.comp_obj]
      have := s.condition
      dsimp only [Functor.comp_obj] at this
      rw [← assoc, ← this, assoc, ← U.map_comp, ← F.map_comp, RegularMono.w, F.map_comp,
        U.map_comp, s.condition_assoc, assoc, ← adj₁.unit_naturality (h _).right]
    · apply ((h X).lift' s.ι _).2
    · intro m hm
      rw [← cancel_mono (adj₁.unit.app X)]
      apply hm.trans ((h X).lift' s.ι _).2.symm

/-- (Implementation)
To construct the right adjoint, we use the equalizer of `U' F η_X` with the composite

`U' F X ⟶ U' F L U' F X ⟶ U' F U F L U' F X ⟶ U' F U F X`

where the first morphism is `ι_U'FX`, the second is `U' F η_LU'FX` and the third is `U' F U δ_FX`.
We will show that this equalizer exists and that it forms the object map for a right adjoint to `L`.
-/
def otherMap (X : B) : U'.obj (F.obj X) ⟶ U'.obj (F.obj (U.obj (F.obj X))) :=
  adj₂.unit.app _ ≫ U'.map (F.map (adj₁.unit.app _ ≫ (U.map (adj₂.counit.app _))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `(U'Fη_X, otherMap X)` is a coreflexive pair: in particular if `C` has coreflexive equalizers
then this pair has an equalizer.
-/
instance (X : B) :
    IsCoreflexivePair (U'.map (F.map (adj₁.unit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsCoreflexivePair.mk' (U'.map (adj₁.counit.app (F.obj X)))
    (by simp [← Functor.map_comp])
    (by simp only [otherMap, assoc, ← Functor.map_comp]; simp)

variable [HasCoreflexiveEqualizers C]

/-- Construct the object part of the desired right adjoint as the equalizer of `U'Fη_Y` with
`otherMap`.
-/
noncomputable def constructRightAdjointObj (Y : B) : C :=
  equalizer (U'.map (F.map (adj₁.unit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homset equivalence which helps show that `L` is a left adjoint. -/
@[simps!]
noncomputable def constructRightAdjointEquiv (h : ∀ X : B, RegularMono (adj₁.unit.app X)) (Y : C)
    (X : B) : (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃ (L.obj Y ⟶ X) :=
  calc
    (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃
        { f : Y ⟶ U'.obj (F.obj X) //
          f ≫ U'.map (F.map (adj₁.unit.app X)) = f ≫ (otherMap _ _ adj₁ adj₂ X) } :=
      Fork.IsLimit.homIso (limit.isLimit _) _
    _ ≃ { g : F.obj (L.obj Y) ⟶ F.obj X // F.map (adj₁.unit.app _≫ U.map g) =
        g ≫ F.map (adj₁.unit.app _) } := by
      apply (adj₂.homEquiv _ _).symm.subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff, eq_comm, otherMap,
        ← adj₂.homEquiv_naturality_right_symm, adj₂.homEquiv_unit, ← adj₂.unit_naturality_assoc,
        adj₂.homEquiv_counit]
      simp
    _ ≃ { z : L.obj Y ⟶ U.obj (F.obj X) //
        z ≫ U.map (F.map (adj₁.unit.app X)) = z ≫ adj₁.unit.app (U.obj (F.obj X)) } := by
      apply (adj₁.homEquiv _ _).subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).injective.eq_iff, adj₁.homEquiv_unit,
        adj₁.homEquiv_unit, adj₁.homEquiv_unit, eq_comm]
      simp
    _ ≃ (L.obj Y ⟶ X) := (Fork.IsLimit.homIso (unitEqualises adj₁ h X) _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construct the right adjoint to `L`, with object map `constructRightAdjointObj`. -/
noncomputable def constructRightAdjoint (h : ∀ X : B, RegularMono (adj₁.unit.app X)) : B ⥤ C := by
  refine Adjunction.rightAdjointOfEquiv
    (fun X Y => (constructRightAdjointEquiv L _ adj₁ adj₂ h X Y).symm) ?_
  intro X Y Y' g h
  rw [constructRightAdjointEquiv_symm_apply, constructRightAdjointEquiv_symm_apply,
    Equiv.symm_apply_eq, Subtype.ext_iff]
  dsimp
  simp only [Adjunction.homEquiv_counit]
  erw [Fork.IsLimit.homIso_natural, Fork.IsLimit.homIso_natural]
  simp only [Fork.ofι_pt, Functor.map_comp, assoc, limit.cone_x]
  erw [adj₂.homEquiv_naturality_left, Equiv.rightInverse_symm]
  simp

end LiftRightAdjoint

/-- The adjoint triangle theorem: Suppose `U : A ⥤ B` has a left adjoint `F` such that each unit
`η_X : X ⟶ UFX` is a regular monomorphism. Then if a category `C` has equalizers of coreflexive
pairs, then a functor `L : C ⥤ B` has a right adjoint if the composite `L ⋙ F` does.

Note the converse is true (with weaker assumptions), by `Adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
lemma isLeftAdjoint_triangle_lift {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (adj₁ : F ⊣ U)
    (h : ∀ X, RegularMono (adj₁.unit.app X)) [HasCoreflexiveEqualizers C]
    [(L ⋙ F).IsLeftAdjoint] : L.IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨LiftRightAdjoint.constructRightAdjoint L _ adj₁ (Adjunction.ofIsLeftAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

/-- If `L ⋙ F` has a right adjoint, the domain of `L` has coreflexive equalizers and `F` is a
comonadic functor, then `L` has a right adjoint.
This is a special case of `isLeftAdjoint_triangle_lift` which is often more useful in practice.
-/
lemma isLeftAdjoint_triangle_lift_comonadic (F : B ⥤ A) [ComonadicLeftAdjoint F] {L : C ⥤ B}
    [HasCoreflexiveEqualizers C] [(L ⋙ F).IsLeftAdjoint] : L.IsLeftAdjoint := by
  let L' : _ ⥤ _ := L ⋙ Comonad.comparison (comonadicAdjunction F)
  rsuffices : L'.IsLeftAdjoint
  · let this : (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv).IsLeftAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsLeftAdjoint
      (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparison _).asEquivalence.unitIso.symm ≪≫ L.leftUnitor
  let this : (L' ⋙ Comonad.forget (comonadicAdjunction F).toComonad).IsLeftAdjoint := by
    refine ((Adjunction.ofIsLeftAdjoint (L ⋙ F)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparisonForget (comonadicAdjunction F)).symm
  let this : ∀ X, RegularMono ((Comonad.adj (comonadicAdjunction F).toComonad).unit.app X) := by
    intro X
    simp only [Comonad.adj_unit]
    exact ⟨_, _, _, _, Comonad.beckCoalgebraEqualizer X⟩
  exact isLeftAdjoint_triangle_lift L' (Comonad.adj _) this

variable {D : Type u₄}
variable [Category.{v₄} D]

/-- Suppose we have a commutative square of functors

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      L
```

where `U` has a right adjoint, `A` has coreflexive equalizers and `V` has a right adjoint such that
each component of the counit is a regular mono.
Then `Q` has a right adjoint if `L` has a right adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
lemma isLeftAdjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
    (comm : U ⋙ L ≅ Q ⋙ V) [U.IsLeftAdjoint] [V.IsLeftAdjoint] [L.IsLeftAdjoint]
    (h : ∀ X, RegularMono ((Adjunction.ofIsLeftAdjoint V).unit.app X))
    [HasCoreflexiveEqualizers A] : Q.IsLeftAdjoint :=
  have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift Q (Adjunction.ofIsLeftAdjoint V) h

/-- Suppose we have a commutative square of functors

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      L
```

where `U` has a right adjoint, `A` has reflexive equalizers and `V` is comonadic.
Then `Q` has a right adjoint if `L` has a right adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
lemma isLeftAdjoint_square_lift_comonadic (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
    (comm : U ⋙ L ≅ Q ⋙ V) [U.IsLeftAdjoint] [ComonadicLeftAdjoint V] [L.IsLeftAdjoint]
    [HasCoreflexiveEqualizers A] : Q.IsLeftAdjoint :=
  have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift_comonadic V

end CategoryTheory
