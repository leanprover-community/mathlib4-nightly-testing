import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Tactic.CategoryTheory.CastProofs
import Mathlib.Tactic.Semireducible

namespace CastProofsPercentTest

open CategoryTheory CategoryTheory.Functor MonoidalCategory
open CategoryTheory.Localization

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

section
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (F : C ⥤ D) (G : D ⥤ E)

def identityExample : F ⋙ 𝟭 D ≅ F := by
  with_reducible_and_instances exact cast_proofs% (Iso.refl _)

example (X : C) : (identityExample F).hom.app X = 𝟙 (F.obj X) := by
  simp [identityExample]

example (X : C) : (cast_proofs% (Iso.refl _) : 𝟭 C ⋙ F ≅ F).inv.app X = 𝟙 (F.obj X) := by
  dsimp

example : F ⋙ 𝟭 D ≅ F := cast_proofs% (Iso.refl F)

def transformationExample : 𝟭 C ⋙ F ⟶ F := by
  with_reducible_and_instances exact cast_proofs% (𝟙 F)

example (X : C) : (transformationExample F).app X = 𝟙 (F.obj X) := by
  simp [transformationExample]

example (H : D ⥤ E) : (𝟭 C ⋙ F) ⋙ H ≅ F ⋙ H := by
  with_reducible_and_instances exact cast_proofs% (Iso.refl _)

-- Keep categorical identities intact when the component morphisms are structures.
def doubleOppositeExample : 𝟭 (Cᵒᵖᵒᵖ) ≅ unopUnop C ⋙ opOp C := cast_proofs% (Iso.refl _)

example (X : Cᵒᵖᵒᵖ) : (doubleOppositeExample (C := C)).hom.app X = 𝟙 X := by
  simp [doubleOppositeExample]

-- The wrapper does not invent a map equality for arbitrary functors.
example (_F' : C ⥤ D) : True := by
  fail_if_success have : F ≅ _F' := cast_proofs% (Iso.refl F)
  trivial

-- Model the intended transparency of Functor.unop, including its hidden map field.
@[implicit_reducible]
def unopWithHiddenMap (H : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj X := (H.obj (Opposite.op X)).unop
  map f := semireducible% (H.map f.op).unop

def opUnopHiddenExample : unopWithHiddenMap F.op ≅ F := by
  fail_if_success with_implicit exact Iso.refl F
  with_reducible_and_instances exact cast_proofs% (Iso.refl F)

def unopOpHiddenExample (H : Cᵒᵖ ⥤ Dᵒᵖ) : (unopWithHiddenMap H).op ≅ H := by
  fail_if_success with_implicit exact Iso.refl H
  with_reducible_and_instances exact cast_proofs% (Iso.refl H)

example (X : C) : (opUnopHiddenExample F).hom.app X = 𝟙 (F.obj X) := by
  simp [opUnopHiddenExample]

example (H : Cᵒᵖ ⥤ Dᵒᵖ) (X : Cᵒᵖ) :
    (unopOpHiddenExample H).hom.app X = 𝟙 (H.obj X) := by
  simp [unopOpHiddenExample]
end

section
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Monoidal]
  (F : D ⥤ E) (G : C ⥤ E) [G.Monoidal] [W.ContainsIdentities] [Lifting L W G F]

@[simps! hom_app_app inv_app_app]
def localizationExample :
    (((whiskeringLeft₂ E).obj L).obj L).obj (curriedTensorPost F) ≅ curriedTensorPost G :=
  cast_proofs% ((postcompose₂.obj F).mapIso (Functor.curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F))

example (X Y : C) :
    ((localizationExample L W F G).hom.app X).app Y =
      F.map (Functor.LaxMonoidal.μ L X Y) ≫ (Lifting.iso L W G F).hom.app (X ⊗ Y) := by
  simp only [localizationExample_hom_app_app]

example : localizationExample L W F G =
    ((postcompose₂.obj F).mapIso (Functor.curriedTensorPreIsoPost L) ≪≫
      curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)) := by
  rfl

-- The original expression can also be provided through a named definition.
@[simps! hom_app_app inv_app_app]
def namedSource :
    (((whiskeringLeft₂ E).obj L).obj L).obj (curriedTensorPost F) ≅ curriedTensorPost G :=
  (postcompose₂.obj F).mapIso (Functor.curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

def wrappedSource :
    (((whiskeringLeft₂ E).obj L).obj L).obj (curriedTensorPost F) ≅ curriedTensorPost G :=
  cast_proofs% (namedSource L W F G)

example (X Y : C) :
    ((wrappedSource L W F G).hom.app X).app Y =
      F.map (Functor.LaxMonoidal.μ L X Y) ≫ (Lifting.iso L W G F).hom.app (X ⊗ Y) := by
  simp [wrappedSource]

-- A source whose type already matches is kept without unfolding or rebuilding it.
open Lean Meta Elab in
run_elab do
  let info ← getConstInfoDefn ``wrappedSource
  lambdaTelescope info.value fun _ body => do
    unless body.isAppOf ``namedSource do
      throwError "cast_proofs% rebuilt an already well-typed source"
end

end CastProofsPercentTest
