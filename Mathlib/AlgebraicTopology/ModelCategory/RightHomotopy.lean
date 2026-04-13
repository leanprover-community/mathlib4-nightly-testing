/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.CategoryTheory.Localization.Quotient

/-!
# Right homotopies in model categories

We introduce the types `PrepathObject.RightHomotopy` and `PathObject.RightHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)path object of `Y`.
Given two morphisms `f` and `g`, we introduce the relation `RightHomotopyRel f g`
asserting the existence of a path object `P` and
a right homotopy `P.RightHomotopy f g`, and we define the quotient
type `RightHomotopyClass X Y`. We show that if `Y` is a fibrant
object in a model category, then `RightHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

(This file dualizes the definitions in `Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean`.)

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace PrepathObject

variable {Y : C} (P : PrepathObject Y) {X : C}

/-- Given a pre-path object `P` for `Y`, two maps `f` and `g` in `X ⟶ Y` are
homotopic relative to `P` when there is a morphism `h : X ⟶ P.P`
such that `h ≫ P.p₀ = f` and `h ≫ P.p₁ = g`. -/
structure RightHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the source to the pre-path object -/
  h : X ⟶ P.P
  h₀ : h ≫ P.p₀ = f := by cat_disch
  h₁ : h ≫ P.p₁ = g := by cat_disch

namespace RightHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

/-- `f : X ⟶ Y` is right homotopic to itself relative to any pre-path object. -/
@[simps]
def refl (f : X ⟶ Y) : P.RightHomotopy f f where
  h := f ≫ P.ι

variable {P}

/-- If `f` and `g` are homotopic relative to a pre-path object `P`, then `g` and `f`
are homotopic relative to `P.symm` -/
@[simps]
def symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f where
  h := h.h

set_option backward.isDefEq.respectTransparency false in
/-- If `f₀` is homotopic to `f₁` relative to a pre-path object `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`. -/
@[simps]
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.RightHomotopy f₀ f₁) {P' : PrepathObject Y}
    (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] :
    (P.trans P').RightHomotopy f₀ f₂ where
  h := pullback.lift h.h h'.h (by simp)

/-- Right homotopies are compatible with precomposition. -/
@[simps]
def precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) :
    P.RightHomotopy (i ≫ f) (i ≫ g) where
  h := i ≫ h.h

end RightHomotopy

end PrepathObject

namespace PathObject

variable {X Y : C}

/-- Given a path object `P` for `X`, two maps `f` and `g` in `X ⟶ Y`
are homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`. -/
abbrev RightHomotopy [CategoryWithWeakEquivalences C] (P : PathObject Y) (f g : X ⟶ Y) : Type v :=
  P.toPrepathObject.RightHomotopy f g

namespace RightHomotopy

section

variable [CategoryWithWeakEquivalences C] (P : PathObject Y)

/-- `f : X ⟶ Y` is right homotopic to itself relative to any path object. -/
abbrev refl (f : X ⟶ Y) : P.RightHomotopy f f := PrepathObject.RightHomotopy.refl _ f

variable {P} in
/-- If `f` and `g` are homotopic relative to a path object `P`, then `g` and `f`
are homotopic relative to `P.symm`. -/
abbrev symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f :=
  PrepathObject.RightHomotopy.symm h

variable {P} in
/-- Right homotopies are compatible with precomposition. -/
abbrev precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) :
    P.RightHomotopy (i ≫ f) (i ≫ g) :=
  PrepathObject.RightHomotopy.precomp h i

lemma weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [(weakEquivalences C).ContainsIdentities]
    {f₀ f₁ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  induction h
  grind [weakEquivalence_postcomp_iff]

end

section

variable [ModelCategory C] {P : PathObject Y}

/-- If `f₀ : X ⟶ Y` is homotopic to `f₁` relative to a path object `P`,
and `f₁` is homotopic to `f₂` relative to a good path object `P'`,
then `f₀` is homotopic to `f₂` relative to the path object `P.trans P'`
when `Y` is fibrant. -/
noncomputable abbrev trans [IsFibrant Y] {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.RightHomotopy f₀ f₁) {P' : PathObject Y} [P'.IsGood]
    (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] :
    (P.trans P').RightHomotopy f₀ f₂ :=
  PrepathObject.RightHomotopy.trans h h'

lemma exists_good_pathObject {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    ∃ (P' : PathObject Y), P'.IsGood ∧ Nonempty (P'.RightHomotopy f g) := by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.p
  exact
   ⟨{ P := d.Z
      p₀ := d.p ≫ prod.fst
      p₁ := d.p ≫ prod.snd
      ι := P.ι ≫ d.i }, ⟨by
        rw [fibration_iff]
        convert d.hp
        aesop⟩, ⟨{ h := h.h ≫ d.i }⟩⟩

/-- The homotopy extension theorem: if `p : A ⟶ X` is a cofibration,
`l₀ : X ⟶ B` is a morphism, if there is a right homotopy `h` between
the composition `f₀ := i ≫ l₀` and a morphism `f₁ : A ⟶ B`,
then there exists a morphism `l₁ : X ⟶ B` and a right homotopy `h'` from
`l₀` to `l₁` which is compatible with `h` (in particular, `i ≫ l₁ = f₁`). -/
lemma homotopy_extension {A B X : C} {P : PathObject B} {f₀ f₁ : A ⟶ B}
    [IsFibrant B] [P.IsGood]
    (h : P.RightHomotopy f₀ f₁) (i : A ⟶ X) [Cofibration i]
    (l₀ : X ⟶ B) (hl₀ : i ≫ l₀ = f₀ := by cat_disch) :
    ∃ (l₁ : X ⟶ B) (h' : P.RightHomotopy l₀ l₁), i ≫ h'.h = h.h :=
  have sq : CommSq h.h i P.p₀ l₀ := { }
  ⟨sq.lift ≫ P.p₁, { h := sq.lift }, by simp⟩

end

end RightHomotopy

end PathObject

/-- The right homotopy relation on morphisms in a category with weak equivalences. -/
def RightHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C :=
  fun _ Y f g ↦ ∃ (P : PathObject Y), Nonempty (P.RightHomotopy f g)

lemma PathObject.RightHomotopy.rightHomotopyRel [CategoryWithWeakEquivalences C]
    {X Y : C} {f g : X ⟶ Y}
    {P : PathObject Y} (h : P.RightHomotopy f g) :
    RightHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace RightHomotopyRel

variable (C) in
lemma factorsThroughLocalization [CategoryWithWeakEquivalences C] :
    RightHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.p₀ = L.map P.p₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.ι (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_epi (L.map P.ι), ← L.map_comp]

variable {X Y : C}

lemma refl [ModelCategory C] (f : X ⟶ Y) : RightHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨PathObject.RightHomotopy.refl _ _⟩⟩

lemma precomp [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : RightHomotopyRel f g) {Z : C} (i : Z ⟶ X) :
    RightHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.precomp i).rightHomotopyRel

lemma exists_good_pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) :
    ∃ (P : PathObject Y), P.IsGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_pathObject

lemma exists_very_good_pathObject [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X]
    (h : RightHomotopyRel f g) :
    ∃ (P : PathObject Y), P.IsVeryGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
  let fac := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.ι
  let P' : PathObject Y :=
    { P := fac.Z
      p₀ := fac.p ≫ P.p₀
      p₁ := fac.p ≫ P.p₁
      ι := fac.i
      weakEquivalence_ι := weakEquivalence_of_postcomp_of_fac fac.fac }
  have : Fibration P'.p := by
    rw [show P'.p = fac.p ≫ P.p by cat_disch]
    infer_instance
  have sq : CommSq (initial.to _) (initial.to _) fac.p h.h := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩⟩

lemma symm [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : RightHomotopyRel f g) : RightHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.rightHomotopyRel

lemma trans [ModelCategory C]
    {f₀ f₁ f₂ : X ⟶ Y} [IsFibrant Y] (h : RightHomotopyRel f₀ f₁)
    (h' : RightHomotopyRel f₁ f₂) : RightHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_pathObject
  exact (h.trans h').rightHomotopyRel

lemma equivalence [ModelCategory C] (X Y : C) [IsFibrant Y] :
    _root_.Equivalence (RightHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

set_option backward.isDefEq.respectTransparency false in
lemma postcomp [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotopyRel f g)
    {Z : C} (p : Y ⟶ Z) : RightHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  obtain ⟨Q, _⟩ := PathObject.exists_very_good Z
  have sq : CommSq (p ≫ Q.ι) P.ι Q.p (prod.lift (P.p₀ ≫ p) (P.p₁ ≫ p)) := { }
  exact ⟨Q,
   ⟨{ h := h.h ≫ sq.lift
      h₀ := by
        have := sq.fac_right =≫ prod.fst
        simp only [Category.assoc, prod.lift_fst, Q.p_fst] at this
        simp [this]
      h₁ := by
        have := sq.fac_right =≫ prod.snd
        simp only [Category.assoc, prod.lift_snd, Q.p_snd] at this
        simp [this]
    }⟩⟩

end RightHomotopyRel

variable (X Y Z : C)

/-- In a category with weak equivalences, this is the quotient of the type
of morphisms `X ⟶ Y` by the equivalence relation generated by right homotopies. -/
def RightHomotopyClass [CategoryWithWeakEquivalences C] :=
  _root_.Quot (RightHomotopyRel (X := X) (Y := Y))

variable {X Y Z}

/-- Given `f : X ⟶ Y`, this is the class of `f` in the quotient `RightHomotopyClass X Y`. -/
def RightHomotopyClass.mk [CategoryWithWeakEquivalences C] :
    (X ⟶ Y) → RightHomotopyClass X Y := Quot.mk _

lemma RightHomotopyClass.mk_surjective [CategoryWithWeakEquivalences C] :
    Function.Surjective (mk : (X ⟶ Y) → _) :=
  Quot.mk_surjective

namespace RightHomotopyClass

lemma sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) :
    mk f = mk g := Quot.sound h

/-- The precomposition map `RightHomotopyClass Y Z → (X ⟶ Y) → RightHomotopyClass X Z`. -/
def precomp [CategoryWithWeakEquivalences C] :
    RightHomotopyClass Y Z → (X ⟶ Y) → RightHomotopyClass X Z :=
  fun g f ↦ Quot.lift (fun g ↦ mk (f ≫ g)) (fun _ _ h ↦ sound (h.precomp f)) g

@[simp]
lemma precomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk g).precomp f = mk (f ≫ g) := rfl

lemma mk_eq_mk_iff [ModelCategory C] [IsFibrant Y] (f g : X ⟶ Y) :
    mk f = mk g ↔ RightHomotopyRel f g := by
  rw [← (RightHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

end RightHomotopyClass

end HomotopicalAlgebra
