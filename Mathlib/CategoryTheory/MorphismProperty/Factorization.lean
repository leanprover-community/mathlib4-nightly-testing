/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# The factorization axiom

In this file, we introduce a type-class `HasFactorization W₁ W₂`, which, given
two classes of morphisms `W₁` and `W₂` in a category `C`, asserts that any morphism
in `C` can be factored as a morphism in `W₁` followed by a morphism in `W₂`. The data
of such factorizations can be packaged in the type `FactorizationData W₁ W₂`.

This shall be used in the formalization of model categories for which the CM5 axiom
asserts that any morphism can be factored as a cofibration followed by a trivial
fibration (or a trivial cofibration followed by a fibration).

We also provide a structure `FunctorialFactorizationData W₁ W₂` which contains
the data of a functorial factorization as above. With this design, when we
formalize certain constructions (e.g. cylinder objects in model categories),
we may first construct them using the data `data : FactorizationData W₁ W₂`.
Without duplication of code, it shall be possible to show these cylinders
are functorial when a term `data : FunctorialFactorizationData W₁ W₂` is available,
the existence of which is asserted in the type-class `HasFunctorialFactorization W₁ W₂`.

We also introduce the class `W₁.comp W₂` of morphisms of the form `i ≫ p` with `W₁ i`
and `W₂ p` and show that `W₁.comp W₂ = ⊤` iff `HasFactorization W₁ W₂` holds (this
is `MorphismProperty.comp_eq_top_iff`).

-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)

/-- Given two classes of morphisms `W₁` and `W₂` on a category `C`, this is
the data of the factorization of a morphism `f : X ⟶ Y` as `i ≫ p` with
`W₁ i` and `W₂ p`. -/
structure MapFactorizationData {X Y : C} (f : X ⟶ Y) where
  /-- the intermediate object in the factorization -/
  Z : C
  /-- the first morphism in the factorization -/
  i : X ⟶ Z
  /-- the second morphism in the factorization -/
  p : Z ⟶ Y
  fac : i ≫ p = f := by cat_disch
  hi : W₁ i
  hp : W₂ p

namespace MapFactorizationData

attribute [reassoc (attr := simp)] fac

variable {X Y : C} (f : X ⟶ Y)

/-- The opposite of a factorization. -/
@[simps]
def op {X Y : C} {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f) :
    MapFactorizationData W₂.op W₁.op f.op where
  Z := Opposite.op hf.Z
  i := hf.p.op
  p := hf.i.op
  fac := Quiver.Hom.unop_inj (by simp)
  hi := hf.hp
  hp := hf.hi

end MapFactorizationData

/-- The data of a term in `MapFactorizationData W₁ W₂ f` for any morphism `f`. -/
abbrev FactorizationData := ∀ {X Y : C} (f : X ⟶ Y), MapFactorizationData W₁ W₂ f

/-- The factorization axiom for two classes of morphisms `W₁` and `W₂` in a category `C`. It
asserts that any morphism can be factored as a morphism in `W₁` followed by a morphism
in `W₂`. -/
class HasFactorization : Prop where
  nonempty_mapFactorizationData {X Y : C} (f : X ⟶ Y) : Nonempty (MapFactorizationData W₁ W₂ f)

/-- A chosen term in `FactorizationData W₁ W₂` when `HasFactorization W₁ W₂` holds. -/
noncomputable def factorizationData [HasFactorization W₁ W₂] : FactorizationData W₁ W₂ :=
  fun _ => Nonempty.some (HasFactorization.nonempty_mapFactorizationData _)

instance [HasFactorization W₁ W₂] : HasFactorization W₂.op W₁.op where
  nonempty_mapFactorizationData f := ⟨(factorizationData W₁ W₂ f.unop).op⟩

/-- The class of morphisms that are of the form `i ≫ p` with `W₁ i` and `W₂ p`. -/
def comp : MorphismProperty C := fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)

lemma comp_eq_top_iff : W₁.comp W₂ = ⊤ ↔ HasFactorization W₁ W₂ := by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have : W₁.comp W₂ f := by simp only [h, top_apply]
    exact ⟨this.some⟩
  · intro
    ext X Y f
    simp only [top_apply, iff_true]
    exact ⟨factorizationData W₁ W₂ f⟩

/-- The data of a functorial factorization of any morphism in `C` as a morphism in `W₁`
followed by a morphism in `W₂`. -/
structure FunctorialFactorizationData where
  /-- the intermediate objects in the factorizations -/
  Z : Arrow C ⥤ C
  /-- the first morphism in the factorizations -/
  i : Arrow.leftFunc ⟶ Z
  /-- the second morphism in the factorizations -/
  p : Z ⟶ Arrow.rightFunc
  fac : i ≫ p = Arrow.leftToRight := by cat_disch
  hi (f : Arrow C) : W₁ (i.app f)
  hp (f : Arrow C) : W₂ (p.app f)

namespace FunctorialFactorizationData

variable {W₁ W₂}
variable (data : FunctorialFactorizationData W₁ W₂)

attribute [reassoc (attr := simp)] fac

@[reassoc (attr := simp)]
lemma fac_app {f : Arrow C} : data.i.app f ≫ data.p.app f = f.hom := by
  rw [← NatTrans.comp_app, fac, Arrow.leftToRight_app]

/-- If `W₁ ≤ W₁'` and `W₂ ≤ W₂'`, then a functorial factorization for `W₁` and `W₂` induces
a functorial factorization for `W₁'` and `W₂'`. -/
def ofLE {W₁' W₂' : MorphismProperty C} (le₁ : W₁ ≤ W₁') (le₂ : W₂ ≤ W₂') :
    FunctorialFactorizationData W₁' W₂' where
  Z := data.Z
  i := data.i
  p := data.p
  hi f := le₁ _ (data.hi f)
  hp f := le₂ _ (data.hp f)

set_option backward.isDefEq.respectTransparency false in
/-- The term in `FactorizationData W₁ W₂` that is deduced from a functorial factorization. -/
def factorizationData : FactorizationData W₁ W₂ := fun f =>
  { Z := data.Z.obj (Arrow.mk f)
    i := data.i.app (Arrow.mk f)
    p := data.p.app (Arrow.mk f)
    hi := data.hi _
    hp := data.hp _ }

section

variable {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g)

/-- When `data : FunctorialFactorizationData W₁ W₂`, this is the
morphism `(data.factorizationData f).Z ⟶ (data.factorizationData g).Z` expressing the
functoriality of the intermediate objects of the factorizations
for `φ : Arrow.mk f ⟶ Arrow.mk g`. -/
def mapZ : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z := data.Z.map φ

@[reassoc (attr := simp)]
lemma i_mapZ :
    (data.factorizationData f).i ≫ data.mapZ φ = φ.left ≫ (data.factorizationData g).i :=
  (data.i.naturality φ).symm

@[reassoc (attr := simp)]
lemma mapZ_p :
    data.mapZ φ ≫ (data.factorizationData g).p = (data.factorizationData f).p ≫ φ.right :=
  data.p.naturality φ

variable (f) in
@[simp]
lemma mapZ_id : data.mapZ (𝟙 (Arrow.mk f)) = 𝟙 _ :=
  data.Z.map_id _

@[reassoc, simp]
lemma mapZ_comp {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    data.mapZ (φ ≫ ψ) = data.mapZ φ ≫ data.mapZ ψ :=
  data.Z.map_comp _ _

end

section

variable (J : Type*) [Category* J]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `FunctorialFactorizationData.functorCategory`. -/
@[simps]
def functorCategory.Z : Arrow (J ⥤ C) ⥤ J ⥤ C where
  obj f :=
    { obj := fun j => (data.factorizationData (f.hom.app j)).Z
      map := fun φ => data.mapZ
        { left := f.left.map φ
          right := f.right.map φ }
      map_id := fun j => by
        dsimp
        rw [← data.mapZ_id (f.hom.app j)]
        congr <;> simp
      map_comp := fun _ _ => by
        dsimp
        rw [← data.mapZ_comp]
        congr <;> simp }
  map τ :=
    { app := fun j => data.mapZ
        { left := τ.left.app j
          right := τ.right.app j
          w := congr_app τ.w j }
      naturality := fun _ _ α => by
        dsimp
        rw [← data.mapZ_comp, ← data.mapZ_comp]
        congr 1
        ext <;> simp }
  map_id f := by
    ext j
    dsimp
    rw [← data.mapZ_id]
    congr 1
  map_comp f g := by
    ext j
    dsimp
    rw [← data.mapZ_comp]
    congr 1

/-- A functorial factorization in the category `C` extends to the functor category `J ⥤ C`. -/
def functorCategory :
    FunctorialFactorizationData (W₁.functorCategory J) (W₂.functorCategory J) where
  Z := functorCategory.Z data J
  i := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).i } }
  p := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).p } }
  hi _ _ := data.hi _
  hp _ _ := data.hp _

end

end FunctorialFactorizationData

/-- The functorial factorization axiom for two classes of morphisms `W₁` and `W₂` in a
category `C`. It asserts that any morphism can be factored in a functorial manner
as a morphism in `W₁` followed by a morphism in `W₂`. -/
class HasFunctorialFactorization : Prop where
  nonempty_functorialFactorizationData : Nonempty (FunctorialFactorizationData W₁ W₂)

/-- A chosen term in `FunctorialFactorizationData W₁ W₂` when the functorial factorization
axiom `HasFunctorialFactorization W₁ W₂` holds. -/
noncomputable def functorialFactorizationData [HasFunctorialFactorization W₁ W₂] :
    FunctorialFactorizationData W₁ W₂ :=
  Nonempty.some (HasFunctorialFactorization.nonempty_functorialFactorizationData)

instance [HasFunctorialFactorization W₁ W₂] : HasFactorization W₁ W₂ where
  nonempty_mapFactorizationData f := ⟨(functorialFactorizationData W₁ W₂).factorizationData f⟩

instance [HasFunctorialFactorization W₁ W₂] (J : Type*) [Category* J] :
    HasFunctorialFactorization (W₁.functorCategory J) (W₂.functorCategory J) :=
  ⟨⟨(functorialFactorizationData W₁ W₂).functorCategory J⟩⟩

end MorphismProperty

end CategoryTheory
