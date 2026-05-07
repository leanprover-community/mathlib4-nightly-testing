/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# Parallel pairs of natural transformations between ind-objects

We show that if `A` and `B` are ind-objects and `f` and `g` are natural transformations between
`A` and `B`, then there is a small filtered category `I` such that `A`, `B`, `f` and `g` are
commonly presented by diagrams and natural transformations in `I ⥤ C`.


## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 6.1.15 (though
  our proof is more direct).
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Functor

variable {C : Type u₁} [Category.{v₁} C]

/-- Structure containing data exhibiting two parallel natural transformations `f` and `g` between
presheaves `A` and `B` as induced by a natural transformation in a functor category exhibiting
`A` and `B` as ind-objects. -/
structure IndParallelPairPresentation {A B : Cᵒᵖ ⥤ Type v₁} (f g : A ⟶ B) where
  /-- The indexing category. -/
  I : Type v₁
  /-- Category instance on the indexing category. -/
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  /-- The diagram presenting `A`. -/
  F₁ : I ⥤ C
  /-- The diagram presenting `B`. -/
  F₂ : I ⥤ C
  /-- The cocone on `F₁` with apex `A`. -/
  ι₁ : F₁ ⋙ yoneda ⟶ (Functor.const I).obj A
  /-- The cocone on `F₁` with apex `A` is a colimit cocone. -/
  isColimit₁ : IsColimit (Cocone.mk A ι₁)
  /-- The cocone on `F₂` with apex `B`. -/
  ι₂ : F₂ ⋙ yoneda ⟶ (Functor.const I).obj B
  /-- The cocone on `F₂` with apex `B` is a colimit cocone. -/
  isColimit₂ : IsColimit (Cocone.mk B ι₂)
  /-- The natural transformation presenting `f`. -/
  φ : F₁ ⟶ F₂
  /-- The natural transformation presenting `g`. -/
  ψ : F₁ ⟶ F₂
  /-- `f` is in fact presented by `φ`. -/
  hf : f = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight φ yoneda)
  /-- `g` is in fact presented by `ψ`. -/
  hg : g = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight ψ yoneda)

instance {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B} (P : IndParallelPairPresentation f g) :
    SmallCategory P.I := P.ℐ
instance {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B} (P : IndParallelPairPresentation f g) :
    IsFiltered P.I := P.hI

namespace NonemptyParallelPairPresentationAux

variable {A B : Cᵒᵖ ⥤ Type v₁} (f g : A ⟶ B) (P₁ : IndObjectPresentation A)
  (P₂ : IndObjectPresentation B)

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
abbrev K : Type v₁ :=
  Comma ((P₁.toCostructuredArrow ⋙ CostructuredArrow.map f).prod'
    (P₁.toCostructuredArrow ⋙ CostructuredArrow.map g))
    (P₂.toCostructuredArrow.prod' P₂.toCostructuredArrow)

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
abbrev F₁ : K f g P₁ P₂ ⥤ C := Comma.fst _ _ ⋙ P₁.F
/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
abbrev F₂ : K f g P₁ P₂ ⥤ C := Comma.snd _ _ ⋙ P₂.F

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
abbrev ι₁ : F₁ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj A :=
  whiskerLeft (Comma.fst _ _) P₁.ι

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
noncomputable abbrev isColimit₁ : IsColimit (Cocone.mk A (ι₁ f g P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₁.isColimit

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
abbrev ι₂ : F₂ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj B :=
  whiskerLeft (Comma.snd _ _) P₂.ι

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
noncomputable abbrev isColimit₂ : IsColimit (Cocone.mk B (ι₂ f g P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₂.isColimit

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
def ϕ : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  app h := h.hom.1.left
  naturality _ _ h := by
    have := h.w
    simp only [ prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.1

set_option backward.simpa.using.reducibleClose false in
set_option backward.defeqAttrib.useBackward true in
theorem hf : f = IsColimit.map (isColimit₁ f g P₁ P₂)
    (Cocone.mk B (ι₂ f g P₁ P₂)) (whiskerRight (ϕ f g P₁ P₂) yoneda) := by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using i.hom.1.w.symm

/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
def ψ : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  app h := h.hom.2.left
  naturality _ _ h := by
    have := h.w
    simp only [ prod'_map, Functor.comp_map, Prod.hom_ext_iff,
      CostructuredArrow.hom_eq_iff] at this
    exact this.2

set_option backward.simpa.using.reducibleClose false in
set_option backward.defeqAttrib.useBackward true in
theorem hg : g = IsColimit.map (isColimit₁ f g P₁ P₂)
    (Cocone.mk B (ι₂ f g P₁ P₂)) (whiskerRight (ψ f g P₁ P₂) yoneda) := by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using i.hom.2.w.symm

attribute [local instance] Comma.isFiltered_of_final in
/-- Implementation; see `nonempty_indParallelPairPresentation`. -/
noncomputable def presentation : IndParallelPairPresentation f g where
  I := K f g P₁ P₂
  F₁ := F₁ f g P₁ P₂
  F₂ := F₂ f g P₁ P₂
  ι₁ := ι₁ f g P₁ P₂
  isColimit₁ := isColimit₁ f g P₁ P₂
  ι₂ := ι₂ f g P₁ P₂
  isColimit₂ := isColimit₂ f g P₁ P₂
  φ := ϕ f g P₁ P₂
  ψ := ψ f g P₁ P₂
  hf := hf f g P₁ P₂
  hg := hg f g P₁ P₂

end NonemptyParallelPairPresentationAux

theorem nonempty_indParallelPairPresentation {A B : Cᵒᵖ ⥤ Type v₁} (hA : IsIndObject A)
    (hB : IsIndObject B) (f g : A ⟶ B) : Nonempty (IndParallelPairPresentation f g) :=
  ⟨NonemptyParallelPairPresentationAux.presentation f g hA.presentation hB.presentation⟩

namespace IndParallelPairPresentation

set_option backward.isDefEq.respectTransparency false in
/-- Given an `IndParallelPairPresentation f g`, we can understand the parallel pair `(f, g)`
as the colimit of `(P.φ, P.ψ)` in `Cᵒᵖ ⥤ Type v`. -/
noncomputable def parallelPairIsoParallelPairCompYoneda {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B}
    (P : IndParallelPairPresentation f g) :
    parallelPair f g ≅ parallelPair P.φ P.ψ ⋙ (whiskeringRight _ _ _).obj yoneda ⋙ colim :=
  parallelPair.ext
    (P.isColimit₁.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₂.coconePointUniqueUpToIso (colimit.isColimit _))
    (P.isColimit₁.hom_ext (fun j => by
      simp [P.hf, P.isColimit₁.ι_map_assoc, P.isColimit₁.comp_coconePointUniqueUpToIso_hom_assoc,
        P.isColimit₂.comp_coconePointUniqueUpToIso_hom]))
    (P.isColimit₁.hom_ext (fun j => by
      simp [P.hg, P.isColimit₁.ι_map_assoc, P.isColimit₁.comp_coconePointUniqueUpToIso_hom_assoc,
        P.isColimit₂.comp_coconePointUniqueUpToIso_hom]))

end IndParallelPairPresentation

end CategoryTheory
