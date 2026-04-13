/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer

/-!
# Colimits involving subcomplexes of a simplicial set

If `X` is a simplicial set, and we have subcomplexes `A`, `U i` (for `i : ι`) and
`V i j` which satisfy `Subcomplex.MulticoequalizerDiagram A U V` (an abbreviation
for `CompleteLattice.MulticoequalizerDiagram`), we
show that the simplicial sset corresponding to `A` is the multicoequalizer of
the `U i` along the `V i j`.

Similarly, bicartesian squares in the lattice `Subcomplex X` give pushout
squares in the category of simplicial sets.

-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}}

section

variable {A : X.Subcomplex} {ι : Type*}
  {U : ι → X.Subcomplex} {V : ι → ι → X.Subcomplex}

variable (A U V) in
/-- Abbreviation for multicoequalizer diagrams in the complete lattice of
subcomplexes of a simplicial set. -/
abbrev MulticoequalizerDiagram := CompleteLattice.MulticoequalizerDiagram A U V

namespace MulticoequalizerDiagram

variable (h : MulticoequalizerDiagram A U V)

/-- The colimit multicofork attached to a `MulticoequalizerDiagram`
structure in the complete lattice of subcomplexes of a simplicial set. -/
noncomputable def isColimit :
    IsColimit (h.multicofork.map toSSetFunctor) :=
  evaluationJointlyReflectsColimits _ (fun n ↦ by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i ↦ (U i).obj n)
        (fun i j ↦ (V i j).obj n) :=
      { eq_inf := by simp [h.eq_inf]
        iSup_eq := by simp [← h.iSup_eq] }
    exact (Multicofork.isColimitMapEquiv _ _).2
      (Types.isColimitOfMulticoequalizerDiagram h'))

/-- A colimit multicofork attached to a `MulticoequalizerDiagram`
structure in the complete lattice of subcomplexes of a simplicial set.
In this variant, we assume that the index type `ι` has a linear order. This allows
to consider only the "relations" given by tuples `(i, j)` such that `i < j`. -/
noncomputable def isColimit' [LinearOrder ι] :
    IsColimit (h.multicofork.toLinearOrder.map toSSetFunctor) :=
  Multicofork.isColimitToLinearOrder _ h.isColimit
    { iso i j := toSSetFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf, h.eq_inf, inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

end MulticoequalizerDiagram

end

/-- Abbreviation for bicartesian squares in the lattice of subcomplexes of a simplicial set. -/
abbrev BicartSq (A₁ A₂ A₃ A₄ : X.Subcomplex) := Lattice.BicartSq A₁ A₂ A₃ A₄

lemma BicartSq.isPushout {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : BicartSq A₁ A₂ A₃ A₄) :
    IsPushout (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) where
  w := rfl
  isColimit' :=
    ⟨evaluationJointlyReflectsColimits _
      (fun n ↦ (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (by
        have h : Lattice.BicartSq (A₁.obj n) (A₂.obj n) (A₃.obj n) (A₄.obj n) :=
          { sup_eq := by
              rw [← sq.sup_eq]
              rfl
            inf_eq := by
              rw [← sq.inf_eq]
              rfl }
        exact (Types.isPushout_of_bicartSq h).isColimit))⟩

end Subcomplex

end SSet
