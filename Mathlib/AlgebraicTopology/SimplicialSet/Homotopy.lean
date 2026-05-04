/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism

/-!
# Simplicial homotopies

In this file, we define the notion of homotopy (`SSet.Homotopy`) between
morphisms `f : X ⟶ Y` and `g : X ⟶ Y` of simplicial sets: it involves
a morphism `X ⊗ Δ[1] ⟶ Y` inducing both `f` and `g`. (This definition is
a particular case of `SSet.RelativeMorphism.Homotopy` that is defined in
the file `Mathlib/AlgebraicTopology/SimplicialSet/RelativeMorphism.lean`).
We show that from `H : SSet.Homotopy f g`, we can obtain a combinatorial
homotopy `SimplicialObject.Homotopy f g` (where the data involve
a family of maps `X _⦋n⦌ → Y _⦋n + 1⦌` for all `n : ℕ` and `i : Fin (n + 1)`.)

-/

@[expose] public section

open CategoryTheory SimplicialObject MonoidalCategory Simplicial Opposite

universe u

namespace SSet

variable {X Y : SSet.{u}}

/-- Morphisms relatively to the `⊥` subcomplexes of `X` and `Y`
identify to morphisms `X ⟶ Y`. -/
@[simps]
def RelativeMorphism.botEquiv :
    RelativeMorphism (⊥ : X.Subcomplex) (⊥ : Y.Subcomplex)
      (Subcomplex.isInitialBot.to _) ≃ (X ⟶ Y) where
  toFun f := f.map
  invFun f := { map := f }

/-- The type of homotopies between morphisms `X ⟶ Y` of simplicial sets.
The data consists of a morphism `h : X ⊗ Δ[1] ⟶ Y` which induces
both `f` and `g`, see the lemmas `SSet.Homotopy.h₀` and `SSet.Homotopy.h₁`. -/
def Homotopy (f g : X ⟶ Y) : Type u :=
  (RelativeMorphism.botEquiv.symm f).Homotopy (RelativeMorphism.botEquiv.symm g)

namespace Homotopy

variable {f g : X ⟶ Y}

@[reassoc (attr := simp high)]
lemma h₀ (H : Homotopy f g) : ι₀ ≫ H.h = f :=
  RelativeMorphism.Homotopy.h₀ H

@[reassoc (attr := simp high)]
lemma h₁ (H : Homotopy f g) : ι₁ ≫ H.h = g :=
  RelativeMorphism.Homotopy.h₁ H

set_option backward.isDefEq.respectTransparency false in
/-- If `H : Homotopy f g` is a homotopy between morphisms of simplicial sets
`f : X ⟶ Y` and `g : X ⟶ Y` (i.e. `H.h` is a morphism `X ⊗ Δ[1] ⟶ Y` inducing
`f` and `g`), then this is the corresponding (combinatorial) homotopy of
morphisms of simplicial objects between `f` and `g`. -/
-- Adaption note (lean4#13557): `dsimp` no longer makes progress at the
-- intermediate steps in these proofs (it relied on `[backward_defeq]` rules
-- being treated as `[defeq]`).  TODO(joachim): rewrite the proofs without
-- relying on the implicit `dsimp` behaviour.
noncomputable def toSimplicialObjectHomotopy (H : Homotopy f g) :
    SimplicialObject.Homotopy f g where
  h i := ↾fun x ↦
    (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app _ (prodStdSimplex.nonDegenerateEquiv₁ i).1
  h_zero_comp_δ_zero n := by sorry
  h_last_comp_δ_last n := by sorry
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by sorry
  h_succ_comp_δ_castSucc_succ {n} i := by sorry
  h_castSucc_comp_δ_succ_of_lt {n} i j hij := by sorry
  h_comp_σ_castSucc_of_le {n} i j hij := by sorry
  h_comp_σ_succ_of_lt {n} i j hij := by sorry

end Homotopy

end SSet
