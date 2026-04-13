/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# A binary product of finite simplicial sets is finite

If `X₁` and `X₂` are respectively of dimensions `≤ d₁` and `≤ d₂`,
then `X₁ ⊗ X₂` has dimension `≤ d₁ + d₂`.

We also show that if `X₁` and `X₂` are finite, then `X₁ ⊗ X₂` is also finite.

-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Simplicial Opposite

namespace SSet

variable {X₁ X₂ X₃ X₄ : SSet.{u}}

variable (X₁ X₂) in
lemma iSup_subcomplexOfSimplex_prod_eq_top :
    ⨆ (x₁ : X₁.N) (x₂ : X₂.N),
      (Subcomplex.ofSimplex x₁.simplex).prod (Subcomplex.ofSimplex x₂.simplex) = ⊤ := by
  ext m ⟨x₁, x₂⟩
  simp only [Subfunctor.iSup_obj, Subcomplex.prod_obj, Set.mem_iUnion, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  have hx₁ : x₁ ∈ (⊤ : X₁.Subcomplex).obj _ := by simp
  have hx₂ : x₂ ∈ (⊤ : X₂.Subcomplex).obj _ := by simp
  simp only [← N.iSup_subcomplex_eq_top, Subfunctor.iSup_obj, Set.mem_iUnion] at hx₁ hx₂
  obtain ⟨s₁, hs₁⟩ := hx₁
  obtain ⟨s₂, hs₂⟩ := hx₂
  exact ⟨s₁, s₂, hs₁, hs₂⟩

lemma Subcomplex.ofSimplexProd_eq_range {p q : ℕ} (x₁ : X₁ _⦋p⦌) (x₂ : X₂ _⦋q⦌) :
    (Subcomplex.ofSimplex x₁).prod (Subcomplex.ofSimplex x₂) =
      Subcomplex.range (yonedaEquiv.symm x₁ ⊗ₘ yonedaEquiv.symm x₂) := by
  simp [Subcomplex.range_tensorHom, Subcomplex.range_eq_ofSimplex]

variable (X₁ X₂) in
lemma hasDimensionLT_prod
    (d₁ d₂ : ℕ) [X₁.HasDimensionLT d₁] [X₂.HasDimensionLT d₂]
    (n : ℕ) (hn : d₁ + d₂ ≤ n + 1 := by lia) :
    (X₁ ⊗ X₂).HasDimensionLT n := by
  rw [← hasDimensionLT_subcomplex_top_iff, ← iSup_subcomplexOfSimplex_prod_eq_top]
  simp only [Subcomplex.ofSimplexProd_eq_range, hasDimensionLT_iSup_iff]
  intro x₁ x₂
  have := X₁.dim_lt_of_nonDegenerate ⟨_, x₁.nonDegenerate⟩ d₁
  have := X₂.dim_lt_of_nonDegenerate ⟨_, x₂.nonDegenerate⟩ d₂
  have := (Δ[x₁.dim] ⊗ Δ[x₂.dim]).hasDimensionLT_of_le (x₁.dim + x₂.dim + 1) n
  infer_instance

variable (X₁ X₂) in
lemma hasDimensionLE_prod
    (d₁ d₂ : ℕ) [X₁.HasDimensionLE d₁] [X₂.HasDimensionLE d₂]
    (n : ℕ) (hn : d₁ + d₂ ≤ n := by lia) :
    (X₁ ⊗ X₂).HasDimensionLE n :=
  hasDimensionLT_prod X₁ X₂ (d₁ + 1) (d₂ + 1) (n + 1)

instance (d₁ d₂ : ℕ) [X₁.HasDimensionLT d₁] [X₂.HasDimensionLT d₂] :
    (X₁ ⊗ X₂).HasDimensionLT (d₁ + d₂) :=
  hasDimensionLT_prod _ _ d₁ d₂ (d₁ + d₂)

instance (d₁ d₂ : ℕ) [X₁.HasDimensionLE d₁] [X₂.HasDimensionLE d₂] :
    (X₁ ⊗ X₂).HasDimensionLE (d₁ + d₂) :=
  hasDimensionLE_prod _ _ d₁ d₂ (d₁ + d₂)

instance [X₁.Finite] [X₂.Finite] : (X₁ ⊗ X₂).Finite := by
  obtain ⟨d₁, _⟩ := X₁.hasDimensionLT_of_finite
  obtain ⟨d₂, _⟩ := X₂.hasDimensionLT_of_finite
  exact finite_of_hasDimensionLT _ (d₁ + d₂) (fun _ _ ↦ inferInstance)

open CartesianMonoidalCategory in
lemma finite_of_isPullback {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPullback t l r b) [X₂.Finite] [X₃.Finite] : X₁.Finite :=
  have : Mono (lift t l) :=
    ⟨fun _ _ h ↦ sq.hom_ext (by simpa using h =≫ fst _ _) (by simpa using h =≫ snd _ _)⟩
  finite_of_mono (lift t l)

instance [X₂.Finite] [X₃.Finite] (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) :
    (pullback r b).Finite :=
  finite_of_isPullback (IsPullback.of_hasPullback r b)

end SSet
