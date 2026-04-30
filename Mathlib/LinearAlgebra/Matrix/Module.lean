/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Basis

/-!
# Mₙ(R)-module structure on `Mⁿ`

## Main Results

- `Matrix.Module.matrixModule`: This instance shows `ι → M` is a module over `Matrix ι ι R`, and
  the action of it is a generalization of `Matrix.mulVec`, this is only available in the
  `Matrix.Module` namespace.
- `LinearMap.mapMatrixModule`: This defines a linear map from `ι → M` to `ι → N` over
  `Matrix ι ι R` induced by a linear map from `M` to `N` and together with `Matrix.matrixModule`
  it gives a functor from the category of `R`-modules to the category of `Matrix ι ι R`-modules.

## Tags
matrix, module
-/

@[expose] public section

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

namespace Matrix.Module

/-- `Mⁿ` is a `Mₙ(R)` module, note that this creates a diamond when `M` is `Matrix ι ι R` or when
  `M` is `R`. -/
scoped instance matrixModule : Module (Matrix ι ι R) (ι → M) where
  smul N v i := ∑ j : ι, N i j • v j
  one_smul v := funext fun i ↦ show ∑ _, _ = _ by simp [one_apply]
  mul_smul N₁ N₂ v := funext fun i ↦ show ∑ _, _ = ∑ _, _ • (∑ _, _) by
    simp_rw [mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
  smul_zero v := funext fun i ↦ show ∑ _, _ = _ by simp
  smul_add N v₁ v₂ := funext fun i ↦ show ∑ j : ι, N i j • (v₁ + v₂) j = (∑ _, _) + (∑ _, _) by
    simp [smul_add, Finset.sum_add_distrib]
  add_smul N₁ N₂ v := funext fun i ↦ show ∑ j : ι, (N₁ + N₂) i j • v j = (∑ _, _) + (∑ _, _) by
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul v := funext fun i ↦ show ∑ _, _ = _ by simp

lemma smul_def (N : Matrix ι ι R) (v : ι → M) :
    N • v = fun i ↦ ∑ j : ι, N i j • v j := rfl

lemma smul_def' (N : Matrix ι ι R) (v : ι → M) : N • v = ∑ j : ι, fun i ↦ N i j • v j := by
  ext; simp [smul_def]

@[simp]
lemma smul_apply (N : Matrix ι ι R) (v : ι → M) (i : ι) :
    (N • v) i = ∑ j : ι, N i j • v j := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem single_smul (i j : ι) (r : R) (v : ι → M) :
    Matrix.single i j r • v = Pi.single i (r • v j) := by
  ext i'
  dsimp
  rw [Fintype.sum_eq_single j fun j' hj => ?_]
  · obtain rfl | hi := eq_or_ne i i' <;> simp [*]
  · simp [hj.symm]

@[simp]
lemma diagonal_const_smul (r : R) (v : ι → M) :
    diagonal (fun _ : ι ↦ r) • v = r • v := by
  ext i
  simp [Matrix.diagonal_apply]

lemma scalar_smul (r : R) (v : ι → M) :
    Matrix.scalar ι r • v = r • v := by
  simp

scoped instance (S : Type*) [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    IsScalarTower R (Matrix ι ι S) (ι → M) where
  smul_assoc _ _ _ := by ext; simp [Finset.smul_sum]

end Matrix.Module

namespace LinearMap

open Matrix.Module

variable (ι) in
/-- The induced linear map from `Mⁿ` to `Nⁿ` by a linear map `f : M → N`, this is the matrix linear
  version of `LinearMap.compLeft`. -/
@[simps]
def mapMatrixModule (f : M →ₗ[R] N) : (ι → M) →ₗ[Matrix ι ι R] (ι → N) where
  toFun := LinearMap.compLeft f ι
  map_add' := map_add _
  map_smul' _ _ := by ext; simp

@[simp]
lemma mapMatrixModule_id :
    LinearMap.id.mapMatrixModule ι = .id (R := Matrix ι ι R) (M := ι → M) := by
  ext; simp

lemma mapMatrixModule_id_apply (v : ι → M) :
    LinearMap.id.mapMatrixModule ι (R := R) v = v := by
  simp

lemma mapMatrixModule_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (g ∘ₗ f).mapMatrixModule ι = g.mapMatrixModule ι ∘ₗ f.mapMatrixModule ι := by
  ext; simp

@[simp]
lemma mapMatrixModule_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (v : ι → M) :
    (g ∘ₗ f).mapMatrixModule ι v =
      g.mapMatrixModule ι (f.mapMatrixModule ι v) := by
  simp [mapMatrixModule_comp]

end LinearMap
