/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Graded tensor products over graded algebras

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ℕ`, `ℤ`, or `ZMod 2` (or more generally, any index
that satisfies `Module ι (Additive ℤˣ)`).

The results for internally-graded algebras (via `GradedAlgebra`) are elsewhere, as is the type
`GradedTensorProduct`.

## Main results

* `TensorProduct.gradedComm`: the symmetric braiding operator on the tensor product of
  externally-graded rings.
* `TensorProduct.gradedMul`: the previously-described multiplication on externally-graded rings, as
  a bilinear map.

## Implementation notes

Rather than implementing the multiplication directly as above, we first implement the canonical
non-trivial braiding sending $a \otimes b$ to $(-1)^{\deg a' \deg b} (b \otimes a)$, as the
multiplication follows trivially from this after some point-free nonsense.

## References

* https://math.stackexchange.com/q/202718/1896
* [*Algebra I*, Bourbaki : Chapter III, §4.7, example (2)][bourbaki1989]

-/

@[expose] public section

open scoped TensorProduct DirectSum

variable {R ι : Type*}

namespace TensorProduct

variable [CommSemiring ι] [Module ι (Additive ℤˣ)] [DecidableEq ι]
variable (𝒜 : ι → Type*) (ℬ : ι → Type*)
variable [CommRing R]
variable [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (ℬ i)]
variable [∀ i, Module R (𝒜 i)] [∀ i, Module R (ℬ i)]

-- this helps with performance
instance (i : ι × ι) : Module R (𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i)) :=
  TensorProduct.leftModule

open DirectSum (lof)

variable (R)

section gradedComm

local notation "𝒜ℬ" => (fun i : ι × ι => 𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i))
local notation "ℬ𝒜" => (fun i : ι × ι => ℬ (Prod.fst i) ⊗[R] 𝒜 (Prod.snd i))

/-- Auxiliary construction used to build `TensorProduct.gradedComm`.

This operates on direct sums of tensors instead of tensors of direct sums. -/
def gradedCommAux : DirectSum _ 𝒜ℬ →ₗ[R] DirectSum _ ℬ𝒜 :=
  DirectSum.toModule R _ _ fun i =>
    have o := DirectSum.lof R _ ℬ𝒜 (i.2, i.1)
    have s : ℤˣ := ((-1 : ℤˣ) ^ (i.1 * i.2 : ι) : ℤˣ)
    (s • o) ∘ₗ (TensorProduct.comm R _ _).toLinearMap

@[simp]
theorem gradedCommAux_lof_tmul (i j : ι) (a : 𝒜 i) (b : ℬ j) :
    gradedCommAux R 𝒜 ℬ (lof R _ 𝒜ℬ (i, j) (a ⊗ₜ b)) =
      (-1 : ℤˣ) ^ (j * i) • lof R _ ℬ𝒜 (j, i) (b ⊗ₜ a) := by
  rw [gradedCommAux]
  simp [mul_comm i j]

set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem gradedCommAux_comp_gradedCommAux :
    gradedCommAux R 𝒜 ℬ ∘ₗ gradedCommAux R ℬ 𝒜 = LinearMap.id := by
  ext i a b
  dsimp
  rw [gradedCommAux_lof_tmul, LinearMap.map_smul_of_tower, gradedCommAux_lof_tmul, smul_smul,
    mul_comm i.2 i.1, Int.units_mul_self, one_smul]

/-- The braiding operation for tensor products of externally `ι`-graded algebras.

This sends $a ⊗ b$ to $(-1)^{\deg a' \deg b} (b ⊗ a)$. -/
def gradedComm :
    (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) ≃ₗ[R] (⨁ i, ℬ i) ⊗[R] (⨁ i, 𝒜 i) := by
  refine TensorProduct.directSum R R 𝒜 ℬ ≪≫ₗ ?_ ≪≫ₗ (TensorProduct.directSum R R ℬ 𝒜).symm
  exact LinearEquiv.ofLinear (gradedCommAux _ _ _) (gradedCommAux _ _ _)
    (gradedCommAux_comp_gradedCommAux _ _ _) (gradedCommAux_comp_gradedCommAux _ _ _)

/-- The braiding is symmetric. -/
@[simp]
theorem gradedComm_symm : (gradedComm R 𝒜 ℬ).symm = gradedComm R ℬ 𝒜 := by
  rfl

theorem gradedComm_of_tmul_of (i j : ι) (a : 𝒜 i) (b : ℬ j) :
    gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a ⊗ₜ lof R _ ℬ j b) =
      (-1 : ℤˣ) ^ (j * i) • (lof R _ ℬ _ b ⊗ₜ lof R _ 𝒜 _ a) := by
  rw [gradedComm]
  dsimp only [LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply]
  rw [TensorProduct.directSum_lof_tmul_lof, gradedCommAux_lof_tmul, Units.smul_def,
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 specialized `map_smul` to `LinearEquiv.map_smul` to avoid timeouts.
    ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul, TensorProduct.directSum_symm_lof_tmul,
    Int.cast_smul_eq_zsmul, ← Units.smul_def]

theorem gradedComm_tmul_of_zero (a : ⨁ i, 𝒜 i) (b : ℬ 0) :
    gradedComm R 𝒜 ℬ (a ⊗ₜ lof R _ ℬ 0 b) = lof R _ ℬ _ b ⊗ₜ a := by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ
        (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)).flip (lof R _ ℬ 0 b) =
      TensorProduct.mk R _ _ (lof R _ ℬ 0 b) from
    DFunLike.congr_fun this a
  ext i a
  dsimp
  rw [gradedComm_of_tmul_of, zero_mul, uzpow_zero, one_smul]

theorem gradedComm_of_zero_tmul (a : 𝒜 0) (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (lof R _ 𝒜 0 a ⊗ₜ b) = b ⊗ₜ lof R _ 𝒜 _ a := by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)) (lof R _ 𝒜 0 a) =
      (TensorProduct.mk R _ _).flip (lof R _ 𝒜 0 a) from
    DFunLike.congr_fun this b
  ext i b
  dsimp
  rw [gradedComm_of_tmul_of, mul_zero, uzpow_zero, one_smul]

theorem gradedComm_tmul_one [GradedMonoid.GOne ℬ] (a : ⨁ i, 𝒜 i) :
    gradedComm R 𝒜 ℬ (a ⊗ₜ 1) = 1 ⊗ₜ a :=
  gradedComm_tmul_of_zero _ _ _ _ _

theorem gradedComm_one_tmul [GradedMonoid.GOne 𝒜] (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (1 ⊗ₜ b) = b ⊗ₜ 1 :=
  gradedComm_of_zero_tmul _ _ _ _ _

@[simp]
theorem gradedComm_one [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ] : gradedComm R 𝒜 ℬ 1 = 1 :=
  gradedComm_one_tmul _ _ _ _

theorem gradedComm_tmul_algebraMap [DirectSum.GSemiring ℬ] [DirectSum.GAlgebra R ℬ]
    (a : ⨁ i, 𝒜 i) (r : R) :
    gradedComm R 𝒜 ℬ (a ⊗ₜ algebraMap R _ r) = algebraMap R _ r ⊗ₜ a :=
  gradedComm_tmul_of_zero _ _ _ _ _

theorem gradedComm_algebraMap_tmul [DirectSum.GSemiring 𝒜] [DirectSum.GAlgebra R 𝒜]
    (r : R) (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (algebraMap R _ r ⊗ₜ b) = b ⊗ₜ algebraMap R _ r :=
  gradedComm_of_zero_tmul _ _ _ _ _

theorem gradedComm_algebraMap [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ]
    [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ] (r : R) :
    gradedComm R 𝒜 ℬ (algebraMap R _ r) = algebraMap R _ r :=
  (gradedComm_algebraMap_tmul R 𝒜 ℬ r 1).trans (Algebra.TensorProduct.algebraMap_apply' r).symm

end gradedComm

variable [DirectSum.GRing 𝒜] [DirectSum.GRing ℬ]
variable [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ]

open TensorProduct (assoc map) in
/-- The multiplication operation for tensor products of externally `ι`-graded algebras. -/
noncomputable irreducible_def gradedMul :
    letI AB := DirectSum _ 𝒜 ⊗[R] DirectSum _ ℬ
    letI : Module R AB := TensorProduct.leftModule
    AB →ₗ[R] AB →ₗ[R] AB := by
  refine TensorProduct.curry ?_
  refine map (LinearMap.mul' R (⨁ i, 𝒜 i)) (LinearMap.mul' R (⨁ i, ℬ i)) ∘ₗ ?_
  refine (assoc R _ _ _).symm.toLinearMap ∘ₗ .lTensor _ ?_ ∘ₗ (assoc R _ _ _).toLinearMap
  refine (assoc R _ _ _).toLinearMap ∘ₗ .rTensor _ ?_ ∘ₗ (assoc R _ _ _).symm.toLinearMap
  exact (gradedComm _ _ _).toLinearMap

theorem tmul_of_gradedMul_of_tmul (j₁ i₂ : ι)
    (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) :
    gradedMul R 𝒜 ℬ (a₁ ⊗ₜ lof R _ ℬ j₁ b₁) (lof R _ 𝒜 i₂ a₂ ⊗ₜ b₂) =
      (-1 : ℤˣ) ^ (j₁ * i₂) • ((a₁ * lof R _ 𝒜 _ a₂) ⊗ₜ (lof R _ ℬ _ b₁ * b₂)) := by
  rw [gradedMul]
  dsimp only [curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_tmul,
    map_tmul, LinearMap.id_coe, id_eq, assoc_symm_tmul, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  rw [mul_comm j₁ i₂, gradedComm_of_tmul_of]
  -- the tower smul lemmas elaborate too slowly
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to avoid timeouts.
  rw [← smul_tmul', LinearEquiv.map_smul, tmul_smul, LinearEquiv.map_smul, map_smul]
  dsimp

variable {R}

set_option backward.defeqAttrib.useBackward true in
theorem algebraMap_gradedMul (r : R) (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ (algebraMap R _ r ⊗ₜ 1) x = r • x := by
  suffices gradedMul R 𝒜 ℬ (algebraMap R _ r ⊗ₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext ia a ib b
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [zero_mul, uzpow_zero, one_smul, smul_tmul']
  erw [one_mul, _root_.Algebra.smul_def]

theorem one_gradedMul (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ 1 x = x := by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using algebraMap_gradedMul 𝒜 ℬ 1 x

set_option backward.defeqAttrib.useBackward true in
theorem gradedMul_algebraMap (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) (r : R) :
    gradedMul R 𝒜 ℬ x (algebraMap R _ r ⊗ₜ 1) = r • x := by
  suffices (gradedMul R 𝒜 ℬ).flip (algebraMap R _ r ⊗ₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [mul_zero, uzpow_zero, one_smul, smul_tmul',
      mul_one, _root_.Algebra.smul_def, Algebra.commutes]
  rfl

theorem gradedMul_one (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ x 1 = x := by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using gradedMul_algebraMap 𝒜 ℬ x 1

set_option backward.isDefEq.respectTransparency false in
theorem gradedMul_assoc (x y z : DirectSum _ 𝒜 ⊗[R] DirectSum _ ℬ) :
    gradedMul R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y) z = gradedMul R 𝒜 ℬ x (gradedMul R 𝒜 ℬ y z) := by
  let mA := gradedMul R 𝒜 ℬ
    -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mA ∘ₗ mA =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mA.flip ∘ₗ mA).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext ixa xa ixb xb iya ya iyb yb iza za izb zb
  dsimp [mA]
  simp_rw [tmul_of_gradedMul_of_tmul, Units.smul_def, ← Int.cast_smul_eq_zsmul R,
    LinearMap.map_smul₂, map_smul, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, tmul_of_gradedMul_of_tmul, DirectSum.lof_eq_of, ← DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, mul_assoc]
  simp_rw [Int.cast_smul_eq_zsmul R, ← Units.smul_def, smul_smul, ← uzpow_add, add_mul, mul_add]
  congr 2
  abel

set_option backward.isDefEq.respectTransparency false in
theorem gradedComm_gradedMul (x y : DirectSum _ 𝒜 ⊗[R] DirectSum _ ℬ) :
    gradedComm R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y)
      = gradedMul R ℬ 𝒜 (gradedComm R 𝒜 ℬ x) (gradedComm R 𝒜 ℬ y) := by
  suffices (gradedMul R 𝒜 ℬ).compr₂ (gradedComm R 𝒜 ℬ).toLinearMap
      = (gradedMul R ℬ 𝒜 ∘ₗ (gradedComm R 𝒜 ℬ).toLinearMap).compl₂
        (gradedComm R 𝒜 ℬ).toLinearMap from
    LinearMap.congr_fun₂ this x y
  ext i₁ a₁ j₁ b₁ i₂ a₂ j₂ b₂
  dsimp
  rw [gradedComm_of_tmul_of, gradedComm_of_tmul_of, tmul_of_gradedMul_of_tmul]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to avoid timeouts.
  simp_rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul, map_smul,
    LinearMap.smul_apply]
  simp_rw [Int.cast_smul_eq_zsmul R, ← Units.smul_def, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, gradedComm_of_tmul_of, tmul_of_gradedMul_of_tmul, smul_smul,
    DirectSum.lof_eq_of, ← DirectSum.of_mul_of, ← DirectSum.lof_eq_of R]
  simp_rw [← uzpow_add, mul_add, add_mul, mul_comm i₁ j₂]
  congr 1
  abel_nf
  rw [two_nsmul, uzpow_add, uzpow_add, Int.units_mul_self, one_mul]

end TensorProduct
