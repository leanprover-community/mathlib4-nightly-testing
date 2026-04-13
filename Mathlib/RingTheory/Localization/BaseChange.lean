/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definition

* `isLocalizedModule_iff_isBaseChange` : A localization of modules corresponds to a base change.
-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M →ₗ[R] M')

/-- The forward direction of `isLocalizedModule_iff_isBaseChange`. It is also used to prove the
other direction. -/
theorem IsLocalizedModule.isBaseChange [IsLocalizedModule S f] : IsBaseChange A f :=
  .of_lift_unique _ fun Q _ _ _ _ g ↦ by
    obtain ⟨ℓ, rfl, h₂⟩ := IsLocalizedModule.is_universal S f g fun s ↦ by
      rw [← (Algebra.lsmul R (A := A) R Q).commutes]; exact (IsLocalization.map_units A s).map _
    refine ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h ↦ ?_⟩
    cases h₂ (LinearMap.restrictScalars R g'') h; rfl

/-- The map `(f : M →ₗ[R] M')` is a localization of modules iff the map
`(Localization S) × M → N, (s, m) ↦ s • f m` is the tensor product (insomuch as it is the universal
bilinear map).
In particular, there is an isomorphism between `LocalizedModule S M` and `(Localization S) ⊗[R] M`
given by `m/s ↦ (1/s) ⊗ₜ m`.
-/
theorem isLocalizedModule_iff_isBaseChange : IsLocalizedModule S f ↔ IsBaseChange A f := by
  refine ⟨fun _ ↦ IsLocalizedModule.isBaseChange S A f, fun h ↦ ?_⟩
  letI : Module A (LocalizedModule S M) := LocalizedModule.moduleOfIsLocalization ..
  have : IsBaseChange A (LocalizedModule.mkLinearMap S M) := IsLocalizedModule.isBaseChange S A _
  let e := (this.equiv.symm.trans h.equiv).restrictScalars R
  convert IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M) e
  ext
  rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, IsBaseChange.equiv_symm_apply,
    IsBaseChange.equiv_tmul, one_smul]

open TensorProduct

variable (M) in
/-- The localization of an `R`-module `M` at a submonoid `S` is isomorphic to `S⁻¹R ⊗[R] M` as
an `S⁻¹R`-module. -/
noncomputable def LocalizedModule.equivTensorProduct :
    LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[R] M :=
  IsLocalizedModule.isBaseChange S (Localization S)
    (LocalizedModule.mkLinearMap S M) |>.equiv.symm

@[simp]
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul (x : M) (r : R) (s : S) :
    (equivTensorProduct S M).symm (Localization.mk r s ⊗ₜ[R] x) = r • mk x s := by
  simp [equivTensorProduct, IsBaseChange.equiv_tmul, mk_smul_mk, smul'_mk]

@[simp]
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul_one (x : M) :
    (equivTensorProduct S M).symm (1 ⊗ₜ[R] x) = mk x 1 := by
  simp [← Localization.mk_one]

@[simp]
lemma LocalizedModule.equivTensorProduct_apply_mk (x : M) (s : S) :
    equivTensorProduct S M (mk x s) = Localization.mk 1 s ⊗ₜ[R] x := by
  apply (equivTensorProduct S M).symm.injective
  simp

namespace IsLocalization

open TensorProduct Algebra.TensorProduct

instance tensorProduct_isLocalizedModule : IsLocalizedModule S (TensorProduct.mk R A M 1) :=
  (isLocalizedModule_iff_isBaseChange _ A _).mpr (TensorProduct.isBaseChange _ _ _)

variable (M₁ M₂ B C) [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  [Module A M₁] [Module A M₂] [IsScalarTower R A M₁] [IsScalarTower R A M₂]
  [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Semiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
include S

theorem tensorProduct_compatibleSMul : CompatibleSMul R A M₁ M₂ where
  smul_tmul a _ _ := by
    obtain ⟨r, s, rfl⟩ := exists_mk'_eq S a
    rw [← (map_units A s).smul_left_cancel]
    simp_rw [algebraMap_smul, smul_tmul', ← smul_assoc, smul_tmul, ← smul_assoc, smul_mk'_self,
      algebraMap_smul, smul_tmul]

instance [Module (Localization S) M₁] [Module (Localization S) M₂]
    [IsScalarTower R (Localization S) M₁] [IsScalarTower R (Localization S) M₂] :
    CompatibleSMul R (Localization S) M₁ M₂ :=
  tensorProduct_compatibleSMul S ..

instance (N N') [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N'] (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (TensorProduct.map f g) := by
  let eM := IsLocalizedModule.linearEquiv S f (TensorProduct.mk R (Localization S) M 1)
  let eN := IsLocalizedModule.linearEquiv S g (TensorProduct.mk R (Localization S) N 1)
  convert IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R (Localization S) (M ⊗[R] N) 1) <|
    (AlgebraTensorModule.distribBaseChange R (Localization S) ..).restrictScalars R ≪≫ₗ
    (congr eM eN ≪≫ₗ TensorProduct.equivOfCompatibleSMul ..).symm
  ext; congrm (?_ ⊗ₜ ?_) <;> simp [LinearEquiv.eq_symm_apply, eM, eN]

/-- If `A` is a localization of `R`, tensoring two `A`-modules over `A` is the same as
tensoring them over `R`. -/
noncomputable def moduleTensorEquiv : M₁ ⊗[A] M₂ ≃ₗ[A] M₁ ⊗[R] M₂ :=
  have := tensorProduct_compatibleSMul S A M₁ M₂
  equivOfCompatibleSMul R A A M₁ M₂

/-- If `A` is a localization of `R`, tensoring an `A`-module with `A` over `R` does nothing. -/
noncomputable def moduleLid : A ⊗[R] M₁ ≃ₗ[A] M₁ :=
  have := tensorProduct_compatibleSMul S A A M₁
  (equivOfCompatibleSMul R A A A M₁).symm ≪≫ₗ TensorProduct.lid _ _

/-- If `A` is a localization of `R`, tensoring two `A`-algebras over `A` is the same as
tensoring them over `R`. -/
noncomputable def algebraTensorEquiv : B ⊗[A] C ≃ₐ[A] B ⊗[R] C :=
  have := tensorProduct_compatibleSMul S A B C
  Algebra.TensorProduct.equivOfCompatibleSMul R A A B C

/-- If `A` is a localization of `R`, tensoring an `A`-algebra with `A` over `R` does nothing. -/
noncomputable def algebraLid : A ⊗[R] B ≃ₐ[A] B :=
  have := tensorProduct_compatibleSMul S A A B
  Algebra.TensorProduct.lidOfCompatibleSMul R A B

set_option linter.docPrime false in
theorem bijective_linearMap_mul' : Function.Bijective (LinearMap.mul' R A) :=
  have := tensorProduct_compatibleSMul S A A A
  (Algebra.TensorProduct.lmulEquiv R A).bijective

end IsLocalization

variable (T B : Type*) [CommSemiring T] [CommSemiring B]
  [Algebra R T] [Algebra T B] [Algebra R B] [Algebra A B] [IsScalarTower R T B]
  [IsScalarTower R A B]

variable {T B} in
lemma Algebra.isLocalization_iff_isPushout :
    IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B := by
  rw [Algebra.IsPushout.comm, Algebra.isPushout_iff, ← isLocalizedModule_iff_isLocalization]
  rw [← isLocalizedModule_iff_isBaseChange (S := S)]

lemma Algebra.isPushout_of_isLocalization [IsLocalization (Algebra.algebraMapSubmonoid T S) B] :
    Algebra.IsPushout R T A B :=
  (Algebra.isLocalization_iff_isPushout S _).mp inferInstance

variable (R M) in
open TensorProduct in
instance {α} [IsLocalizedModule S f] :
    IsLocalizedModule S (Finsupp.mapRange.linearMap (α := α) f) := by
  classical
  let e : Localization S ⊗[R] M ≃ₗ[R] M' :=
    (LocalizedModule.equivTensorProduct S M).symm.restrictScalars R ≪≫ₗ IsLocalizedModule.iso S f
  let e' : Localization S ⊗[R] (α →₀ M) ≃ₗ[R] (α →₀ M') :=
    finsuppRight R R (Localization S) M α ≪≫ₗ Finsupp.mapRange.linearEquiv e
  suffices IsLocalizedModule S (e'.symm.toLinearMap ∘ₗ Finsupp.mapRange.linearMap f) by
    convert this.of_linearEquiv (e := e')
    ext
    simp
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  convert TensorProduct.isBaseChange R (α →₀ M) (Localization S) using 1
  ext a m
  apply (finsuppRight R R (Localization S) M α).injective
  ext b
  apply e.injective
  suffices (if a = b then f m else 0) = e (1 ⊗ₜ[R] if a = b then m else 0) by
    simpa [e', Finsupp.single_apply, -EmbeddingLike.apply_eq_iff_eq, apply_ite]
  split_ifs with h
  · simp [e]
  · simp only [tmul_zero, map_zero]

open Finsupp in
theorem IsLocalizedModule.map_linearCombination {α : Type*} {v : α → M} [IsLocalizedModule S f] :
    map S (mapRange.linearMap (Algebra.linearMap R A)) f (linearCombination R v) =
      linearCombination A (f ∘ v) :=
  linearMap_ext (S := S) (mapRange.linearMap (Algebra.linearMap R A)) f <| by
    ext; simp [IsLocalizedModule.map_comp]

section

variable (S : Submonoid A) {N : Type*} [AddCommMonoid N] [Module R N]
variable [Module A M] [IsScalarTower R A M]

open TensorProduct

/-- `S⁻¹M ⊗[R] N = S⁻¹(M ⊗[R] N)`. -/
instance IsLocalizedModule.rTensor (g : M →ₗ[A] M') [h : IsLocalizedModule S g] :
    IsLocalizedModule S (AlgebraTensorModule.rTensor R N g) := by
  let Aₚ := Localization S
  letI : Module Aₚ M' := (IsLocalizedModule.iso S g).symm.toAddEquiv.module Aₚ
  haveI : IsScalarTower A Aₚ M' := (IsLocalizedModule.iso S g).symm.isScalarTower Aₚ
  haveI : IsScalarTower R Aₚ M' :=
    IsScalarTower.of_algebraMap_smul <| fun r x ↦ by simp [IsScalarTower.algebraMap_apply R A Aₚ]
  rw [isLocalizedModule_iff_isBaseChange (S := S) (A := Aₚ)] at h ⊢
  exact isBaseChange_tensorProduct_map _ h

variable {P : Type*} [AddCommMonoid P] [Module R P] (f : N →ₗ[R] P)

lemma IsLocalizedModule.map_lTensor (g : M →ₗ[A] M') [h : IsLocalizedModule S g] :
    IsLocalizedModule.map S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
      (AlgebraTensorModule.lTensor A M f) = AlgebraTensorModule.lTensor A M' f := by
  apply linearMap_ext S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
  rw [map_comp]
  ext
  simp

end

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (r : R) (A : Type*) [CommSemiring A] [Algebra R A]

instance IsLocalization.tensor (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) (S ⊗[R] A) := by
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

attribute [local instance] Algebra.TensorProduct.rightAlgebra
instance IsLocalization.tensorRight (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) (A ⊗[R] S) := by
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

open Algebra.TensorProduct in
lemma IsLocalization.tmul_mk' (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M) :
    s ⊗ₜ IsLocalization.mk' A x y =
      IsLocalization.mk' (S ⊗[R] A) (algebraMap R S x * s)
        ⟨algebraMap R S y.1, Algebra.mem_algebraMapSubmonoid_of_mem _⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_apply, Algebra.algebraMap_self,
    RingHomCompTriple.comp_apply, tmul_one_eq_one_tmul, tmul_mul_tmul, mul_one, mul_comm,
    IsLocalization.mk'_spec', algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← Algebra.smul_def, smul_tmul, Algebra.smul_def, mul_one]

open Algebra.TensorProduct in
lemma IsLocalization.mk'_tmul (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M) :
    IsLocalization.mk' A x y ⊗ₜ s =
      IsLocalization.mk' (A ⊗[R] S) (algebraMap R S x * s)
        ⟨algebraMap R S y.1, Algebra.mem_algebraMapSubmonoid_of_mem _⟩ := by
  simp [IsLocalization.eq_mk'_iff_mul_eq, map_mul,
    RingHom.algebraMap_toAlgebra]

variable (R S) {A} in
/-- `A[M⁻¹] ⊗[R] S` is the localization of `A ⊗[R] S` at `M`. -/
lemma IsLocalization.tensorProduct_tensorProduct (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization M B]
    [Algebra (A ⊗[R] S) (B ⊗[R] S)] [IsScalarTower A (A ⊗[R] S) (B ⊗[R] S)]
    (H : (algebraMap (A ⊗[R] S) (B ⊗[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] S) M) (B ⊗[R] S) :=
  (Algebra.isLocalization_iff_isPushout M _).mpr
    (Algebra.IsPushout.tensorProduct_tensorProduct R S A B H).symm

namespace IsLocalization.Away

instance tensor [IsLocalization.Away r A] :
    IsLocalization.Away (algebraMap R S r) (S ⊗[R] A) := by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

variable (S) in
/-- The `S`-isomorphism `S ⊗[R] Rᵣ ≃ₐ Sᵣ`. -/
noncomputable abbrev tensorEquiv [IsLocalization.Away r A] :
    S ⊗[R] A ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

attribute [local instance] Algebra.TensorProduct.rightAlgebra

instance tensorRight [IsLocalization.Away r A] :
    IsLocalization.Away (algebraMap R S r) (A ⊗[R] S) := by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

variable (S) in
/-- The `S`-isomorphism `S ⊗[R] Rᵣ ≃ₐ Sᵣ`. -/
noncomputable abbrev tensorRightEquiv [IsLocalization.Away r A] :
    A ⊗[R] S ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

end IsLocalization.Away

end
