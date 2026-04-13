/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Flat.Tensor

/-!

# Adic completion as tensor product

In this file we examine properties of the natural map

`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.

We show (in the `AdicCompletion` namespace):

- `ofTensorProduct_bijective_of_pi_of_fintype`: it is an isomorphism if `M = R^n`.
- `ofTensorProduct_surjective_of_finite`: it is surjective, if `M` is a finite `R`-module.
- `ofTensorProduct_bijective_of_finite_of_isNoetherian`: it is an isomorphism if `R` is Noetherian
  and `M` is a finite `R`-module.

As a corollary we obtain

- `flat_of_isNoetherian`: the adic completion of a Noetherian ring `R` is `R`-flat.

## TODO

- Show that `ofTensorProduct` is an isomorphism for any finite free `R`-module over an arbitrary
  ring. This is mostly composing with the isomorphism to `R^n` and checking that the diagram
  commutes.

-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

suppress_compilation

universe u v

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

open TensorProduct

namespace AdicCompletion

set_option backward.privateInPublic true in
private
def ofTensorProductBil : AdicCompletion I R →ₗ[AdicCompletion I R] M →ₗ[R] AdicCompletion I M where
  toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
  map_add' x y := by
    apply LinearMap.ext
    simp
  map_smul' r x := by
    apply LinearMap.ext
    simp

@[simp]
private lemma ofTensorProductBil_apply_apply (r : AdicCompletion I R) (x : M) :
    ((AdicCompletion.ofTensorProductBil I M) r) x = r • (of I M) x :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The natural `AdicCompletion I R`-linear map from `AdicCompletion I R ⊗[R] M` to
the adic completion of `M`. -/
def ofTensorProduct : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M :=
  TensorProduct.AlgebraTensorModule.lift (ofTensorProductBil I M)

@[simp]
lemma ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) :
    ofTensorProduct I M (r ⊗ₜ x) = r • of I M x := by
  simp [ofTensorProduct]

set_option backward.isDefEq.respectTransparency false in
variable {M} in
/-- `ofTensorProduct` is functorial in `M`. -/
lemma ofTensorProduct_naturality (f : M →ₗ[R] N) :
    map I f ∘ₗ ofTensorProduct I M =
      ofTensorProduct I N ∘ₗ AlgebraTensorModule.map LinearMap.id f := by
  ext
  simp

section PiFintype

/-
In this section we show that `ofTensorProduct` is an isomorphism if `M = R^n`.
-/

variable (ι : Type*)

section DecidableEq

variable [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
private lemma piEquivOfFintype_comp_ofTensorProduct_eq :
    piEquivOfFintype I (fun _ : ι ↦ R) ∘ₗ ofTensorProduct I (ι → R) =
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  ext i j k
  suffices h : (if j = i then 1 else 0) = (if j = i then 1 else 0 : AdicCompletion I R).val k by
    simpa [Pi.single_apply, -smul_eq_mul]
  split <;> simp

private lemma ofTensorProduct_eq :
    ofTensorProduct I (ι → R) = (piEquivOfFintype I (ι := ι) (fun _ : ι ↦ R)).symm.toLinearMap ∘ₗ
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  rw [← piEquivOfFintype_comp_ofTensorProduct_eq I ι, ← LinearMap.comp_assoc]
  simp

set_option backward.privateInPublic true in
/- If `M = R^ι` and `ι` is finite, we may construct an inverse to `ofTensorProduct I (ι → R)`. -/
private def ofTensorProductInvOfPiFintype :
    AdicCompletion I (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (ι → R) :=
  letI f := piEquivOfFintype I (fun _ : ι ↦ R)
  letI g := (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).symm
  f.trans g

set_option backward.privateInPublic true in
private lemma ofTensorProductInvOfPiFintype_comp_ofTensorProduct :
    ofTensorProductInvOfPiFintype I ι ∘ₗ ofTensorProduct I (ι → R) = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, LinearMap.comp_assoc, piEquivOfFintype_comp_ofTensorProduct_eq]
  simp

set_option backward.privateInPublic true in
private lemma ofTensorProduct_comp_ofTensorProductInvOfPiFintype :
    ofTensorProduct I (ι → R) ∘ₗ ofTensorProductInvOfPiFintype I ι = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, ofTensorProduct_eq, LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `ofTensorProduct` as an equiv in the case of `M = R^ι` where `ι` is finite. -/
def ofTensorProductEquivOfPiFintype :
    AdicCompletion I R ⊗[R] (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I (ι → R) :=
  LinearEquiv.ofLinear
    (ofTensorProduct I (ι → R))
    (ofTensorProductInvOfPiFintype I ι)
    (ofTensorProduct_comp_ofTensorProductInvOfPiFintype I ι)
    (ofTensorProductInvOfPiFintype_comp_ofTensorProduct I ι)

end DecidableEq

/-- If `M = R^ι`, `ofTensorProduct` is bijective. -/
lemma ofTensorProduct_bijective_of_pi_of_fintype [Finite ι] :
    Function.Bijective (ofTensorProduct I (ι → R)) := by
  classical
  cases nonempty_fintype ι
  exact EquivLike.bijective (ofTensorProductEquivOfPiFintype I ι)

end PiFintype

set_option backward.isDefEq.respectTransparency false in
/-- If `M` is a finite `R`-module, then the canonical map
`AdicCompletion I R ⊗[R] M →ₗ AdicCompletion I M` is surjective. -/
lemma ofTensorProduct_surjective_of_finite [Module.Finite R M] :
    Function.Surjective (ofTensorProduct I M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := map I p ∘ₗ ofTensorProduct I (Fin n → R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hf : Function.Surjective f := by
    simp only [hfg, LinearMap.coe_comp, g]
    apply Function.Surjective.comp
    · exact AdicCompletion.map_surjective I hp
    · exact (ofTensorProduct_bijective_of_pi_of_fintype I (Fin n)).surjective
  exact Function.Surjective.of_comp hf

section Noetherian

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-!

### Noetherian case

Suppose `R` is Noetherian. Then we show that the canonical map
`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M` is an isomorphism for every
finite `R`-module `M`.

The strategy is the following: Choose a surjection `f : (ι → R) →ₗ[R] M` and consider the following
commutative diagram:

```
 AdicCompletion I R ⊗[R] ker f -→ AdicCompletion I R ⊗[R] (ι → R) -→ AdicCompletion I R ⊗[R] M -→ 0
               |                             |                                 |                  |
               ↓                             ↓                                 ↓                  ↓
    AdicCompletion I (ker f) ------→ AdicCompletion I (ι → R) -------→ AdicCompletion I M ------→ 0
```

The vertical maps are given by `ofTensorProduct`. By the previous section we know that the second
vertical map is an isomorphism. Since `R` is Noetherian, `ker f` is finitely-generated, so again
by the previous section the first vertical map is surjective.

Moreover, both rows are exact by right-exactness of the tensor product and exactness of adic
completions over Noetherian rings. Hence we conclude by the 5-lemma.

-/

open CategoryTheory

section

variable {ι : Type} (f : (ι → R) →ₗ[R] M)

/- The first horizontal arrow in the top row. -/
private
def lTensorKerIncl : AdicCompletion I R ⊗[R] LinearMap.ker f →ₗ[AdicCompletion I R]
    AdicCompletion I R ⊗[R] (ι → R) :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.ker f).subtype

/- The second horizontal arrow in the top row. -/
private def lTensorf :
    AdicCompletion I R ⊗[R] (ι → R) →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] M :=
  AlgebraTensorModule.map LinearMap.id f

variable (hf : Function.Surjective f)

include hf

private lemma tens_exact : Function.Exact (lTensorKerIncl I M f) (lTensorf I M f) :=
  lTensor_exact (AdicCompletion I R) (f.exact_subtype_ker_map) hf

private lemma tens_surj : Function.Surjective (lTensorf I M f) :=
  LinearMap.lTensor_surjective (AdicCompletion I R) hf

private lemma adic_exact [IsNoetherianRing R] [Finite ι] :
    Function.Exact (map I (LinearMap.ker f).subtype) (map I f) :=
  map_exact (Submodule.injective_subtype _) (f.exact_subtype_ker_map) hf

private lemma adic_surj : Function.Surjective (map I f) :=
  map_surjective I hf

private
lemma ofTensorProduct_bijective_of_map_from_fin [Finite ι] [IsNoetherianRing R] :
    Function.Bijective (ofTensorProduct I M) :=
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (lTensorKerIncl I M f)
    (lTensorf I M f)
    (0 : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] Unit)
    (0 : _ →ₗ[AdicCompletion I R] Unit)
    (map I <| (LinearMap.ker f).subtype)
    (map I f)
    (0 : _ →ₗ[AdicCompletion I R] Unit)
    (0 : _ →ₗ[AdicCompletion I R] Unit)
    (ofTensorProduct I (LinearMap.ker f))
    (ofTensorProduct I (ι → R))
    (ofTensorProduct I M)
    0
    0
    (ofTensorProduct_naturality I <| (LinearMap.ker f).subtype)
    (ofTensorProduct_naturality I f)
    rfl
    rfl
    (tens_exact I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| tens_surj I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| Function.surjective_to_subsingleton _)
    (adic_exact I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| adic_surj I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| Function.surjective_to_subsingleton _)
    (ofTensorProduct_surjective_of_finite I (LinearMap.ker f))
    (ofTensorProduct_bijective_of_pi_of_fintype I ι)
    (Function.bijective_of_subsingleton _)
    (Function.injective_of_subsingleton _)

end

variable [IsNoetherianRing R]

/-- If `R` is a Noetherian ring and `M` is a finite `R`-module, then the natural map
given by `AdicCompletion.ofTensorProduct` is an isomorphism. -/
theorem ofTensorProduct_bijective_of_finite_of_isNoetherian
    [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ofTensorProduct_bijective_of_map_from_fin I M f hf

/-- `ofTensorProduct` packaged as linear equiv if `M` is a finite `R`-module and `R` is
Noetherian. -/
def ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_isNoetherian I M)

lemma coe_ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] :
    ofTensorProductEquivOfFiniteNoetherian I M = ofTensorProduct I M :=
  rfl

@[simp]
lemma ofTensorProductEquivOfFiniteNoetherian_apply [Module.Finite R M]
    (x : AdicCompletion I R ⊗[R] M) :
    ofTensorProductEquivOfFiniteNoetherian I M x = ofTensorProduct I M x :=
  rfl

@[simp]
lemma ofTensorProductEquivOfFiniteNoetherian_symm_of
    [Module.Finite R M] (x : M) :
    (ofTensorProductEquivOfFiniteNoetherian I M).symm ((of I M) x) = 1 ⊗ₜ x := by
  have h : (of I M) x = ofTensorProductEquivOfFiniteNoetherian I M (1 ⊗ₜ x) := by
    simp
  rw [h, LinearEquiv.symm_apply_apply]

section

variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
variable [Module.Finite R M] [Module.Finite R N]

set_option backward.isDefEq.respectTransparency false in
lemma tensor_map_id_left_eq_map :
    (AlgebraTensorModule.map LinearMap.id f) =
      (ofTensorProductEquivOfFiniteNoetherian I N).symm.toLinearMap ∘ₗ
      map I f ∘ₗ
      (ofTensorProductEquivOfFiniteNoetherian I M).toLinearMap := by
  rw [coe_ofTensorProductEquivOfFiniteNoetherian, ofTensorProduct_naturality I f]
  ext x
  simp

variable {f}

lemma tensor_map_id_left_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map LinearMap.id f :
        AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] N) := by
  rw [tensor_map_id_left_eq_map I f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact map_injective I hf

end

/-- Adic completion of a Noetherian ring `R` is flat over `R`. -/
instance flat_of_isNoetherian [IsNoetherianRing R] : Module.Flat R (AdicCompletion I R) :=
  Module.Flat.iff_lTensor_injective'.mpr fun J ↦
    tensor_map_id_left_injective_of_injective I (Submodule.injective_subtype J)

end Noetherian

end AdicCompletion
