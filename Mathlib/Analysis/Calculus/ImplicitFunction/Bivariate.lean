/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Implicit function theorem — curried bivariate

This specialization of the implicit function theorem applies to a curried bivariate function
`f : E₁ → E₂ → F` and assumes continuity of both its partial derivatives at `u : E₁ × E₂` as well as
invertibility of `f₂ u.1 u.2 : E₂ →L[𝕜] F` its partial derivative with respect to the second
argument.

It proves the existence of `ψ : E₁ → E₂` such that for `v` in a neighbourhood of `u` we have
`f v.1 v.2 = f u.1 u.2 ↔ ψ v.1 = v.2`. This is `implicitFunctionOfBivariate`. A formula for its
first derivative follows.

A similar specialization is made to an uncurried bivariate function by
`HasStrictFDerivAt.implicitFunctionOfProdDomain` in a sister file.

## Tags

implicit function
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

variable {u : E₁ × E₂}
  {f : E₁ → E₂ → F} {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} {f₂ : E₁ → E₂ → E₂ →L[𝕜] F}
  (df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
  (df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
  (cf₁ : ContinuousAt ↿f₁ u) (cf₂ : ContinuousAt ↿f₂ u) (if₂u : (f₂ u.1 u.2).IsInvertible)

set_option backward.simpa.using.reducibleClose false in
/-- Implicit function `ψ : E₁ → E₂` associated with the (curried) bivariate function
`f : E₁ → E₂ → F` at `u : E₁ × E₂`. -/
noncomputable def implicitFunctionOfBivariate : E₁ → E₂ :=
  HasStrictFDerivAt.implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using if₂u)

set_option backward.simpa.using.reducibleClose false in
theorem implicitFunctionOfBivariate_def :
    implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u =
      HasStrictFDerivAt.implicitFunctionOfProdDomain
        (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using if₂u) := by
  rfl

set_option backward.simpa.using.reducibleClose false in
theorem tendsto_implicitFunctionOfBivariate :
    Tendsto (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u) (𝓝 u.1) (𝓝 u.2) := by
  simpa using HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using if₂u)

set_option backward.simpa.using.reducibleClose false in
theorem eventually_apply_implicitFunctionOfBivariate :
    ∀ᶠ x in 𝓝 u.1, f x (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u x) = f u.1 u.2 := by
  simpa using HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using if₂u)

set_option backward.simpa.using.reducibleClose false in
theorem eventually_apply_eq_iff_implicitFunctionOfBivariate :
    ∀ᶠ v in 𝓝 u,
      f v.1 v.2 = f u.1 u.2 ↔ implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u v.1 = v.2 := by
  simpa using HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using if₂u)

set_option backward.simpa.using.reducibleClose false in
theorem hasStrictFDerivAt_implicitFunctionOfBivariate :
    HasStrictFDerivAt (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u)
      (-(f₂ u.1 u.2).inverse ∘L f₁ u.1 u.2) u.1 := by
  simpa using HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using if₂u)

end
