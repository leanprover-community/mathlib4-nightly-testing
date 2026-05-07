/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Exponential in a Banach algebra

In this file, we define `NormedSpace.exp : 𝔸 → 𝔸`,
the exponential map in a topological algebra `𝔸`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `NormedSpace.exp` independent of a particular choice of norm. The
definition also does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `Real.exp` and `Complex.exp` can be found in
`Analysis.SpecialFunctions.Exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `NormedSpace.exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero,
  then given two commuting elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given two elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring,
  then given an element `x` in the disk of convergence,
  we have `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `expSeries_radius_eq_top` : the `FormalMultilinearSeries` defining `NormedSpace.exp`
  has infinite radius of convergence
- `NormedSpace.exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add` : if `𝔸` is commutative, then we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)` for any `x` and `y`
- `NormedSpace.exp_neg` : if `𝔸` is a division ring, then we have
  `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.
- `NormedSpace.exp_sum_of_commute` : the analogous result to `NormedSpace.exp_add_of_commute`
  for `Finset.sum`.
- `NormedSpace.exp_sum` : the analogous result to `NormedSpace.exp_add` for `Finset.sum`.
- `NormedSpace.exp_nsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.
- `NormedSpace.exp_zsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.

### Notes

We put nearly all the statements in this file in the `NormedSpace` namespace,
to avoid collisions with the `Real` or `Complex` namespaces.

As of 2023-11-16 due to bad instances in Mathlib
```
import Mathlib

open Real

#time example (x : ℝ) : 0 < exp x      := exp_pos _ -- 250ms
#time example (x : ℝ) : 0 < Real.exp x := exp_pos _ -- 2ms
```
This is because `exp x` tries the `NormedSpace.exp 𝕂 : 𝔸 → 𝔸` function previously defined here,
and generates a slow coercion search from `Real` to `Type`, to fit the first argument here.
We will resolve this slow coercion separately,
but we want to move `exp` out of the root namespace in any case to avoid this ambiguity.

To avoid explicitly passing the base field `𝕂`, we currently fix `𝕂 = ℚ` in the definition of
`NormedSpace.exp : 𝔸 → 𝔸`. If `𝔸` can be equipped with a `ℚ`-algebra structure, we use
`Classical.choice` to pick the unique `Algebra ℚ 𝔸` instead of requiring an instance argument.
This eliminates the need to provide `Algebra ℚ 𝔸` every time `exp` is used. If `𝔸` can't be equipped
with a `ℚ`-algebra structure, we use the junk value `1`.

In the long term it may be possible to replace `Real.exp` and `Complex.exp` with `NormedSpace.exp`
and move it back to the root namespace.
-/

@[expose] public section


namespace NormedSpace

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries

open scoped Nat Topology ENNReal Ring

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- `expSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `NormedSpace.exp : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/-- The exponential series as an `ofScalars` series. -/
theorem expSeries_eq_ofScalars : expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n ↦ (n !⁻¹ : 𝕂) := by
  simp_rw [FormalMultilinearSeries.ext_iff, expSeries, ofScalars, implies_true]

variable {𝕂 𝔸}

open scoped Classical in
/-- `NormedSpace.exp : 𝔸 → 𝔸` is the exponential map. It is defined as the sum of the
`FormalMultilinearSeries` `expSeries ℚ 𝔸`.

If `𝔸` can't be equipped with a `ℚ`-algebra structure, we use the junk value `1`. For details on why
this approach is taken, see the module documentation for
`Mathlib/Analysis/Normed/Algebra/Exponential.lean`.

Note that when `𝔸 = Matrix n n 𝕂`, this is the **Matrix Exponential**; see
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` for lemmas
specific to that case. -/
noncomputable irreducible_def exp (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra ℚ 𝔸) then
    letI _ := h.some
    (NormedSpace.expSeries ℚ 𝔸).sum x
  else
    1

/-- The junk value when `𝔸` can't be equipped with a `ℚ`-algebra structure. -/
@[simp]
theorem exp_of_isEmpty_algebra_rat [IsEmpty (Algebra ℚ 𝔸)] (x : 𝔸) : exp x = 1 := by
  rw [exp, dif_neg (not_nonempty_iff.mpr ‹_›)]

theorem expSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n := by simp [expSeries]

theorem expSeries_apply_eq' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  funext (expSeries_apply_eq x)

theorem expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  tsum_congr fun n => expSeries_apply_eq x n

theorem expSeries_sum_eq_rat [Algebra ℚ 𝔸] : (expSeries 𝕂 𝔸).sum = (expSeries ℚ 𝔸).sum := by
  ext; simp_rw [expSeries_sum_eq, inv_natCast_smul_eq 𝕂 ℚ]

theorem expSeries_eq_expSeries_rat [Algebra ℚ 𝔸] (n : ℕ) :
    ⇑(expSeries 𝕂 𝔸 n) = expSeries ℚ 𝔸 n := by
  ext c
  simp [expSeries, inv_natCast_smul_eq 𝕂 ℚ]

variable (𝕂) in
theorem exp_eq_expSeries_sum [CharZero 𝕂] : exp = (expSeries 𝕂 𝔸).sum := by
  ext x
  rw [exp, dif_pos ⟨RestrictScalars.algebra ℚ 𝕂 𝔸⟩, ← @expSeries_sum_eq_rat (𝕂 := 𝕂)]

variable (𝕂) in
theorem exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n := by
  rw [exp_eq_expSeries_sum 𝕂]
  ext x
  exact expSeries_sum_eq x

theorem exp_eq_tsum_rat [Algebra ℚ 𝔸] : exp = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : ℚ) • x ^ n :=
  exp_eq_tsum ℚ

variable (𝕂) in
/-- The exponential sum as an `ofScalarsSum`. -/
theorem exp_eq_ofScalarsSum [CharZero 𝕂] :
    exp = ofScalarsSum (E := 𝔸) fun n ↦ (n !⁻¹ : 𝕂) := by
  rw [exp_eq_tsum 𝕂, ofScalarsSum_eq_tsum]

theorem expSeries_apply_zero (n : ℕ) :
    expSeries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [expSeries_apply_eq]
  rcases n with - | n
  · simp
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]

@[simp]
theorem exp_zero : exp (0 : 𝔸) = 1 := by
  rw [exp]
  split_ifs
  · simp_rw [expSeries_sum_eq, ← expSeries_apply_eq, expSeries_apply_zero, tsum_pi_single]
  · rfl

@[simp]
theorem exp_op [T2Space 𝔸] (x : 𝔸) :
    exp (MulOpposite.op x) = MulOpposite.op (exp x) := by
  obtain h | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · have : IsEmpty (Algebra ℚ 𝔸ᵐᵒᵖ) := ⟨fun _ => h.elim <| (RingEquiv.opOp 𝔸).algebra ℚ⟩
    simp
  · rw [exp_eq_tsum ℚ, exp_eq_tsum ℚ]
    simp_rw [← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
theorem exp_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    exp (MulOpposite.unop x) = MulOpposite.unop (exp x) := by
  induction x; simp

theorem star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (exp x) = exp (star x) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · simp_rw [exp_eq_tsum ℚ, ← star_pow, ← star_inv_natCast_smul, ← tsum_star]

/-- A subalgebra of `𝔸` that is closed topologically and under `ℚ`-scaling is closed under `exp`. -/
theorem exp_mem
    {R S : Type*} [Monoid R] [SMul ℚ R] [MulAction R 𝔸] [Algebra ℚ 𝔸] [IsScalarTower ℚ R 𝔸]
    [SetLike S 𝔸] [SubsemiringClass S 𝔸] [SMulMemClass S R 𝔸] {s : S}
    (h_closed : IsClosed (s : Set 𝔸)) {x : 𝔸} (h : x ∈ s) :
    exp x ∈ s := by
  have := SMulMemClass.ofIsScalarTower S ℚ R 𝔸
  rw [exp_eq_tsum ℚ]
  exact tsum_mem h_closed fun i => SMulMemClass.smul_mem _ <| pow_mem h _

variable (𝕂)

@[aesop safe apply]
theorem _root_.IsSelfAdjoint.exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : IsSelfAdjoint x) : IsSelfAdjoint (exp x) :=
  (star_exp x).trans <| h.symm ▸ rfl

theorem _root_.Commute.exp_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (exp y) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · rw [exp_eq_tsum ℚ]
    exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

theorem _root_.Commute.exp_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) y :=
  h.symm.exp_right.symm

theorem _root_.Commute.exp [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) (exp y) :=
  h.exp_left.exp_right

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type*} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

theorem expSeries_apply_eq_div (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv, ← (Nat.cast_commute n ! (x ^ n)).inv_left₀.eq, ← smul_eq_mul,
    expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝔸]

theorem expSeries_apply_eq_div' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (expSeries_apply_eq_div x)

theorem expSeries_sum_eq_div (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, x ^ n / n ! :=
  tsum_congr (expSeries_apply_eq_div x)

theorem exp_eq_tsum_div [CharZero 𝔸] : exp = fun x : 𝔸 => ∑' n : ℕ, x ^ n / n ! := by
  rw [exp_eq_expSeries_sum ℚ]
  ext x
  exact expSeries_sum_eq_div x

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type*} [NontriviallyNormedField 𝕂]
variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸]

theorem norm_expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx

theorem norm_expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  exact norm_expSeries_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable_of_mem_ball x hx).of_norm

theorem expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable_of_mem_ball' x hx).of_norm

theorem expSeries_hasSum_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) := by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx

theorem expSeries_hasSum_exp_of_mem_ball' [CharZero 𝕂] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) := by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx

theorem hasFPowerSeriesOnBall_exp_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius := by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    (expSeries 𝕂 𝔸).hasFPowerSeriesOnBall h

theorem hasFPowerSeriesAt_exp_zero_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 := by
  simpa only [exp, expSeries_sum_eq_rat] using
    (hasFPowerSeriesOnBall_exp_of_radius_pos h).hasFPowerSeriesAt

theorem continuousOn_exp [CharZero 𝕂] :
    ContinuousOn (exp : 𝔸 → 𝔸) (Metric.eball 0 (expSeries 𝕂 𝔸).radius) := by
  have := FormalMultilinearSeries.continuousOn (p := expSeries 𝕂 𝔸)
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using this

theorem analyticAt_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : AnalyticAt 𝕂 exp x := by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then
`NormedSpace.exp (x + y) = (NormedSpace.exp x) * (NormedSpace.exp y)`. -/
theorem exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y := by
  rw [exp_eq_tsum 𝕂,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _, Finset.smul_sum]
  refine tsum_congr fun n => Finset.sum_congr rfl fun kl hkl => ?_
  rw [← Nat.cast_smul_eq_nsmul 𝕂, smul_smul, smul_mul_smul_comm, ← Finset.mem_antidiagonal.mp hkl,
    Nat.cast_add_choose, Finset.mem_antidiagonal.mp hkl]
  field_simp [n.factorial_ne_zero]

/-- `NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`. -/
@[implicit_reducible]
noncomputable def invertibleExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Invertible (exp x)
    where
  invOf := exp (-x)
  invOf_mul_self := by
    have hnx : -x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx,
      neg_add_cancel, exp_zero]
  mul_invOf_self := by
    have hnx : -x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_right <| Commute.refl x) hx hnx,
      add_neg_cancel, exp_zero]

theorem isUnit_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : IsUnit (exp x) :=
  @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall hx)

theorem invOf_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) [Invertible (exp x)] :
    ⅟(exp x) = exp (-x) := by
  letI := invertibleExpOfMemBall hx; convert (rfl : ⅟(exp x) = _)

/-- Any continuous ring homomorphism commutes with `NormedSpace.exp`. -/
theorem map_exp_of_mem_ball [Algebra 𝕂 𝔹] [CharZero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹]
    (f : F) (hf : Continuous f) (x : 𝔸) (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    f (exp x) = exp (f x) := by
  rw [exp_eq_tsum 𝕂, exp_eq_tsum 𝕂]
  refine ((expSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  simp_rw [map_inv_natCast_smul f 𝕂 𝕂, map_pow]

end CompleteAlgebra

theorem algebraMap_exp_comm_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
  map_exp_of_mem_ball (algebraMap _ _) (algebraMapCLM _ _).continuous _ hx

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)

theorem norm_expSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖x ^ n / (n !)‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact norm_expSeries_summable_of_mem_ball x hx

theorem expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm

theorem expSeries_div_hasSum_exp_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => x ^ n / n !) (exp x) := by
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact expSeries_hasSum_exp_of_mem_ball x hx

theorem exp_neg_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (-x) = (exp x)⁻¹ :=
  letI := invertibleExpOfMemBall hx
  invOf_eq_inv (exp x)

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section AnyAlgebra

variable (𝕂 𝔸 : Type*) [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
variable [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem expSeries_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ := by
  have {n : ℕ} : (Nat.factorial n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply expSeries_eq_ofScalars 𝕂 𝔸 ▸
    ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall fun n => ?_)
  · simp_rw [← norm_div, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_div_right_comm,
      inv_div_inv, norm_mul, div_self this, norm_one, one_mul]
    apply norm_zero (E := 𝕂) ▸ Filter.Tendsto.norm
    apply (Filter.tendsto_add_atTop_iff_nat (f := fun n => (n : 𝕂)⁻¹) 1).mpr
    exact tendsto_inv_atTop_nhds_zero_nat
  · simp [this]

theorem expSeries_radius_pos : 0 < (expSeries 𝕂 𝔸).radius := by
  rw [expSeries_radius_eq_top]
  exact WithTop.top_pos

variable {𝕂 𝔸}

theorem norm_expSeries_summable (x : 𝔸) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_expSeries_summable' (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  norm_expSeries_summable_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem algebraMap_exp_comm [CompleteSpace 𝕂] (x : 𝕂) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
  algebraMap_exp_comm_of_mem_ball x <| (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _

variable [CompleteSpace 𝔸]

theorem expSeries_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable x).of_norm

theorem expSeries_summable' (x : 𝔸) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable' x).of_norm

theorem expSeries_hasSum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_hasSum_exp' (x : 𝔸) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞ :=
  expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFPowerSeriesOnBall_exp_of_radius_pos (expSeries_radius_pos _ _)

theorem exp_hasFPowerSeriesAt_zero : HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 :=
  exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt

theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 exp x :=
  analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end AnyAlgebra

section Rat
variable {𝔸 𝔹 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormedRing 𝔹]

@[continuity, fun_prop]
theorem exp_continuous : Continuous (exp : 𝔸 → 𝔸) := by
  rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ←
    expSeries_radius_eq_top ℚ 𝔸]
  exact continuousOn_exp

open Topology in
lemma _root_.Filter.Tendsto.exp {α : Type*} {l : Filter α} {f : α → 𝔸} {a : 𝔸}
    (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp a)) :=
  (exp_continuous.tendsto _).comp hf

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`. -/
theorem exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball hxy ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)

/-- `NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`. -/
@[implicit_reducible]
noncomputable def invertibleExp (x : 𝔸) : Invertible (exp x) :=
  invertibleExpOfMemBall <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _

theorem isUnit_exp (x : 𝔸) : IsUnit (exp x) :=
  isUnit_exp_of_mem_ball <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _

theorem invOf_exp (x : 𝔸) [Invertible (exp x)] : ⅟(exp x) = exp (-x) :=
  invOf_exp_of_mem_ball <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _

theorem _root_.Ring.inverse_exp (x : 𝔸) : (exp x)⁻¹ʳ = exp (-x) :=
  letI := invertibleExp x
  Ring.inverse_invertible _

theorem exp_mem_unitary_of_mem_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : x ∈ skewAdjoint 𝔸) : exp x ∈ unitary 𝔸 := by
  rw [Unitary.mem_iff, star_exp, skewAdjoint.mem_iff.mp h, ←
    exp_add_of_commute (Commute.refl x).neg_left, ← exp_add_of_commute (Commute.refl x).neg_right,
    neg_add_cancel, add_neg_cancel, exp_zero, and_self_iff]

set_option backward.isDefEq.respectTransparency false in
open scoped Function in -- required for scoped `on` notation
/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `NormedSpace.exp (∑ i, f i) = ∏ i, NormedSpace.exp (f i)`. -/
theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp (f i)) fun _ hi _ hj _ => (h.of_refl hi hj).exp := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.sum_insert ha, exp_add_of_commute,
      ih (h.mono <| Finset.subset_insert _ _)]
    refine Commute.sum_right _ _ _ fun i hi => ?_
    exact h.of_refl (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)

theorem exp_nsmul (n : ℕ) (x : 𝔸) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, exp_add_of_commute ((Commute.refl x).smul_left n), ih]

/-- Any continuous ring homomorphism commutes with `NormedSpace.exp`. -/
theorem map_exp [Algebra ℚ 𝔹]
    {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) :
    f (exp x) = exp (f x) :=
  map_exp_of_mem_ball f hf x <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _

theorem exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] (g : G) (x : 𝔸) :
    exp (g • x) = g • exp x :=
  (map_exp (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul g) x).symm

theorem exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹ :=
  exp_smul (ConjAct.toConjAct y) x

theorem exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp (↑y⁻¹ * x * y) = ↑y⁻¹ * exp x * y :=
  exp_units_conj _ _

@[simp]
theorem _root_.Prod.fst_exp [NormedAlgebra ℚ 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).fst = exp x.fst :=
  map_exp (RingHom.fst 𝔸 𝔹) continuous_fst x

@[simp]
theorem _root_.Prod.snd_exp [NormedAlgebra ℚ 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).snd = exp x.snd :=
  map_exp (RingHom.snd 𝔸 𝔹) continuous_snd x

@[simp]
theorem _root_.Pi.coe_exp {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra ℚ (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) (i : ι) :
    exp x i = exp (x i) :=
  let ⟨_⟩ := nonempty_fintype ι
  map_exp (Pi.evalRingHom 𝔸 i) (continuous_apply _) x

theorem _root_.Pi.exp_def {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra ℚ (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) :
    exp x = fun i => exp (x i) :=
  funext <| Pi.coe_exp x

theorem _root_.Function.update_exp {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [DecidableEq ι]
    [∀ i, NormedRing (𝔸 i)] [∀ i, NormedAlgebra ℚ (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i)
    (j : ι) (xj : 𝔸 j) :
    Function.update (exp x) j (exp xj) = exp (Function.update x j xj) := by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp) x j xj i).symm

end Rat

section DivisionAlgebra

variable {𝔸 : Type*} [NormedDivisionRing 𝔸] [NormedAlgebra ℚ 𝔸]

theorem norm_expSeries_div_summable (x : 𝔸) : Summable fun n => ‖(x ^ n / n ! : 𝔸)‖ :=
  norm_expSeries_div_summable_of_mem_ball ℚ x
    ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)

variable [CompleteSpace 𝔸]

theorem expSeries_div_summable (x : 𝔸) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable x).of_norm

theorem expSeries_div_hasSum_exp (x : 𝔸) : HasSum (fun n => x ^ n / n !) (exp x) :=
  expSeries_div_hasSum_exp_of_mem_ball ℚ x ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_neg (x : 𝔸) : exp (-x) = (exp x)⁻¹ :=
  exp_neg_of_mem_ball ℚ <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _

theorem exp_zsmul (z : ℤ) (x : 𝔸) : exp (z • x) = exp x ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · rw [zpow_neg, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]

theorem exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp (y * x * y⁻¹) = y * exp x * y⁻¹ :=
  exp_units_conj (Units.mk0 y hy) x

theorem exp_conj' (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp (y⁻¹ * x * y) = y⁻¹ * exp x * y :=
  exp_units_conj' (Units.mk0 y hy) x

end DivisionAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`. -/
theorem exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y :=
  exp_add_of_mem_ball ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)

/-- A version of `NormedSpace.exp_sum_of_commute` for a commutative Banach-algebra. -/
theorem exp_sum {ι} (s : Finset ι) (f : ι → 𝔸) : exp (∑ i ∈ s, f i) = ∏ i ∈ s, exp (f i) := by
  rw [exp_sum_of_commute, Finset.noncommProd_eq_prod]
  exact fun i _hi j _hj _ => Commute.all _ _

end CommAlgebra

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type*) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`expSeries` on `𝔸`. -/
theorem expSeries_eq_expSeries (n : ℕ) (x : 𝔸) :
    (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries_apply_eq, expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝕂']

/-- A version of `Complex.ofReal_exp` for `NormedSpace.exp` instead of `Complex.exp` -/
@[simp, norm_cast]
theorem ofReal_exp_ℝ_ℝ (r : ℝ) : ↑(exp r) = exp (r : ℂ) :=
  map_exp (algebraMap ℝ ℂ) (continuous_algebraMap _ _) r

@[deprecated (since := "2025-11-13")] alias of_real_exp_ℝ_ℝ := ofReal_exp_ℝ_ℝ

end ScalarTower

end NormedSpace
