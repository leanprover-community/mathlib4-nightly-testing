/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Properties of integration with respect to the Lebesgue measure -/
set_option backward.defeq.atInstanceTransparency false

public section


open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

section regionBetween

variable {α : Type*}
variable [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {s : Set α}

theorem volume_regionBetween_eq_integral' [SigmaFinite μ] (f_int : IntegrableOn f s μ)
    (g_int : IntegrableOn g s μ) (hs : MeasurableSet s) (hfg : f ≤ᵐ[μ.restrict s] g) :
    μ.prod volume (regionBetween f g s) = ENNReal.ofReal (∫ y in s, (g - f) y ∂μ) := by
  have h : g - f =ᵐ[μ.restrict s] fun x => Real.toNNReal (g x - f x) :=
    hfg.mono fun x hx => (Real.coe_toNNReal _ <| sub_nonneg.2 hx).symm
  rw [volume_regionBetween_eq_lintegral f_int.aemeasurable g_int.aemeasurable hs,
    integral_congr_ae h, lintegral_congr_ae,
    lintegral_coe_eq_integral _ ((integrable_congr h).mp (g_int.sub f_int))]
  dsimp only
  rfl

/-- If two functions are integrable on a measurable set, and one function is less than
or equal to the other on that set, then the volume of the region
between the two functions can be represented as an integral. -/
theorem volume_regionBetween_eq_integral [SigmaFinite μ] (f_int : IntegrableOn f s μ)
    (g_int : IntegrableOn g s μ) (hs : MeasurableSet s) (hfg : ∀ x ∈ s, f x ≤ g x) :
    μ.prod volume (regionBetween f g s) = ENNReal.ofReal (∫ y in s, (g - f) y ∂μ) :=
  volume_regionBetween_eq_integral' f_int g_int hs
    ((ae_restrict_iff' hs).mpr (Eventually.of_forall hfg))

end regionBetween

section SummableNormIcc

open ContinuousMap

/- The following lemma is a minor variation on `integrable_of_summable_norm_restrict` in
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`, but it is placed here because it needs to know
that `Icc a b` has volume `b - a`. -/
/-- If the sequence with `n`-th term the sup norm of `fun x ↦ f (x + n)` on the interval `Icc 0 1`,
for `n ∈ ℤ`, is summable, then `f` is integrable on `ℝ`. -/
theorem Real.integrable_of_summable_norm_Icc {E : Type*} [NormedAddCommGroup E] {f : C(ℝ, E)}
    (hf : Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict (Icc 0 1)‖) :
    Integrable f := by
  refine integrable_of_summable_norm_restrict (.of_nonneg_of_le
    (fun n : ℤ => mul_nonneg (norm_nonneg
      (f.restrict (⟨Icc (n : ℝ) ((n : ℝ) + 1), isCompact_Icc⟩ : Compacts ℝ)))
        ENNReal.toReal_nonneg) (fun n => ?_) hf) ?_
  · simp only [Compacts.coe_mk, le_add_iff_nonneg_right, zero_le_one, volume_real_Icc_of_le,
      add_sub_cancel_left, mul_one, norm_le _ (norm_nonneg _), ContinuousMap.restrict_apply]
    intro x
    have := ((f.comp <| ContinuousMap.addRight n).restrict (Icc 0 1)).norm_coe_le_norm
        ⟨x - n, ⟨sub_nonneg.mpr x.2.1, sub_le_iff_le_add'.mpr x.2.2⟩⟩
    simpa only [ContinuousMap.restrict_apply, comp_apply, coe_addRight, Subtype.coe_mk,
      sub_add_cancel] using this
  · exact iUnion_Icc_intCast ℝ

end SummableNormIcc

/-!
### Substituting `-x` for `x`

These lemmas are stated in terms of either `Iic` or `Ioi` (neglecting `Iio` and `Ici`) to match
mathlib's conventions for integrals over finite intervals (see `intervalIntegral`). For the case
of finite integrals, see `intervalIntegral.integral_comp_neg`.
-/


@[simp]
theorem integral_comp_neg_Iic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : ℝ → E) : (∫ x in Iic c, f (-x)) = ∫ x in Ioi (-c), f x := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have := MeasurableEmbedding.setIntegral_map (μ := volume) A f (Ici (-c))
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at this
  simp_rw [← integral_Ici_eq_integral_Ioi, this, neg_preimage, neg_Ici, neg_neg]

@[simp]
theorem integral_comp_neg_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : ℝ → E) : (∫ x in Ioi c, f (-x)) = ∫ x in Iic (-c), f x := by
  rw [← neg_neg c, ← integral_comp_neg_Iic]
  simp only [neg_neg]

theorem integral_comp_abs {f : ℝ → ℝ} :
    ∫ x, f |x| = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Iic_union_Ioi, restrict_univ]
      _ = 2 * ∫ x in Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose! hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]
