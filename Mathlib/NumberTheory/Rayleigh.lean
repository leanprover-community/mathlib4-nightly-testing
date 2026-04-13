/-
Copyright (c) 2023 Jason Yuen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Yuen
-/
module

public import Mathlib.Data.Real.ConjExponents
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Rayleigh's theorem on Beatty sequences

This file proves Rayleigh's theorem on Beatty sequences. We start by proving `compl_beattySeq`,
which is a generalization of Rayleigh's theorem, and eventually prove
`Irrational.beattySeq_symmDiff_beattySeq_pos`, which is Rayleigh's theorem.

## Main definitions

* `beattySeq`: In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`.
* `beattySeq'`: In this variant of the Beatty sequence for `r`, the `k`th term is `⌈k * r⌉ - 1`.

## Main statements

Define the following Beatty sets, where `r` denotes a real number:

* `B_r := {⌊k * r⌋ | k ∈ ℤ}`
* `B'_r := {⌈k * r⌉ - 1 | k ∈ ℤ}`
* `B⁺_r := {⌊r⌋, ⌊2r⌋, ⌊3r⌋, ...}`
* `B⁺'_r := {⌈r⌉-1, ⌈2r⌉-1, ⌈3r⌉-1, ...}`

The main statements are:

* `compl_beattySeq`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then the complement of `B_r` is `B'_s`.
* `beattySeq_symmDiff_beattySeq'_pos`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then `B⁺_r` and `B⁺'_s` partition the positive integers.
* `Irrational.beattySeq_symmDiff_beattySeq_pos`: Let `r` be an irrational number greater than 1, and
  `1/r + 1/s = 1`. Then `B⁺_r` and `B⁺_s` partition the positive integers.

## References

* [Wikipedia, *Beatty sequence*](https://en.wikipedia.org/wiki/Beatty_sequence)

## Tags

beatty, sequence, rayleigh, irrational, floor, positive
-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

/-- In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`. -/
noncomputable def beattySeq (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌊k * r⌋

/-- In this variant of the Beatty sequence for `r`, the `k`th term is `⌈k * r⌉ - 1`. -/
noncomputable def beattySeq' (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌈k * r⌉ - 1

namespace Beatty

variable {r s : ℝ} {j : ℤ}

/-- Let `r > 1` and `1/r + 1/s = 1`. Then `B_r` and `B'_s` are disjoint (i.e. no collision exists).
-/
private theorem no_collision (hrs : r.HolderConjugate s) :
    Disjoint {beattySeq r k | k} {beattySeq' s k | k} := by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  rw [beattySeq, Int.floor_eq_iff, ← div_le_iff₀ hrs.pos, ← lt_div_iff₀ hrs.pos] at h₁
  rw [beattySeq', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel_right, ← div_lt_iff₀ hrs.symm.pos, ← le_div_iff₀ hrs.symm.pos] at h₂
  have h₃ := add_lt_add_of_le_of_lt h₁.1 h₂.1
  have h₄ := add_lt_add_of_lt_of_le h₁.2 h₂.2
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

/-- Let `r > 1` and `1/r + 1/s = 1`. Suppose there is an integer `j` where `B_r` and `B'_s` both
jump over `j` (i.e. an anti-collision). Then this leads to a contradiction. -/
private theorem no_anticollision (hrs : r.HolderConjugate s) :
    ¬∃ j k m : ℤ, k < j / r ∧ (j + 1) / r ≤ k + 1 ∧ m ≤ j / s ∧ (j + 1) / s < m + 1 := by
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₃ := add_lt_add_of_lt_of_le h₁₁ h₂₁
  have h₄ := add_lt_add_of_le_of_lt h₁₂ h₂₂
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one, ← add_assoc, add_lt_add_iff_right, add_right_comm] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

/-- Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B_r` or `B_r` jumps over `j`. -/
private theorem hit_or_miss (h : r > 0) :
    j ∈ {beattySeq r k | k} ∨ ∃ k : ℤ, k < j / r ∧ (j + 1) / r ≤ k + 1 := by
  -- for both cases, the candidate is `k = ⌈(j + 1) / r⌉ - 1`
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [Int.cast_sub, Int.cast_one, lt_div_iff₀ h, sub_add_cancel]
    exact ⟨‹_›, Int.le_ceil _⟩
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySeq, Int.floor_eq_iff, Int.cast_sub, Int.cast_one, ← lt_div_iff₀ h, sub_lt_iff_lt_add]
    exact ⟨‹_›, Int.ceil_lt_add_one _⟩

/-- Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B'_r` or `B'_r` jumps over `j`. -/
private theorem hit_or_miss' (h : r > 0) :
    j ∈ {beattySeq' r k | k} ∨ ∃ k : ℤ, k ≤ j / r ∧ (j + 1) / r < k + 1 := by
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · exact Or.inr ⟨⌊(j + 1) / r⌋, (le_div_iff₀ h).2 ‹_›, Int.lt_floor_add_one _⟩
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySeq', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one]
    constructor
    · rwa [add_sub_cancel_right]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : ℝ) h)

end Beatty

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1, and `1/r + 1/s = 1`. Then the complement of `B_r` is `B'_s`. -/
theorem compl_beattySeq {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq r k | k}ᶜ = {beattySeq' s k | k} := by
  ext j
  by_cases h₁ : j ∈ {beattySeq r k | k} <;> by_cases h₂ : j ∈ {beattySeq' s k | k}
  · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hrs)).elim
  · simp only [Set.mem_compl_iff, h₁, h₂, not_true_eq_false]
  · simp only [Set.mem_compl_iff, h₁, h₂, not_false_eq_true]
  · have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hrs.pos).resolve_left h₁
    have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hrs.symm.pos).resolve_left h₂
    exact (Beatty.no_anticollision hrs ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim

theorem compl_beattySeq' {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq' r k | k}ᶜ = {beattySeq s k | k} := by
  rw [← compl_beattySeq hrs.symm, compl_compl]

open scoped symmDiff

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1, and `1/r + 1/s = 1`. Then `B⁺_r` and `B⁺'_s` partition the positive integers. -/
theorem beattySeq_symmDiff_beattySeq'_pos {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq r k | k > 0} ∆ {beattySeq' s k | k > 0} = {n | 0 < n} := by
  apply Set.eq_of_subset_of_subset
  · rintro j (⟨⟨k, hk, hjk⟩, -⟩ | ⟨⟨k, hk, hjk⟩, -⟩)
    · rw [Set.mem_setOf_eq, ← hjk, beattySeq, Int.floor_pos]
      exact one_le_mul_of_one_le_of_one_le (by norm_cast) hrs.lt.le
    · rw [Set.mem_setOf_eq, ← hjk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one]
      exact one_lt_mul_of_le_of_lt (by norm_cast) hrs.symm.lt
  intro j (hj : 0 < j)
  have hb₁ : ∀ s ≥ 0, j ∈ {beattySeq s k | k > 0} ↔ j ∈ {beattySeq s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySeq, Int.floor_pos] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans_le hj) hs
  have hb₂ : ∀ s ≥ 0, j ∈ {beattySeq' s k | k > 0} ↔ j ∈ {beattySeq' s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans hj) hs
  rw [Set.mem_symmDiff, hb₁ _ hrs.nonneg, hb₂ _ hrs.symm.nonneg, ← compl_beattySeq hrs,
    Set.notMem_compl_iff, Set.mem_compl_iff, and_self, and_self]
  exact or_not

theorem beattySeq'_symmDiff_beattySeq_pos {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq' r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [symmDiff_comm, beattySeq_symmDiff_beattySeq'_pos hrs.symm]

/-- Let `r` be an irrational number. Then `B⁺_r` and `B⁺'_r` are equal. -/
theorem Irrational.beattySeq'_pos_eq {r : ℝ} (hr : Irrational r) :
    {beattySeq' r k | k > 0} = {beattySeq r k | k > 0} := by
  dsimp only [beattySeq, beattySeq']
  congr! 4; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
  rw [sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel_right]
  refine ⟨(Int.floor_le _).lt_of_ne fun h ↦ ?_, (Int.lt_floor_add_one _).le⟩
  exact (hr.intCast_mul hk.ne').ne_int ⌊k * r⌋ h.symm

/-- **Rayleigh's theorem** on Beatty sequences. Let `r` be an irrational number greater than 1, and
`1/r + 1/s = 1`. Then `B⁺_r` and `B⁺_s` partition the positive integers. -/
theorem Irrational.beattySeq_symmDiff_beattySeq_pos {r s : ℝ}
    (hrs : r.HolderConjugate s) (hr : Irrational r) :
    {beattySeq r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [← hr.beattySeq'_pos_eq, beattySeq'_symmDiff_beattySeq_pos hrs]
