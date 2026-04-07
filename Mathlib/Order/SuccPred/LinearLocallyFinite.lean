/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Linear locally finite orders

We prove that a `LinearOrder` which is a `LocallyFiniteOrder` also verifies
* `SuccOrder`
* `PredOrder`
* `IsSuccArchimedean`
* `IsPredArchimedean`
* `Countable`

Furthermore, we show that there is an `OrderIso` between such an order and a subset of `ℤ`.

## Main definitions

* `toZ i0 i`: in a linear order on which we can define predecessors and successors and which is
  succ-archimedean, we can assign a unique integer `toZ i0 i` to each element `i : ι` while
  respecting the order, starting from `toZ i0 i0 = 0`.

## Main results

Results about linear locally finite orders:
* `LinearLocallyFiniteOrder.SuccOrder`: a linear locally finite order has a successor function.
* `LinearLocallyFiniteOrder.PredOrder`: a linear locally finite order has a predecessor
  function.
* `LinearLocallyFiniteOrder.isSuccArchimedean`: a linear locally finite order is
  succ-archimedean.
* `LinearOrder.pred_archimedean_of_succ_archimedean`: a succ-archimedean linear order is also
  pred-archimedean.
* `countable_of_linear_succ_pred_arch` : a succ-archimedean linear order is countable.

About `toZ`:
* `orderIsoRangeToZOfLinearSuccPredArch`: `toZ` defines an `OrderIso` between `ι` and its
  range.
* `orderIsoNatOfLinearSuccPredArch`: if the order has a bot but no top, `toZ` defines an
  `OrderIso` between `ι` and `ℕ`.
* `orderIsoIntOfLinearSuccPredArch`: if the order has neither bot nor top, `toZ` defines an
  `OrderIso` between `ι` and `ℤ`.
* `orderIsoRangeOfLinearSuccPredArch`: if the order has both a bot and a top, `toZ` gives an
  `OrderIso` between `ι` and `Finset.range ((toZ ⊥ ⊤).toNat + 1)`.

-/

public section

open Order

variable {ι : Type*} [LinearOrder ι]

namespace LinearOrder

variable [SuccOrder ι] [PredOrder ι]

instance (priority := 100) isPredArchimedean_of_isSuccArchimedean [IsSuccArchimedean ι] :
    IsPredArchimedean ι where
  exists_pred_iterate_of_le {i j} hij := by
    have h_exists := exists_succ_iterate_of_le hij
    obtain ⟨n, hn_eq, hn_lt_ne⟩ : ∃ n, succ^[n] i = j ∧ ∀ m < n, succ^[m] i ≠ j :=
      ⟨Nat.find h_exists, Nat.find_spec h_exists, fun m hmn ↦ Nat.find_min h_exists hmn⟩
    refine ⟨n, ?_⟩
    rw [← hn_eq]
    cases n with
    | zero => simp only [Function.iterate_zero, id]
    | succ n =>
      rw [pred_succ_iterate_of_not_isMax]
      rw [Nat.succ_sub_succ_eq_sub, tsub_zero]
      suffices succ^[n] i < succ^[n.succ] i from not_isMax_of_lt this
      refine lt_of_le_of_ne ?_ ?_
      · rw [Function.iterate_succ_apply']
        exact le_succ _
      · rw [hn_eq]
        exact hn_lt_ne _ (Nat.lt_succ_self n)

instance isSuccArchimedean_of_isPredArchimedean [IsPredArchimedean ι] : IsSuccArchimedean ι :=
  inferInstanceAs (IsSuccArchimedean ιᵒᵈᵒᵈ)

/-- In a linear `SuccOrder` that's also a `PredOrder`, `IsSuccArchimedean` and `IsPredArchimedean`
are equivalent. -/
theorem isSuccArchimedean_iff_isPredArchimedean : IsSuccArchimedean ι ↔ IsPredArchimedean ι where
  mp _ := isPredArchimedean_of_isSuccArchimedean
  mpr _ := isSuccArchimedean_of_isPredArchimedean

end LinearOrder

namespace LinearLocallyFiniteOrder

/-- Successor in a linear order. This defines a true successor only when `i` is isolated from above,
i.e. when `i` is not the greatest lower bound of `(i, ∞)`. -/
noncomputable def succFn (i : ι) : ι :=
  (exists_glb_Ioi i).choose

theorem succFn_spec (i : ι) : IsGLB (Set.Ioi i) (succFn i) :=
  (exists_glb_Ioi i).choose_spec

theorem le_succFn (i : ι) : i ≤ succFn i := by
  rw [le_isGLB_iff (succFn_spec i), mem_lowerBounds]
  exact fun x hx ↦ le_of_lt hx

theorem isGLB_Ioc_of_isGLB_Ioi {i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i) k) :
    IsGLB (Set.Ioc i j) k := by
  simp_rw [IsGLB, IsGreatest, mem_upperBounds, mem_lowerBounds] at h ⊢
  refine ⟨fun x hx ↦ h.1 x hx.1, fun x hx ↦ h.2 x ?_⟩
  intro y hy
  rcases le_or_gt y j with h_le | h_lt
  · exact hx y ⟨hy, h_le⟩
  · exact le_trans (hx j ⟨hij_lt, le_rfl⟩) h_lt.le

theorem isMax_of_succFn_le [LocallyFiniteOrder ι] (i : ι) (hi : succFn i ≤ i) : IsMax i := by
  refine fun j _ ↦ not_lt.mp fun hij_lt ↦ ?_
  have h_succFn_eq : succFn i = i := le_antisymm hi (le_succFn i)
  have h_glb : IsGLB (Finset.Ioc i j : Set ι) i := by
    rw [Finset.coe_Ioc]
    have h := succFn_spec i
    rw [h_succFn_eq] at h
    exact isGLB_Ioc_of_isGLB_Ioi hij_lt h
  have hi_mem : i ∈ Finset.Ioc i j := by
    refine Finset.isGLB_mem _ h_glb ?_
    exact ⟨_, Finset.mem_Ioc.mpr ⟨hij_lt, le_rfl⟩⟩
  rw [Finset.mem_Ioc] at hi_mem
  exact lt_irrefl i hi_mem.1

theorem succFn_le_of_lt (i j : ι) (hij : i < j) : succFn i ≤ j := by
  have h := succFn_spec i
  rw [IsGLB, IsGreatest, mem_lowerBounds] at h
  exact h.1 j hij

theorem le_of_lt_succFn (j i : ι) (hij : j < succFn i) : j ≤ i := by
  rw [lt_isGLB_iff (succFn_spec i)] at hij
  obtain ⟨k, hk_lb, hk⟩ := hij
  rw [mem_lowerBounds] at hk_lb
  exact not_lt.mp fun hi_lt_j ↦ not_le.mpr hk (hk_lb j hi_lt_j)

variable (ι) in
/-- A locally finite order is a `SuccOrder`.
This is not an instance, because its `succ` field conflicts with computable `SuccOrder` structures
on `ℕ` and `ℤ`. -/
@[instance_reducible]
noncomputable def succOrder [LocallyFiniteOrder ι] : SuccOrder ι where
  succ := succFn
  le_succ := le_succFn
  max_of_succ_le h := isMax_of_succFn_le _ h
  succ_le_of_lt h := succFn_le_of_lt _ _ h

variable (ι) in
/-- A locally finite order is a `PredOrder`.
This is not an instance, because its `succ` field conflicts with computable `PredOrder` structures
on `ℕ` and `ℤ`. -/
@[instance_reducible]
noncomputable def predOrder [LocallyFiniteOrder ι] : PredOrder ι :=
  letI := succOrder (ι := ιᵒᵈ)
  inferInstanceAs (PredOrder ιᵒᵈᵒᵈ)

instance (priority := 100) [LocallyFiniteOrder ι] [SuccOrder ι] : IsSuccArchimedean ι where
  exists_succ_iterate_of_le := by
    intro i j hij
    rw [le_iff_lt_or_eq] at hij
    rcases hij with hij | hij
    swap
    · refine ⟨0, ?_⟩
      simpa only [Function.iterate_zero, id] using hij
    by_contra! h
    have h_lt : ∀ n, succ^[n] i < j := fun n ↦ by
      induction n with
      | zero => simpa only [Function.iterate_zero, id] using hij
      | succ n hn =>
        refine lt_of_le_of_ne ?_ (h _)
        rw [Function.iterate_succ', Function.comp_apply]
        exact succ_le_of_lt hn
    have h_mem : ∀ n, succ^[n] i ∈ Finset.Icc i j :=
      fun n ↦ Finset.mem_Icc.mpr ⟨le_succ_iterate n i, (h_lt n).le⟩
    obtain ⟨n, m, hnm, h_eq⟩ : ∃ n m, n < m ∧ succ^[n] i = succ^[m] i := by
      let f : ℕ → Finset.Icc i j := fun n ↦ ⟨succ^[n] i, h_mem n⟩
      obtain ⟨n, m, hnm_ne, hfnm⟩ : ∃ n m, n ≠ m ∧ f n = f m :=
        Finite.exists_ne_map_eq_of_infinite f
      have hnm_eq : succ^[n] i = succ^[m] i := by simpa only [f, Subtype.mk_eq_mk] using hfnm
      rcases le_total n m with h_le | h_le
      · exact ⟨n, m, lt_of_le_of_ne h_le hnm_ne, hnm_eq⟩
      · exact ⟨m, n, lt_of_le_of_ne h_le hnm_ne.symm, hnm_eq.symm⟩
    have h_max : IsMax (succ^[n] i) := isMax_iterate_succ_of_eq_of_ne h_eq hnm.ne
    exact not_le.mpr (h_lt n) (h_max (h_lt n).le)

instance (priority := 100) [LocallyFiniteOrder ι] [PredOrder ι] : IsPredArchimedean ι :=
  inferInstanceAs (IsPredArchimedean ιᵒᵈᵒᵈ)

end LinearLocallyFiniteOrder

section toZ

-- Requiring either of `IsSuccArchimedean` or `IsPredArchimedean` is equivalent.
variable [SuccOrder ι] [IsSuccArchimedean ι] [PredOrder ι] {i0 i : ι}

-- For "to_Z"

/-- `toZ` numbers elements of `ι` according to their order, starting from `i0`. We prove in
`orderIsoRangeToZOfLinearSuccPredArch` that this defines an `OrderIso` between `ι` and
the range of `toZ`. -/
def toZ (i0 i : ι) : ℤ :=
  dite (i0 ≤ i) (fun hi ↦ Nat.find (exists_succ_iterate_of_le hi)) fun hi ↦
    -Nat.find (exists_pred_iterate_of_le (α := ι) (not_le.mp hi).le)

theorem toZ_of_ge (hi : i0 ≤ i) : toZ i0 i = Nat.find (exists_succ_iterate_of_le hi) :=
  dif_pos hi

theorem toZ_of_lt (hi : i < i0) :
    toZ i0 i = -Nat.find (exists_pred_iterate_of_le (α := ι) hi.le) :=
  dif_neg (not_le.mpr hi)

@[simp]
theorem toZ_of_eq : toZ i0 i0 = 0 := by
  rw [toZ_of_ge le_rfl]
  norm_cast
  rw [← nonpos_iff_eq_zero]
  apply Nat.find_le
  rw [Function.iterate_zero, id]

theorem iterate_succ_toZ (i : ι) (hi : i0 ≤ i) : succ^[(toZ i0 i).toNat] i0 = i := by
  rw [toZ_of_ge hi, Int.toNat_natCast]
  exact Nat.find_spec (exists_succ_iterate_of_le hi)

theorem iterate_pred_toZ (i : ι) (hi : i < i0) : pred^[(-toZ i0 i).toNat] i0 = i := by
  rw [toZ_of_lt hi, neg_neg, Int.toNat_natCast]
  exact Nat.find_spec (exists_pred_iterate_of_le hi.le)

lemma toZ_nonneg (hi : i0 ≤ i) : 0 ≤ toZ i0 i := by rw [toZ_of_ge hi]; exact Int.natCast_nonneg _

theorem toZ_neg (hi : i < i0) : toZ i0 i < 0 := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [toZ_of_lt hi]
    lia
  · by_contra h
    have h_eq := iterate_pred_toZ i hi
    rw [← h_eq, h] at hi
    simp only [neg_zero, Int.toNat_zero, Function.iterate_zero, id, lt_self_iff_false] at hi

theorem toZ_iterate_succ_le (n : ℕ) : toZ i0 (succ^[n] i0) ≤ n := by
  rw [toZ_of_ge (le_succ_iterate _ _)]
  norm_cast
  exact Nat.find_min' _ rfl

theorem toZ_iterate_pred_ge (n : ℕ) : -(n : ℤ) ≤ toZ i0 (pred^[n] i0) := by
  rcases le_or_gt i0 (pred^[n] i0) with h | h
  · have h_eq : pred^[n] i0 = i0 := le_antisymm (pred_iterate_le _ _) h
    rw [h_eq, toZ_of_eq]
    lia
  · rw [toZ_of_lt h]
    refine Int.neg_le_neg ?_
    norm_cast
    exact Nat.find_min' _ rfl

theorem toZ_iterate_succ_of_not_isMax (n : ℕ) (hn : ¬IsMax (succ^[n] i0)) :
    toZ i0 (succ^[n] i0) = n := by
  let m := (toZ i0 (succ^[n] i0)).toNat
  have h_eq : succ^[m] i0 = succ^[n] i0 := iterate_succ_toZ _ (le_succ_iterate _ _)
  by_cases hmn : m = n
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max, toZ_of_ge (le_succ_iterate _ _), max_eq_left]
    exact Int.natCast_nonneg _
  suffices IsMax (succ^[n] i0) from absurd this hn
  exact isMax_iterate_succ_of_eq_of_ne h_eq.symm (Ne.symm hmn)

theorem toZ_iterate_pred_of_not_isMin (n : ℕ) (hn : ¬IsMin (pred^[n] i0)) :
    toZ i0 (pred^[n] i0) = -n := by
  rcases n with - | n
  · simp
  have : pred^[n.succ] i0 < i0 := by
    refine lt_of_le_of_ne (pred_iterate_le _ _) fun h_pred_iterate_eq ↦ hn ?_
    have h_pred_eq_pred : pred^[n.succ] i0 = pred^[0] i0 := by
      rwa [Function.iterate_zero, id]
    exact isMin_iterate_pred_of_eq_of_ne h_pred_eq_pred (Nat.succ_ne_zero n)
  let m := (-toZ i0 (pred^[n.succ] i0)).toNat
  have h_eq : pred^[m] i0 = pred^[n.succ] i0 := iterate_pred_toZ _ this
  by_cases hmn : m = n + 1
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max, toZ_of_lt this, max_eq_left, neg_neg]
    rw [neg_neg]
    exact Int.natCast_nonneg _
  · suffices IsMin (pred^[n.succ] i0) from absurd this hn
    exact isMin_iterate_pred_of_eq_of_ne h_eq.symm (Ne.symm hmn)

theorem toZ_strictMono : StrictMono (toZ i0) := by
  intro j i h_le
  contrapose! h_le
  rcases le_or_gt i0 i with hi | hi <;> rcases le_or_gt i0 j with hj | hj
  · rw [← iterate_succ_toZ i hi, ← iterate_succ_toZ j hj]
    exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ _) (Int.toNat_le_toNat h_le)
  · exact absurd ((toZ_neg hj).trans_le (toZ_nonneg hi)) (not_lt.mpr h_le)
  · exact hi.le.trans hj
  · rw [← iterate_pred_toZ i hi, ← iterate_pred_toZ j hj]
    refine Monotone.antitone_iterate_of_map_le pred_mono (pred_le _) (Int.toNat_le_toNat ?_)
    exact Int.neg_le_neg h_le

theorem injective_toZ : Function.Injective (toZ i0) :=
  toZ_strictMono.injective

@[simp]
theorem toZ_le_toZ {i j : ι} : toZ i0 i ≤ toZ i0 j ↔ i ≤ j :=
  toZ_strictMono.le_iff_le

@[deprecated (since := "2026-05-07")]
alias toZ_le_iff := toZ_le_toZ

@[deprecated toZ_le_toZ (since := "2026-05-06")]
alias ⟨le_of_toZ_le, toZ_mono⟩ := toZ_le_toZ

@[simp]
theorem toZ_lt_toZ {i j : ι} : toZ i0 i < toZ i0 j ↔ i < j :=
  toZ_strictMono.lt_iff_lt

@[deprecated (since := "2026-05-07")]
alias toZ_lt_iff := toZ_lt_toZ

@[simp]
theorem toZ_inj {i j : ι} : toZ i0 i = toZ i0 j ↔ i = j :=
  injective_toZ.eq_iff

theorem toZ_iterate_succ [NoMaxOrder ι] (n : ℕ) : toZ i0 (succ^[n] i0) = n :=
  toZ_iterate_succ_of_not_isMax n (not_isMax _)

theorem toZ_iterate_pred [NoMinOrder ι] (n : ℕ) : toZ i0 (pred^[n] i0) = -n :=
  toZ_iterate_pred_of_not_isMin n (not_isMin _)

end toZ

section OrderIso

variable [SuccOrder ι] [PredOrder ι] [IsSuccArchimedean ι]

/-- `toZ` defines an `OrderIso` between `ι` and its range. -/
noncomputable def orderIsoRangeToZOfLinearSuccPredArch [hι : Nonempty ι] :
    ι ≃o Set.range (toZ hι.some) where
  toEquiv := Equiv.ofInjective _ injective_toZ
  map_rel_iff' := by simp

instance (priority := 100) countable_of_linear_succ_pred_arch : Countable ι := by
  rcases isEmpty_or_nonempty ι with _ | hι
  · infer_instance
  · exact Countable.of_equiv _ orderIsoRangeToZOfLinearSuccPredArch.symm.toEquiv

/-- If the order has neither bot nor top, `toZ` defines an `OrderIso` between `ι` and `ℤ`. -/
noncomputable def orderIsoIntOfLinearSuccPredArch [NoMaxOrder ι] [NoMinOrder ι] [hι : Nonempty ι] :
    ι ≃o ℤ where
  toFun := toZ hι.some
  invFun n := if 0 ≤ n then succ^[n.toNat] hι.some else pred^[(-n).toNat] hι.some
  left_inv i := by
    rcases le_or_gt hι.some i with hi | hi
    · have h_nonneg : 0 ≤ toZ hι.some i := toZ_nonneg hi
      simp_rw [if_pos h_nonneg]
      exact iterate_succ_toZ i hi
    · have h_neg : toZ hι.some i < 0 := toZ_neg hi
      simp_rw [if_neg (not_le.mpr h_neg)]
      exact iterate_pred_toZ i hi
  right_inv n := by
    rcases le_or_gt 0 n with hn | hn
    · simp_rw [if_pos hn]
      rw [toZ_iterate_succ]
      exact Int.toNat_of_nonneg hn
    · simp_rw [if_neg (not_le.mpr hn)]
      rw [toZ_iterate_pred]
      simp only [hn.le, Int.toNat_of_nonneg, Int.neg_nonneg_of_nonpos, Int.neg_neg]
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/-- If the order has a bot but no top, `toZ` defines an `OrderIso` between `ι` and `ℕ`. -/
def orderIsoNatOfLinearSuccPredArch [NoMaxOrder ι] [OrderBot ι] : ι ≃o ℕ where
  toFun i := (toZ ⊥ i).toNat
  invFun n := succ^[n] ⊥
  left_inv i := by
    dsimp only
    exact iterate_succ_toZ i bot_le
  right_inv n := by
    dsimp only
    rw [toZ_iterate_succ]
    exact Int.toNat_natCast n
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Int.toNat_le]
    rw [← toZ_le_toZ (i0 := (⊥ : ι)), Int.toNat_of_nonneg (toZ_nonneg bot_le)]

set_option backward.isDefEq.respectTransparency false in
/-- If the order has both a bot and a top, `toZ` gives an `OrderIso` between `ι` and
`Finset.range n` for some `n`. -/
def orderIsoRangeOfLinearSuccPredArch [OrderBot ι] [OrderTop ι] :
    ι ≃o Finset.range ((toZ ⊥ (⊤ : ι)).toNat + 1) where
  toFun i :=
    ⟨(toZ ⊥ i).toNat,
      Finset.mem_range_succ_iff.mpr (Int.toNat_le_toNat (toZ_le_toZ.mpr le_top))⟩
  invFun n := succ^[n] ⊥
  left_inv i := iterate_succ_toZ i bot_le
  right_inv n := by
    ext1
    simp only
    refine le_antisymm ?_ ?_
    · rw [Int.toNat_le]
      exact toZ_iterate_succ_le _
    by_cases hn_max : IsMax (succ^[↑n] (⊥ : ι))
    · rw [← isTop_iff_isMax, isTop_iff_eq_top] at hn_max
      rw [hn_max]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp n.prop)
    · rw [toZ_iterate_succ_of_not_isMax _ hn_max]
      simp only [Int.toNat_natCast, le_refl]
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Int.toNat_le]
    rw [← toZ_le_toZ (i0 := (⊥ : ι)), Int.toNat_of_nonneg (toZ_nonneg bot_le)]

end OrderIso

instance (priority := 100) Countable.of_linearOrder_locallyFiniteOrder [LocallyFiniteOrder ι] :
    Countable ι :=
  have := LinearLocallyFiniteOrder.succOrder ι
  have := LinearLocallyFiniteOrder.predOrder ι
  countable_of_linear_succ_pred_arch
