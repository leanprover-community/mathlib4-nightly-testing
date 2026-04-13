/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs

/-!

# Covariants and contravariants

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `Ordered[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `CovariantClass` and
`ContravariantClass`:

* `CovariantClass` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `ContravariantClass` models the implication `a * b < a * c → b < c`.

Since `Co(ntra)variantClass` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`Ordered[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[OrderedCancelMonoid M]`, into three typeclasses, e.g.
`[CancelMonoid M] [PartialOrder M] [CovariantClass M M (Function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several `Co(ntra)variantClass` assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[CovariantClass M M (*) (≤)] [ContravariantClass M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `CovariantClass` uses the `(≤)`-relation, while
`ContravariantClass` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[Semigroup α] [PartialOrder α] [ContravariantClass α α (*) (≤)] → LeftCancelSemigroup α
```
holds -- note the `Co*ntra*` assumption on the `(≤)`-relation.

## Formalization notes

We stick to the convention of using `Function.swap (*)` (or `Function.swap (+)`), for the
typeclass assumptions, since `Function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use.

-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section


-- TODO: convert `ExistsMulOfLE`, `ExistsAddOfLE`?
-- TODO: relationship with `Con/AddCon`
-- TODO: include equivalence of `LeftCancelSemigroup` with
-- `Semigroup PartialOrder ContravariantClass α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion?  See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.
open Function

section Variants

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)
variable (M N)

/-- `Covariant` is useful to formulate succinctly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `CovariantClass` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/-- `Contravariant` is useful to formulate succinctly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `ContravariantClass` doc-string for its meaning. -/
def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`CovariantClass` says that "the action `μ` preserves the relation `r`."

More precisely, the `CovariantClass` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by acting upon it by `m`.

If `m : M` and `h : r n₁ n₂`, then `CovariantClass.elim m h : r (μ m n₁) (μ m n₂)`.
-/
class CovariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
  `(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)` -/
  protected elim : Covariant M N μ r

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`ContravariantClass` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`."

More precisely, the `ContravariantClass` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the
assertion that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
`r` also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `ContravariantClass.elim m h : r n₁ n₂`.
-/
class ContravariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
  pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
  `r` also holds for the pair `(n₁, n₂)`. -/
  protected elim : Contravariant M N μ r

/-- Typeclass for monotonicity of multiplication on the left,
namely `b₁ ≤ b₂ → a * b₁ ≤ a * b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCommMonoid`. -/
abbrev MulLeftMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (· * ·) (· ≤ ·)

/-- Typeclass for monotonicity of multiplication on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCommMonoid`. -/
abbrev MulRightMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· ≤ ·)

/-- Typeclass for monotonicity of addition on the left,
namely `b₁ ≤ b₂ → a + b₁ ≤ a + b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedAddCommMonoid`. -/
abbrev AddLeftMono [Add M] [LE M] : Prop :=
  CovariantClass M M (· + ·) (· ≤ ·)

/-- Typeclass for monotonicity of addition on the right,
namely `a₁ ≤ a₂ → a₁ + b ≤ a₂ + b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedAddCommMonoid`. -/
abbrev AddRightMono [Add M] [LE M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· ≤ ·)

attribute [to_additive existing] MulLeftMono MulRightMono

/-- Typeclass for monotonicity of multiplication on the left,
namely `b₁ < b₂ → a * b₁ < a * b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCommGroup`. -/
abbrev MulLeftStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (· * ·) (· < ·)

/-- Typeclass for monotonicity of multiplication on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCommGroup`. -/
abbrev MulRightStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· < ·)

/-- Typeclass for monotonicity of addition on the left,
namely `b₁ < b₂ → a + b₁ < a + b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedAddCommGroup`. -/
abbrev AddLeftStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (· + ·) (· < ·)

/-- Typeclass for monotonicity of addition on the right,
namely `a₁ < a₂ → a₁ + b < a₂ + b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedAddCommGroup`. -/
abbrev AddRightStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftStrictMono MulRightStrictMono

/-- Typeclass for strict reverse monotonicity of multiplication on the left,
namely `a * b₁ < a * b₂ → b₁ < b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCommGroup`. -/
abbrev MulLeftReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (· * ·) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication on the right,
namely `a₁ * b < a₂ * b → a₁ < a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCommGroup`. -/
abbrev MulRightReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (swap (· * ·)) (· < ·)

/-- Typeclass for strict reverse monotonicity of addition on the left,
namely `a + b₁ < a + b₂ → b₁ < b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedAddCommGroup`. -/
abbrev AddLeftReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (· + ·) (· < ·)

/-- Typeclass for strict reverse monotonicity of addition on the right,
namely `a₁ * b < a₂ * b → a₁ < a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedAddCommGroup`. -/
abbrev AddRightReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftReflectLT MulRightReflectLT

/-- Typeclass for reverse monotonicity of multiplication on the left,
namely `a * b₁ ≤ a * b₂ → b₁ ≤ b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCancelCommMonoid`. -/
abbrev MulLeftReflectLE [Mul M] [LE M] : Prop :=
  ContravariantClass M M (· * ·) (· ≤ ·)

/-- Typeclass for reverse monotonicity of multiplication on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCancelCommMonoid`. -/
abbrev MulRightReflectLE [Mul M] [LE M] : Prop :=
  ContravariantClass M M (swap (· * ·)) (· ≤ ·)

/-- Typeclass for reverse monotonicity of addition on the left,
namely `a + b₁ ≤ a + b₂ → b₁ ≤ b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCancelAddCommMonoid`. -/
abbrev AddLeftReflectLE [Add M] [LE M] : Prop :=
  ContravariantClass M M (· + ·) (· ≤ ·)

/-- Typeclass for reverse monotonicity of addition on the right,
namely `a₁ + b ≤ a₂ + b → a₁ ≤ a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`OrderedCancelAddCommMonoid`. -/
abbrev AddRightReflectLE [Add M] [LE M] : Prop :=
  ContravariantClass M M (swap (· + ·)) (· ≤ ·)

attribute [to_additive existing] MulLeftReflectLE MulRightReflectLE

theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩

section flip

variable {M N μ r}

theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) :=
  fun a _ _ ↦ h a

theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) :=
  fun a _ _ ↦ h a

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab

@[to_additive]
theorem Group.covariant_iff_contravariant [Group N] :
    Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r := by
  refine ⟨fun h a b c bc ↦ ?_, fun h a b c bc ↦ ?_⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc

@[to_additive]
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] :
    ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩

@[to_additive]
theorem Group.mulLeftReflectLE_of_mulLeftMono [Group N] [LE N]
    [MulLeftMono N] : MulLeftReflectLE N :=
  inferInstance

@[to_additive]
theorem Group.mulLeftReflectLT_of_mulLeftStrictMono [Group N] [LT N]
    [MulLeftStrictMono N] : MulLeftReflectLT N :=
  inferInstance

@[to_additive]
theorem Group.covariant_swap_iff_contravariant_swap [Group N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r := by
  refine ⟨fun h a b c bc ↦ ?_, fun h a b c bc ↦ ?_⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc


@[to_additive]
instance (priority := 100) Group.covconv_swap [Group N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩

@[to_additive]
theorem Group.mulRightReflectLE_of_mulRightMono [Group N] [LE N]
    [MulRightMono N] : MulRightReflectLE N :=
  inferInstance

@[to_additive]
theorem Group.mulRightReflectLT_of_mulRightStrictMono [Group N] [LT N]
    [MulRightStrictMono N] : MulRightReflectLT N :=
  inferInstance


section Trans

variable [IsTrans N r] (m : M) {a b c : N}

--  Lemmas with 3 elements.
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  _root_.trans (act_rel_act_of_rel m ab) rl

theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  _root_.trans rr (act_rel_act_of_rel _ ab)

end Trans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [i : CovariantClass N N mu r]
  [i' : CovariantClass N N (swap mu) r] {a b c d : N}

theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r _ c _ _ ab) (act_rel_act_of_rel b cd)

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab

section Trans

variable [IsTrans N r] (m : M) {a b c : N}

--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
    r (μ m a) c :=
  _root_.trans ab (rel_of_act_rel_act m rl)

theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
    r a (μ m c) :=
  _root_.trans (rel_of_act_rel_act m ab) rr

end Trans

end Contravariant

section Monotone

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]
variable {f : N → α}

/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) :=
  fun _ _ ↦ CovariantClass.elim m

/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (m + n))`. -/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone (f <| μ m ·) :=
  hf.comp (Covariant.monotone_of_const m)

/-- Same as `Monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (n + m))`. -/
theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Monotone f) (m : N) : Monotone (f <| μ · m) :=
  Monotone.covariant_of_const (μ := swap μ) hf m

/-- Dual of `Monotone.covariant_of_const` -/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone (f <| μ m ·) :=
  hf.comp_monotone <| Covariant.monotone_of_const m

/-- Dual of `Monotone.covariant_of_const'` -/
theorem Antitone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Antitone f) (m : N) : Antitone (f <| μ · m) :=
  Antitone.covariant_of_const (μ := swap μ) hf m

end Monotone

theorem covariant_le_of_covariant_lt [PartialOrder N] :
    Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  intro h a b c bc
  rcases bc.eq_or_lt with (rfl | bc)
  · exact le_rfl
  · exact (h _ bc).le

theorem covariantClass_le_of_lt [PartialOrder N] [CovariantClass M N μ (· < ·)] :
    CovariantClass M N μ (· ≤ ·) := ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

@[to_additive]
theorem mulLeftMono_of_mulLeftStrictMono (M) [Mul M] [PartialOrder M] [MulLeftStrictMono M] :
    MulLeftMono M := covariantClass_le_of_lt _ _ _

@[to_additive]
theorem mulRightMono_of_mulRightStrictMono (M) [Mul M] [PartialOrder M] [MulRightStrictMono M] :
    MulRightMono M := covariantClass_le_of_lt _ _ _

theorem contravariant_le_iff_contravariant_lt_and_eq [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) ∧ Contravariant M N μ (· = ·) := by
  refine ⟨fun h ↦ ⟨fun a b c bc ↦ ?_, fun a b c bc ↦ ?_⟩, fun h ↦ fun a b c bc ↦ ?_⟩
  · exact (h a bc.le).lt_of_ne (by rintro rfl; exact lt_irrefl _ bc)
  · exact (h a bc.le).antisymm (h a bc.ge)
  · exact bc.lt_or_eq.elim (fun bc ↦ (h.1 a bc).le) (fun bc ↦ (h.2 a bc).le)

theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) :=
  And.left ∘ (contravariant_le_iff_contravariant_lt_and_eq M N μ).mp

theorem covariant_le_iff_contravariant_lt [LinearOrder N] :
    Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h _ _ _ bc ↦ not_le.mp fun k ↦ bc.not_ge (h _ k),
   fun h _ _ _ bc ↦ not_lt.mp fun k ↦ bc.not_gt (h _ k)⟩

theorem covariant_lt_iff_contravariant_le [LinearOrder N] :
    Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h _ _ _ bc ↦ not_lt.mp fun k ↦ bc.not_gt (h _ k),
   fun h _ _ _ bc ↦ not_le.mp fun k ↦ bc.not_ge (h _ k)⟩

variable (mu : N → N → N)

theorem covariant_flip_iff [h : Std.Commutative mu] :
    Covariant N N (flip mu) r ↔ Covariant N N mu r := by unfold flip; simp_rw [h.comm]

theorem contravariant_flip_iff [h : Std.Commutative mu] :
    Contravariant N N (flip mu) r ↔ Contravariant N N mu r := by unfold flip; simp_rw [h.comm]

instance contravariant_lt_of_covariant_le [LinearOrder N]
    [CovariantClass N N mu (· ≤ ·)] : ContravariantClass N N mu (· < ·) where
  elim := (covariant_le_iff_contravariant_lt N N mu).mp CovariantClass.elim

@[to_additive]
theorem mulLeftReflectLT_of_mulLeftMono [Mul N] [LinearOrder N] [MulLeftMono N] :
    MulLeftReflectLT N :=
  inferInstance

@[to_additive]
theorem mulRightReflectLT_of_mulRightMono [Mul N] [LinearOrder N] [MulRightMono N] :
    MulRightReflectLT N :=
  inferInstance

instance covariant_lt_of_contravariant_le [LinearOrder N]
    [ContravariantClass N N mu (· ≤ ·)] : CovariantClass N N mu (· < ·) where
  elim := (covariant_lt_iff_contravariant_le N N mu).mpr ContravariantClass.elim

@[to_additive]
theorem mulLeftStrictMono_of_mulLeftReflectLE [Mul N] [LinearOrder N] [MulLeftReflectLE N] :
    MulLeftStrictMono N :=
  inferInstance

@[to_additive]
theorem mulRightStrictMono_of_mulRightReflectLE [Mul N] [LinearOrder N] [MulRightReflectLE N] :
    MulRightStrictMono N :=
  inferInstance

@[to_additive]
instance covariant_swap_mul_of_covariant_mul [CommSemigroup N]
    [CovariantClass N N (· * ·) r] : CovariantClass N N (swap (· * ·)) r where
  elim := (covariant_flip_iff N r (· * ·)).mpr CovariantClass.elim

@[to_additive]
theorem mulRightMono_of_mulLeftMono [CommSemigroup N] [LE N] [MulLeftMono N] :
    MulRightMono N :=
  inferInstance

@[to_additive]
theorem mulRightStrictMono_of_mulLeftStrictMono [CommSemigroup N] [LT N] [MulLeftStrictMono N] :
    MulRightStrictMono N :=
  inferInstance

@[to_additive]
instance contravariant_swap_mul_of_contravariant_mul [CommSemigroup N]
    [ContravariantClass N N (· * ·) r] : ContravariantClass N N (swap (· * ·)) r where
  elim := (contravariant_flip_iff N r (· * ·)).mpr ContravariantClass.elim

@[to_additive]
theorem mulRightReflectLE_of_mulLeftReflectLE [CommSemigroup N] [LE N] [MulLeftReflectLE N] :
    MulRightReflectLE N :=
  inferInstance

@[to_additive]
theorem mulRightReflectLT_of_mulLeftReflectLT [CommSemigroup N] [LT N] [MulLeftReflectLT N] :
    MulRightReflectLT N :=
  inferInstance

theorem covariant_lt_of_covariant_le_of_contravariant_eq [ContravariantClass M N μ (· = ·)]
    [PartialOrder N] [CovariantClass M N μ (· ≤ ·)] : CovariantClass M N μ (· < ·) where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne (bc.ne ∘ ContravariantClass.elim _)

theorem contravariant_le_of_contravariant_eq_and_lt [PartialOrder N]
    [ContravariantClass M N μ (· = ·)] [ContravariantClass M N μ (· < ·)] :
    ContravariantClass M N μ (· ≤ ·) where
  elim := (contravariant_le_iff_contravariant_lt_and_eq M N μ).mpr
    ⟨ContravariantClass.elim, ContravariantClass.elim⟩

/- TODO:
  redefine `IsLeftCancel N mu` as abbrev of `ContravariantClass N N mu (· = ·)`,
  redefine `IsRightCancel N mu` as abbrev of `ContravariantClass N N (flip mu) (· = ·)`,
  redefine `IsLeftCancelMul` as abbrev of `IsLeftCancel`,
  then the following four instances (actually eight) can be removed in favor of the above two. -/

@[to_additive]
instance IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftMono N] :
    MulLeftStrictMono N where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_right a).mpr bc.ne)

@[to_additive]
instance IsRightCancelMul.mulRightStrictMono_of_mulRightMono
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightMono N] :
    MulRightStrictMono N where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_left a).mpr bc.ne)

@[to_additive]
instance IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftReflectLT N] :
    MulLeftReflectLE N where
  elim := (contravariant_le_iff_contravariant_lt_and_eq N N _).mpr
    ⟨ContravariantClass.elim, fun _ ↦ mul_left_cancel⟩

@[to_additive]
instance IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightReflectLT N] :
    MulRightReflectLE N where
  elim := (contravariant_le_iff_contravariant_lt_and_eq N N _).mpr
    ⟨ContravariantClass.elim, fun _ ↦ mul_right_cancel⟩

end Variants
