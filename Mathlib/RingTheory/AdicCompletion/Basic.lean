/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Judith Ludwig, Christian Merten, Jiedong Jiang
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.SuppressCompilation

/-!
# Completion of a module with respect to an ideal.

In this file we define the notions of Hausdorff, precomplete, and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `IsHausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `IsPrecomplete I M`: this says that every Cauchy sequence converges.
- `IsAdicComplete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorffification I M`: this is the universal Hausdorff module with a map from `M`.
- `AdicCompletion I M`: if `I` is finitely generated, then this is the universal complete module
  with a linear map `AdicCompletion.lift` from `M`. This map is injective iff `M` is Hausdorff
  and surjective iff `M` is precomplete.
- `IsAdicComplete.lift`: if `N` is `I`-adically complete, then a compatible family of
  linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤)` can be lifted to a unique linear map `M →ₗ[R] N`.
  Together with `mk_lift_apply` and `eq_lift`, it gives the universal property of being
  `I`-adically complete.
-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

suppress_compilation

open Submodule Ideal Quotient

variable {R S T : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
class IsHausdorff : Prop where
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
class IsPrecomplete : Prop where
  prec' : ∀ f : ℕ → M, (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
    ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
@[mk_iff, stacks 0317 "see also `IsAdicComplete.of_bijective_iff`"]
class IsAdicComplete : Prop extends IsHausdorff I M, IsPrecomplete I M

variable {I M}

theorem IsHausdorff.haus (_ : IsHausdorff I M) :
    ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  IsHausdorff.haus'

theorem isHausdorff_iff :
    IsHausdorff I M ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩

theorem IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {x y : M} :
    x = y ↔ ∀ n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  refine ⟨fun h _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (x - y)
  simpa [SModEq.sub_mem] using h

theorem IsHausdorff.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsHausdorff (I.map (algebraMap R S)) M ↔ IsHausdorff I M := by
  simp [isHausdorff_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

theorem IsHausdorff.of_map [CommRing S] [Module S M] {J : Ideal S} [Algebra R S]
    [IsScalarTower R S M] (hIJ : I.map (algebraMap R S) ≤ J) [IsHausdorff J M] :
    IsHausdorff I M := by
  refine ⟨fun x h ↦ IsHausdorff.haus ‹_› x fun n ↦ ?_⟩
  apply SModEq.of_toAddSubgroup_le
      (U := (I ^ n • ⊤ : Submodule R M)) (V := (J ^ n • ⊤ : Submodule S M))
  · rw [← AddSubgroup.toAddSubmonoid_le]
    simp only [Submodule.smul_toAddSubmonoid, Submodule.top_toAddSubmonoid]
    rw [AddSubmonoid.smul_le]
    intro r hr m hm
    rw [← algebraMap_smul S r m]
    apply AddSubmonoid.smul_mem_smul ?_ hm
    have := Ideal.mem_map_of_mem (algebraMap R S) hr
    simp only [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hIJ n this
  · exact h n

variable (I) in
theorem IsHausdorff.funext {M : Type*} [IsHausdorff I N] {f g : M → N}
    (h : ∀ n m, Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f m) =
    Submodule.Quotient.mk (g m)) :
    f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  exact h n m

variable (I) in
theorem IsHausdorff.StrictMono.funext {M : Type*} [IsHausdorff I N] {f g : M → N} {a : ℕ → ℕ}
    (ha : StrictMono a) (h : ∀ n m, Submodule.Quotient.mk (p := (I ^ a n • ⊤ : Submodule R N))
    (f m) = Submodule.Quotient.mk (g m)) : f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I N ha.le_apply)
  exact h n m

/--
A variant of `IsHausdorff.funext`, where the target is a ring instead of a module.
-/
theorem IsHausdorff.funext' {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
    {f g : R → S} (h : ∀ n r, Ideal.Quotient.mk (I ^ n) (f r) = Ideal.Quotient.mk (I ^ n) (g r)) :
    f = g := by
  ext r
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simpa using h n r

/--
A variant of `IsHausdorff.StrictMono.funext`, where the target is a ring instead of a module.
-/
theorem IsHausdorff.StrictMono.funext' {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
    {f g : R → S} {a : ℕ → ℕ} (ha : StrictMono a) (h : ∀ n r, Ideal.Quotient.mk (I ^ a n) (f r) =
    Ideal.Quotient.mk (I ^ a n) (g r)) : f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I S ha.le_apply)
  simpa using h n m

theorem IsPrecomplete.prec (_ : IsPrecomplete I M) {f : ℕ → M} :
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _

theorem isPrecomplete_iff :
    IsPrecomplete I M ↔
      ∀ f : ℕ → M,
        (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
          ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem IsPrecomplete.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsPrecomplete (I.map (algebraMap R S)) M ↔ IsPrecomplete I M := by
  simp [isPrecomplete_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

variable (I M)

/-- The Hausdorffification of a module with respect to an ideal. -/
abbrev Hausdorffification : Type _ :=
  M ⧸ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M)

/-- The canonical linear map `M ⧸ (I ^ n • ⊤) →ₗ[R] M ⧸ (I ^ m • ⊤)` for `m ≤ n` used
to define `AdicCompletion`. -/
abbrev AdicCompletion.transitionMap {m n : ℕ} (hmn : m ≤ n) := factorPow I M hmn

/-- The completion of a module with respect to an ideal.

This is Hausdorff but not necessarily complete: a classical sufficient condition for
completeness is that `I` be finitely generated [Stacks, 05GG]. -/
def AdicCompletion : Type _ :=
  { f : ∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M) //
    ∀ {m n} (hmn : m ≤ n), AdicCompletion.transitionMap I M hmn (f n) = f m }

namespace IsHausdorff

instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩

variable {M} in
protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y => eq_of_sub_eq_zero <| h.haus (x - y) fun n => by
    rw [Ideal.top_pow, top_smul]
    exact SModEq.top⟩

instance (priority := 100) of_subsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩

variable {I M}

theorem iInf_pow_smul (h : IsHausdorff I M) : (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2 fun x hx =>
    (mem_bot _).2 <| h.haus x fun n => SModEq.zero.2 <| (mem_iInf fun n : ℕ => I ^ n • ⊤).1 hx n

end IsHausdorff

namespace Hausdorffification

/-- The canonical linear map to the Hausdorffification. -/
def of : M →ₗ[R] Hausdorffification I M :=
  mkQ _

variable {I M}

@[elab_as_elim]
theorem induction_on {C : Hausdorffification I M → Prop} (x : Hausdorffification I M)
    (ih : ∀ x, C (of I M x)) : C x :=
  Quotient.inductionOn' x ih

variable (I M)

instance : IsHausdorff I (Hausdorffification I M) :=
  ⟨fun x => Quotient.inductionOn' x fun x hx =>
    (Quotient.mk_eq_zero _).2 <| (mem_iInf _).2 fun n => by
      have := comap_map_mkQ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      rw [← this, map_smul'', Submodule.mem_comap, Submodule.map_top, range_mkQ, ← SModEq.zero]
      exact hx n⟩

variable {M} [h : IsHausdorff I N]

/-- Universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftQ _ f <| map_le_iff_le_comap.1 <| h.iInf_pow_smul ▸ le_iInf fun n =>
    le_trans (map_mono <| iInf_le _ n) <| by
      rw [map_smul'']
      exact smul_mono le_rfl le_top

theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl

theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext fun _ => rfl

/-- Uniqueness of lift. -/
theorem lift_eq (f : M →ₗ[R] N) (g : Hausdorffification I M →ₗ[R] N) (hg : g.comp (of I M) = f) :
    g = lift I f :=
  LinearMap.ext fun x => induction_on x fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]

end Hausdorffification

namespace IsPrecomplete

instance bot : IsPrecomplete (⊥ : Ideal R) M := by
  refine ⟨fun f hf => ⟨f 1, fun n => ?_⟩⟩
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact SModEq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one, bot_smul, SModEq.bot] at hf; rw [hf]

instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow, top_smul]
      exact SModEq.top⟩⟩

instance (priority := 100) of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f _ => ⟨0, fun n => by rw [Subsingleton.elim (f n) 0]⟩⟩

end IsPrecomplete

namespace AdicCompletion

/-- `AdicCompletion` is the submodule of compatible families in
`∀ n : ℕ, M ⧸ (I ^ n • ⊤)`. -/
def submodule : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := { f | ∀ {m n} (hmn : m ≤ n), AdicCompletion.transitionMap I M hmn (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply, Pi.add_apply, map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, map_smul, hf hmn]

instance : Zero (AdicCompletion I M) where
  zero := ⟨0, by simp⟩

instance : Add (AdicCompletion I M) where
  add x y := ⟨x.val + y.val, by simp [x.property, y.property]⟩

instance : Neg (AdicCompletion I M) where
  neg x := ⟨- x.val, by simp [x.property]⟩

instance : Sub (AdicCompletion I M) where
  sub x y := ⟨x.val - y.val, by simp [x.property, y.property]⟩

instance instSMul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S (AdicCompletion I M) where
  smul r x := ⟨r • x.val, by simp [x.property]⟩

@[simp, norm_cast] lemma val_zero : (0 : AdicCompletion I M).val = 0 := rfl

lemma val_zero_apply (n : ℕ) : (0 : AdicCompletion I M).val n = 0 := rfl

variable {I M}

@[simp, norm_cast] lemma val_add (f g : AdicCompletion I M) : (f + g).val = f.val + g.val := rfl
@[simp, norm_cast] lemma val_sub (f g : AdicCompletion I M) : (f - g).val = f.val - g.val := rfl
@[simp, norm_cast] lemma val_neg (f : AdicCompletion I M) : (-f).val = -f.val := rfl

lemma val_add_apply (f g : AdicCompletion I M) (n : ℕ) : (f + g).val n = f.val n + g.val n := rfl
lemma val_sub_apply (f g : AdicCompletion I M) (n : ℕ) : (f - g).val n = f.val n - g.val n := rfl
lemma val_neg_apply (f : AdicCompletion I M) (n : ℕ) : (-f).val n = -f.val n := rfl

/- No `simp` attribute, since it causes `simp` unification timeouts when considering
the `Module (AdicCompletion I R) (AdicCompletion I M)` instance (see `AdicCompletion/Algebra`). -/
@[norm_cast]
lemma val_smul [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M) :
    (s • f).val = s • f.val := rfl

lemma val_smul_apply [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M)
    (n : ℕ) : (s • f).val n = s • f.val n := rfl

@[ext]
lemma ext {x y : AdicCompletion I M} (h : ∀ n, x.val n = y.val n) : x = y := Subtype.ext <| funext h

variable (I M)

instance : AddCommGroup (AdicCompletion I M) :=
  let f : AdicCompletion I M → ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M) := Subtype.val
  Subtype.val_injective.addCommGroup f rfl val_add val_neg val_sub (fun _ _ ↦ val_smul ..)
    (fun _ _ ↦ val_smul ..)

instance [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S (AdicCompletion I M) :=
  let f : AdicCompletion I M →+ ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  Subtype.val_injective.module S f val_smul

instance instIsScalarTower [SMul S T] [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [IsScalarTower S T M] :
    IsScalarTower S T (AdicCompletion I M) where
  smul_assoc s t f := by ext; simp [val_smul]

instance instSMulCommClass [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [SMulCommClass S T M] :
    SMulCommClass S T (AdicCompletion I M) where
  smul_comm s t f := by ext; simp [val_smul, smul_comm]

instance instIsCentralScalar [SMul S R] [SMul Sᵐᵒᵖ R] [SMul S M] [SMul Sᵐᵒᵖ M]
    [IsScalarTower S R M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S (AdicCompletion I M) where
  op_smul_eq_smul s f := by ext; simp [val_smul, op_smul_eq_smul]

/-- The canonical inclusion from the completion to the product. -/
@[simps]
def incl : AdicCompletion I M →ₗ[R] (∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {I M}

@[simp, norm_cast]
lemma val_sum {ι : Type*} (s : Finset ι) (f : ι → AdicCompletion I M) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
  simp_rw [← funext (incl_apply _ _ _), map_sum]

lemma val_sum_apply {ι : Type*} (s : Finset ι) (f : ι → AdicCompletion I M) (n : ℕ) :
    (∑ i ∈ s, f i).val n = ∑ i ∈ s, (f i).val n := by simp

variable (I M)

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] AdicCompletion I M where
  toFun x := ⟨fun n => mkQ (I ^ n • ⊤ : Submodule R M) x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : AdicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun f := f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_eval (n : ℕ) :
    (eval I M n : AdicCompletion I M → M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl

theorem eval_apply (n : ℕ) (f : AdicCompletion I M) : eval I M n f = f.1 n :=
  rfl

theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

@[simp]
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkQ _ :=
  rfl

theorem eval_surjective (n : ℕ) : Function.Surjective (eval I M n) := fun x ↦
  Quotient.inductionOn' x fun x ↦ ⟨of I M x, rfl⟩

@[simp]
theorem range_eval (n : ℕ) : LinearMap.range (eval I M n) = ⊤ :=
  LinearMap.range_eq_top.2 (eval_surjective I M n)

variable {I M}

variable (I M)

instance : IsHausdorff I (AdicCompletion I M) where
  haus' x h := ext fun n ↦ by
    refine smul_induction_on (SModEq.zero.1 <| h n) (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp only [val_smul_apply, val_zero]
      induction x.val n using Quotient.inductionOn' with | _ a
      exact SModEq.zero.2 <| smul_mem_smul hr mem_top
    · simp only [val_add_apply, hx, val_zero_apply, hy, add_zero]

@[simp]
theorem transitionMap_comp_eval_apply {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I M) :
    transitionMap I M hmn (x.val n) = x.val m :=
  x.property hmn

@[simp]
theorem transitionMap_comp_eval {m n : ℕ} (hmn : m ≤ n) :
    transitionMap I M hmn ∘ₗ eval I M n = eval I M m := by
  ext x
  simp

/-- A sequence `ℕ → M` is an `I`-adic Cauchy sequence if for every `m ≤ n`,
`f m ≡ f n` modulo `I ^ m • ⊤`. -/
def IsAdicCauchy (f : ℕ → M) : Prop :=
  ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]

/-- The type of `I`-adic Cauchy sequences. -/
def AdicCauchySequence : Type _ := { f : ℕ → M // IsAdicCauchy I M f }

namespace AdicCauchySequence

/-- The type of `I`-adic Cauchy sequences is a submodule of the product `ℕ → M`. -/
def submodule : Submodule R (ℕ → M) where
  carrier := { f | IsAdicCauchy I M f }
  add_mem' := by
    intro f g hf hg m n hmn
    exact SModEq.add (hf hmn) (hg hmn)
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r f hf m n hmn
    exact SModEq.smul (hf hmn) r

instance : Zero (AdicCauchySequence I M) where
  zero := ⟨0, fun _ ↦ rfl⟩

instance : Add (AdicCauchySequence I M) where
  add x y := ⟨x.val + y.val, fun hmn ↦ SModEq.add (x.property hmn) (y.property hmn)⟩

instance : Neg (AdicCauchySequence I M) where
  neg x := ⟨- x.val, fun hmn ↦ SModEq.neg (x.property hmn)⟩

instance : Sub (AdicCauchySequence I M) where
  sub x y := ⟨x.val - y.val, fun hmn ↦ SModEq.sub (x.property hmn) (y.property hmn)⟩

instance : SMul ℕ (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn ↦ SModEq.nsmul (x.property hmn) n⟩

instance : SMul ℤ (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn ↦ SModEq.zsmul (x.property hmn) n⟩

instance : AddCommGroup (AdicCauchySequence I M) := by
  let f : AdicCauchySequence I M → (ℕ → M) := Subtype.val
  apply Subtype.val_injective.addCommGroup f rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : SMul R (AdicCauchySequence I M) where
  smul r x := ⟨r • x.val, fun hmn ↦ SModEq.smul (x.property hmn) r⟩

instance : Module R (AdicCauchySequence I M) :=
  let f : AdicCauchySequence I M →+ (ℕ → M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  Subtype.val_injective.module R f (fun _ _ ↦ rfl)

instance : CoeFun (AdicCauchySequence I M) (fun _ ↦ ℕ → M) where
  coe f := f.val

@[simp]
theorem zero_apply (n : ℕ) : (0 : AdicCauchySequence I M) n = 0 :=
  rfl

variable {I M}

@[simp]
theorem add_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n :=
  rfl

@[simp]
theorem sub_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f - g) n = f n - g n :=
  rfl

@[simp]
theorem smul_apply (n : ℕ) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r • f n :=
  rfl

@[ext]
theorem ext {x y : AdicCauchySequence I M} (h : ∀ n, x n = y n) : x = y :=
  Subtype.ext <| funext h

/-- The defining property of an adic Cauchy sequence unwrapped. -/
theorem mk_eq_mk {m n : ℕ} (hmn : m ≤ n) (f : AdicCauchySequence I M) :
    Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f n) =
      Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f m) :=
  (f.property hmn).symm

end AdicCauchySequence

/-- The `I`-adic Cauchy condition can be checked on successive `n`. -/
theorem isAdicCauchy_iff (f : ℕ → M) :
    IsAdicCauchy I M f ↔ ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  constructor
  · intro h n
    exact h (Nat.le_succ n)
  · intro h m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
        trans
        · exact ih
        · refine SModEq.mono (smul_mono (Ideal.pow_le_pow_right hmn) (by rfl)) (h n)

/-- Construct `I`-adic Cauchy sequence from sequence satisfying the successive Cauchy condition. -/
@[simps]
def AdicCauchySequence.mk (f : ℕ → M)
    (h : ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)]) : AdicCauchySequence I M where
  val := f
  property := by rwa [isAdicCauchy_iff]

/-- The canonical linear map from Cauchy sequences to the completion. -/
@[simps]
def mk : AdicCauchySequence I M →ₗ[R] AdicCompletion I M where
  toFun f := ⟨fun n ↦ Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (f n), by
    intro m n hmn
    simp only [mkQ_apply]
    exact (f.property hmn).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Criterion for checking that an adic Cauchy sequence is mapped to zero in the adic completion. -/
theorem mk_zero_of (f : AdicCauchySequence I M)
    (h : ∃ k : ℕ, ∀ n ≥ k, ∃ m ≥ n, ∃ l ≥ n, f m ∈ (I ^ l • ⊤ : Submodule R M)) :
    AdicCompletion.mk I M f = 0 := by
  obtain ⟨k, h⟩ := h
  ext n
  obtain ⟨m, hnm, l, hnl, hl⟩ := h (n + k) (by lia)
  rw [mk_apply_coe, Submodule.mkQ_apply, val_zero,
    ← AdicCauchySequence.mk_eq_mk (show n ≤ m by lia)]
  simpa using (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hl

/-- Every element in the adic completion is represented by a Cauchy sequence. -/
theorem mk_surjective : Function.Surjective (mk I M) := by
  intro x
  choose a ha using fun n ↦ Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro m n hmn
    rw [SModEq.def, ha m, ← mkQ_apply,
      ← factor_mk (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (a n),
      mkQ_apply, ha n, x.property hmn]
  · ext n
    simp [ha n]

/-- To show a statement about an element of `adicCompletion I M`, it suffices to check it
on Cauchy sequences. -/
theorem induction_on {p : AdicCompletion I M → Prop} (x : AdicCompletion I M)
    (h : ∀ (f : AdicCauchySequence I M), p (mk I M f)) : p x := by
  obtain ⟨f, rfl⟩ := mk_surjective I M x
  exact h f

variable {M}

/-- Lift a compatible family of linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)` to
the `I`-adic completion of `M`. -/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m) :
    M →ₗ[R] AdicCompletion I N where
  toFun := fun x ↦ ⟨fun n ↦ f n x, fun hkl ↦ LinearMap.congr_fun (h hkl) x⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [LinearMapClass.map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma eval_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) : eval I N n ∘ₗ lift I f h = f n :=
  rfl

@[simp]
lemma eval_lift_apply (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) (x : M) : (lift I f h x).val n = f n x :=
  rfl

section Bijective

variable {I}

set_option backward.isDefEq.respectTransparency false in
theorem of_injective_iff : Function.Injective (of I M) ↔ IsHausdorff I M := by
  constructor
  · refine fun h ↦ ⟨fun x hx ↦ h ?_⟩
    ext n
    simpa [of, SModEq.zero] using hx n
  · intro h
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    refine ⟨fun hx ↦ h.haus x fun n ↦ ?_, fun hx ↦ by simp [hx]⟩
    rw [Subtype.ext_iff] at hx
    simpa [SModEq.zero] using congrFun hx n

variable (I M) in
theorem of_injective [IsHausdorff I M] : Function.Injective (of I M) :=
  of_injective_iff.mpr ‹_›

@[simp]
theorem of_inj [IsHausdorff I M] {a b : M} : of I M a = of I M b ↔ a = b :=
  (of_injective I M).eq_iff

theorem of_surjective_iff : Function.Surjective (of I M) ↔ IsPrecomplete I M := by
  constructor
  · refine fun h ↦ ⟨fun f hmn ↦ ?_⟩
    let u : AdicCompletion I M := ⟨fun n ↦ Submodule.Quotient.mk (f n), fun c ↦ (hmn c).symm⟩
    obtain ⟨x, hx⟩ := h u
    refine ⟨x, fun n ↦ ?_⟩
    simp only [SModEq]
    rw [← mkQ_apply _ x, ← eval_of, hx]
    simp [u]
  · intro h u
    choose x hx using (fun n ↦ Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R M) (u.1 n))
    obtain ⟨a, ha⟩ := h.prec (f := x) (fun hmn ↦ by rw [SModEq, hx, ← u.2 hmn, ← hx]; simp)
    use a
    ext n
    simpa [SModEq, ← eval_of, ha, ← hx] using (ha n).symm

variable (I M) in
theorem of_surjective [IsPrecomplete I M] : Function.Surjective (of I M) :=
  of_surjective_iff.mpr ‹_›

theorem of_bijective_iff : Function.Bijective (of I M) ↔ IsAdicComplete I M :=
  ⟨fun h ↦
    { toIsHausdorff := of_injective_iff.mp h.1,
      toIsPrecomplete := of_surjective_iff.mp h.2 },
   fun h ↦ ⟨of_injective_iff.mpr h.1, of_surjective_iff.mpr h.2⟩⟩

variable (I M)

variable [IsAdicComplete I M]

theorem of_bijective : Function.Bijective (of I M) :=
  of_bijective_iff.mpr ‹_›

/--
When `M` is `I`-adic complete, the canonical map from `M` to its `I`-adic completion is a linear
equivalence.
-/
@[simps! apply]
def ofLinearEquiv : M ≃ₗ[R] AdicCompletion I M :=
  LinearEquiv.ofBijective (of I M) (of_bijective I M)

variable {M}

@[simp]
theorem ofLinearEquiv_symm_of (x : M) : (ofLinearEquiv I M).symm (of I M x) = x := by
  simp [ofLinearEquiv]

@[simp]
theorem of_ofLinearEquiv_symm (x : AdicCompletion I M) :
    of I M ((ofLinearEquiv I M).symm x) = x := by
  simp [ofLinearEquiv]

end Bijective

theorem pow_smul_top_le_ker_eval (n : ℕ) : I ^ n • ⊤ ≤ (eval I M n).ker := by
  simp only [smul_le, mem_top, LinearMap.mem_ker, map_smul, coe_eval, forall_const]
  intro r r_in x
  rw [← Submodule.Quotient.mk_out (x.val n), ← Quotient.mk_smul, Quotient.mk_eq_zero]
  exact smul_mem_smul r_in mem_top

lemma val_apply_mem_smul_top_iff {m n : ℕ} {x : AdicCompletion I M}
    (m_ge : n ≤ m) : x.val m ∈ I ^ n • (⊤ : Submodule R (M ⧸ I ^ m • ⊤)) ↔ x.val n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← x.prop m_ge, transitionMap, Submodule.factorPow, Submodule.factor, mapQ,
      ← LinearMap.mem_ker]
    simpa [ker_liftQ]
  simpa [mapQ, h, ← LinearMap.mem_ker, ker_liftQ] using x.prop m_ge

end AdicCompletion

namespace IsAdicComplete

open AdicCompletion

theorem map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] :  IsAdicComplete (I.map (algebraMap R S)) M ↔ IsAdicComplete I M := by
  simp [isAdicComplete_iff, IsPrecomplete.map_algebraMap_iff, IsHausdorff.map_algebraMap_iff]

section lift

variable [IsAdicComplete I N]

variable {M}

/--
Universal property of `IsAdicComplete`.
The lift linear map `lift I f h : M →ₗ[R] N` of a sequence of compatible
linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    M →ₗ[R] N := (ofLinearEquiv I N).symm ∘ₗ AdicCompletion.lift I f h

@[simp]
theorem of_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (x : M) :
    of I N (lift I f h x) = AdicCompletion.lift I f h x := by
  simp [lift]

@[simp]
theorem of_comp_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    of I N ∘ₗ lift I f h = AdicCompletion.lift I f h := by
  ext1; simp

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N → N ⧸ (I ^ n • ⊤)` is `f n` .
-/
@[simp]
theorem mk_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) (x : M) :
    Submodule.Quotient.mk (lift I f h x) = f n x := by
  simp only [lift, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N →ₗ[R] N ⧸ (I ^ n • ⊤)` is `f n`.
-/
@[simp]
theorem mkQ_comp_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) :
    mkQ (I ^ n • ⊤ : Submodule R N) ∘ₗ lift I f h = f n := by
  ext; simp

/--
Uniqueness of the lift.
Given a compatible family of linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
If `F : M →ₗ[R] N` makes the following diagram commute
```
  N
  | \
 F|  \ f n
  |   \
  v    v
  M --> M ⧸ (I ^ n • ⊤)
```
Then it is the map `IsAdicComplete.lift`.
-/
theorem eq_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) {F : M →ₗ[R] N}
    (hF : ∀ n, mkQ _ ∘ₗ F = f n) : F = lift I f h := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n m
  simp [← hF n]

end lift

namespace StrictMono

variable {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ (a n) • ⊤ : Submodule R N))

variable {I M}
/--
Instead of providing all `M →ₗ[R] N ⧸ (I ^ n • ⊤)`, one can just provide
`M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)` for a strictly increasing sequence `a n` to recover all
`M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def extend (n : ℕ) :
    M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  factorPow I N (ha.id_le n) ∘ₗ f n

variable (hf : ∀ {m}, factorPow I N (ha.monotone m.le_succ) ∘ₗ (f (m + 1)) = f m)

include hf in
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq
    {m n : ℕ} (hle : m ≤ n) : factorPow I N (ha.monotone hle) ∘ₗ f n = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n ↦ f n x) ?_ hle
  · exact fun _ _ le ↦ smul_mono_left (Ideal.pow_le_pow_right (ha.monotone le))
  · intro s
    simp only [LinearMap.ext_iff] at hf
    simpa using (hf x).symm

include hf in
theorem extend_eq (n : ℕ) : extend ha f (a n) = f n :=
  factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf (ha.id_le n)

include hf in
theorem factorPow_comp_extend {m n : ℕ} (hle : m ≤ n) :
    factorPow I N hle ∘ₗ extend ha f n = extend ha f m := by
  ext
  simp [extend, ← factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf hle]

variable [IsAdicComplete I N]

variable (I)

/--
A variant of `IsAdicComplete.lift`. Only takes `f n : M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)`
from a strictly increasing sequence `a n`.
-/
def lift : M →ₗ[R] N :=
  IsAdicComplete.lift I (extend ha f) (factorPow_comp_extend ha f hf)

theorem of_lift (x : M) :
    of I N (lift I ha f hf x) =
    AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) x :=
  IsAdicComplete.of_lift I (extend ha f) (factorPow_comp_extend ha f hf) x

theorem of_comp_lift :
    of I N ∘ₗ lift I ha f hf =
      AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) :=
  IsAdicComplete.of_comp_lift I (extend ha f) (factorPow_comp_extend ha f hf)

@[simp]
theorem mk_lift {n : ℕ} (x : M) :
    (Submodule.Quotient.mk (lift I ha f hf x)) = f n x := by
  simp only [lift, IsAdicComplete.lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp [extend_eq ha f hf]

@[simp]
theorem mkQ_comp_lift {n : ℕ} :
    mkQ (I ^ (a n) • ⊤ : Submodule R N) ∘ₗ (lift I ha f hf) = f n := by
  ext; simp

theorem eq_lift {F : M →ₗ[R] N}
    (hF : ∀ n, mkQ _ ∘ₗ F = f n) : F = lift I ha f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext I ha
  intro n m
  simp [← hF n]

end StrictMono

instance bot : IsAdicComplete (⊥ : Ideal R) M where

protected theorem subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.subsingleton

instance (priority := 100) of_subsingleton [Subsingleton M] : IsAdicComplete I M where

open Finset

theorem le_jacobson_bot [IsAdicComplete I R] : I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [← Ideal.neg_mem_iff, Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : ℕ → R := fun n => ∑ i ∈ range n, (x * y) ^ i
  have hf : ∀ m n, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [f, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← add_tsub_cancel_of_le h, Finset.sum_range_add, ← sub_sub, sub_self, zero_sub,
      @neg_mem_iff]
    apply Submodule.sum_mem
    intro n _
    rw [mul_pow, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hx m)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec toIsPrecomplete @hf
  rw [isUnit_iff_exists_inv]
  use L
  rw [← sub_eq_zero, neg_mul]
  apply IsHausdorff.haus (toIsHausdorff : IsHausdorff I R)
  intro n
  specialize hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL ⊢
  rw [sub_zero]
  suffices (1 - x * y) * f n - 1 ∈ I ^ n by
    convert Ideal.sub_mem _ this (Ideal.mul_mem_left _ (1 + -(x * y)) hL) using 1
    ring
  cases n
  · simp only [Ideal.one_eq_top, pow_zero, mem_top]
  · rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_comm (_ ^ _), ← sub_sub,
      sub_self, zero_sub, @neg_mem_iff, mul_pow]
    exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)

end IsAdicComplete
