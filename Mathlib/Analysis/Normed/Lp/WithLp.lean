/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # The `WithLp` type synonym

`WithLp p V` is a copy of `V` with exactly the same vector space structure, but with the Lp norm
instead of any existing norm on `V`; recall that by default `ι → R` and `R × R` are equipped with
a norm defined as the supremum of the norms of their components.

This file defines the vector space structure for all types `V`; the norm structure is built for
different specializations of `V` in downstream files.

Note that this should not be used for infinite products, as in these cases the "right" Lp spaces is
not the same as the direct product of the spaces. See the docstring in `Mathlib/Analysis/PiLp` for
more details.

## Main definitions

* `WithLp p V`: a copy of `V` to be equipped with an L`p` norm.
* `WithLp.toLp`: the canonical inclusion from `V` to `WithLp p V`.
* `WithLp.ofLp`: the canonical inclusion from `WithLp p V` to `V`.
* `WithLp.linearEquiv p K V`: the canonical `K`-module isomorphism between `WithLp p V` and `V`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type (`ProdLp`, `PiLp`, etc), and allows all the structure-copying code
to be shared.

TODO: is it safe to copy across the topology and uniform space structure too for all reasonable
choices of `V`?
-/

@[expose] public section


open scoped ENNReal

/-- A type synonym for the given `V`, associated with the L`p` norm. Note that by default this just
forgets the norm structure on `V`; it is up to downstream users to implement the L`p` norm (for
instance, on `Prod` and finite `Pi` types). -/
structure WithLp (p : ℝ≥0∞) (V : Type*) where
  /-- Converts an element of `V` to an element of `WithLp p V`. -/
  toLp (p) ::
  /-- Converts an element of `WithLp p V` to an element of `V`. -/
  ofLp : V

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toLp p x` being printed as `{ ofLp := x }` by `delabStructureInstance`. -/
@[app_delab WithLp.toLp]
meta def WithLp.delabToLp : Delab := delabApp

end Notation

variable (p : ℝ≥0∞) (K K' : Type*) {K'' : Type*} (V : Type*) {V' V'' : Type*}

namespace WithLp

/-- `WithLp.ofLp` and `WithLp.toLp` as an equivalence. -/
@[simps]
protected def equiv : WithLp p V ≃ V where
  toFun := ofLp
  invFun := toLp p
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma equiv_symm_apply : ⇑(WithLp.equiv p V).symm = toLp p := rfl

/-! `WithLp p V` inherits various module-adjacent structures from `V`. -/

instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := (WithLp.equiv p V).nontrivial
instance instUnique [Unique V] : Unique (WithLp p V) := (WithLp.equiv p V).unique
instance instDecidableEq [DecidableEq V] : DecidableEq (WithLp p V) :=
  (WithLp.equiv p V).decidableEq

instance instAddCommGroup [AddCommGroup V] : AddCommGroup (WithLp p V) :=
  (WithLp.equiv p V).addCommGroup
@[to_additive] instance instSMul [SMul K V] : SMul K (WithLp p V) :=
  (WithLp.equiv p V).smul K
@[to_additive] instance instMulAction [Monoid K] [MulAction K V] : MulAction K (WithLp p V) :=
  fast_instance% (WithLp.equiv p V).mulAction K
instance instDistribMulAction [Monoid K] [AddCommGroup V] [DistribMulAction K V] :
    DistribMulAction K (WithLp p V) := fast_instance% (WithLp.equiv p V).distribMulAction K
instance instModule [Semiring K] [AddCommGroup V] [Module K V] : Module K (WithLp p V) :=
  fast_instance% (WithLp.equiv p V).module K

variable {K V}

@[defeq]
lemma ofLp_toLp (x : V) : ofLp (toLp p x) = x := rfl
@[defeq, simp] lemma toLp_ofLp (x : WithLp p V) : toLp p (ofLp x) = x := rfl

lemma ofLp_surjective : Function.Surjective (@ofLp p V) :=
  Function.RightInverse.surjective <| ofLp_toLp _

lemma toLp_surjective : Function.Surjective (@toLp p V) :=
  Function.RightInverse.surjective <| toLp_ofLp _

lemma ofLp_injective : Function.Injective (@ofLp p V) :=
  Function.LeftInverse.injective <| toLp_ofLp _

lemma toLp_injective : Function.Injective (@toLp p V) :=
  Function.LeftInverse.injective <| ofLp_toLp _

lemma ofLp_bijective : Function.Bijective (@ofLp p V) :=
  ⟨ofLp_injective p, ofLp_surjective p⟩

lemma toLp_bijective : Function.Bijective (@toLp p V) :=
  ⟨toLp_injective p, toLp_surjective p⟩

/-- Lift a function to `WithLp`. -/
@[simp]
protected def map (f : V → V') (x : WithLp p V) : WithLp p V' :=
  toLp p (f x.ofLp)

@[simp]
theorem map_id : WithLp.map p (id (α := V)) = id :=
  rfl

theorem map_comp (f : V' → V'') (g : V → V') :
    WithLp.map p (f ∘ g) = WithLp.map p f ∘ WithLp.map p g :=
  rfl

/-- Lift an equivalence to `WithLp`. -/
protected def congr (f : V ≃ V') : WithLp p V ≃ WithLp p V' :=
  (WithLp.equiv p V).trans <| f.trans <| (WithLp.equiv p V').symm

@[simp]
theorem coe_congr (f : V ≃ V') : ⇑(WithLp.congr p f) = WithLp.map p f :=
  rfl

@[simp]
theorem congr_refl : WithLp.congr p (Equiv.refl V) = Equiv.refl _ :=
  rfl

@[simp]
theorem congr_symm (f : V ≃ V') : (WithLp.congr p f).symm = WithLp.congr p f.symm :=
  rfl

theorem congr_trans (f : V ≃ V') (g : V' ≃ V'') :
    WithLp.congr p (f.trans g) = (WithLp.congr p f).trans (WithLp.congr p g) :=
  rfl

section AddCommGroup
variable [AddCommGroup V]

@[simp] lemma toLp_zero : toLp p (0 : V) = 0 := rfl
@[simp] lemma ofLp_zero : ofLp (0 : WithLp p V) = 0 := rfl

@[simp] lemma toLp_add (x y : V) : toLp p (x + y) = toLp p x + toLp p y := rfl
@[simp] lemma ofLp_add (x y : WithLp p V) : ofLp (x + y) = ofLp x + ofLp y := rfl

@[simp] lemma toLp_sub (x y : V) : toLp p (x - y) = toLp p x - toLp p y := rfl
@[simp] lemma ofLp_sub (x y : WithLp p V) : ofLp (x - y) = ofLp x - ofLp y := rfl

@[simp] lemma toLp_neg (x : V) : toLp p (-x) = -toLp p x := rfl
@[simp] lemma ofLp_neg (x : WithLp p V) : ofLp (-x) = -ofLp x := rfl

@[simp] lemma toLp_eq_zero {x : V} : toLp p x = 0 ↔ x = 0 := (toLp_injective p).eq_iff
@[simp] lemma ofLp_eq_zero {x : WithLp p V} : ofLp x = 0 ↔ x = 0 := (ofLp_injective p).eq_iff

end AddCommGroup

@[simp] lemma toLp_smul [SMul K V] (c : K) (x : V) : toLp p (c • x) = c • (toLp p x) := rfl
@[simp] lemma ofLp_smul [SMul K V] (c : K) (x : WithLp p V) : ofLp (c • x) = c • ofLp x := rfl

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
instance instIsScalarTower [SMul K K'] [SMul K V] [SMul K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) where
  smul_assoc x y z := by
    change toLp p ((x • y) • (ofLp z)) = toLp p (x • y • ofLp z)
    simp

@[to_additive]
instance instSMulCommClass [SMul K V] [SMul K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) where
  smul_comm x y z := by
    change toLp p (x • y • ofLp z) = toLp p (y • x • ofLp z)
    rw [smul_comm]

variable (K V)

/-- `WithLp.equiv` as a group isomorphism. -/
@[simps apply symm_apply]
protected def addEquiv [AddCommGroup V] : WithLp p V ≃+ V where
  toFun := ofLp
  invFun := toLp p
  map_add' := ofLp_add p

lemma coe_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V) = ofLp := rfl

lemma coe_symm_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V).symm = toLp p := rfl

@[simp]
lemma ofLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι → WithLp p V) :
    (∑ i ∈ s, f i).ofLp = ∑ i ∈ s, (f i).ofLp :=
  map_sum (WithLp.addEquiv _ _) _ _

@[simp]
lemma toLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι → V) :
    toLp p (∑ i ∈ s, f i) = ∑ i ∈ s, toLp p (f i) :=
  map_sum (WithLp.addEquiv _ _).symm _ _

@[simp]
lemma ofLp_listSum [AddCommGroup V] (l : List (WithLp p V)) :
    l.sum.ofLp = (l.map ofLp).sum :=
  map_list_sum (WithLp.addEquiv _ _) _

@[simp]
lemma toLp_listSum [AddCommGroup V] (l : List V) :
    toLp p l.sum = (l.map (toLp p)).sum :=
  map_list_sum (WithLp.addEquiv _ _).symm _

@[simp]
lemma ofLp_multisetSum [AddCommGroup V] (s : Multiset (WithLp p V)) :
    s.sum.ofLp = (s.map ofLp).sum :=
  map_multiset_sum (WithLp.addEquiv _ _) _

@[simp]
lemma toLp_multisetSum [AddCommGroup V] (s : Multiset V) :
    toLp p s.sum = (s.map (toLp p)).sum :=
  map_multiset_sum (WithLp.addEquiv _ _).symm _

/-- `WithLp.equiv` as a linear equivalence. -/
@[simps apply symm_apply]
protected def linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : WithLp p V ≃ₗ[K] V where
  __ := WithLp.addEquiv p V
  map_smul' _ _ := rfl

lemma coe_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V) = ofLp := rfl

lemma coe_symm_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V).symm = toLp p := rfl

@[simp]
lemma toAddEquiv_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    (WithLp.linearEquiv p K V).toAddEquiv = WithLp.addEquiv p V := rfl

instance instModuleFinite
    [Semiring K] [AddCommGroup V] [Module K V] [Module.Finite K V] :
    Module.Finite K (WithLp p V) :=
  Module.Finite.equiv (WithLp.linearEquiv p K V).symm

end WithLp

section

variable {K K' V} [Semiring K] [Semiring K'] [Semiring K'']
  {σ : K →+* K'} {σ' : K' →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {τ : K' →+* K''} {τ' : K'' →+* K'} [RingHomInvPair τ τ'] [RingHomInvPair τ' τ]
  {ρ : K →+* K''} {ρ' : K'' →+* K} [RingHomInvPair ρ ρ'] [RingHomInvPair ρ' ρ]
  [RingHomCompTriple σ τ ρ] [RingHomCompTriple τ' σ' ρ']
  [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V'] [AddCommGroup V''] [Module K'' V'']

namespace LinearMap

/-- Lift a (semi)linear map to `WithLp`. -/
def withLpMap (f : V →ₛₗ[σ] V') : WithLp p V →ₛₗ[σ] WithLp p V' :=
  (WithLp.linearEquiv p K' V').symm.toLinearMap ∘ₛₗ f ∘ₛₗ (WithLp.linearEquiv p K V).toLinearMap

@[simp]
theorem coe_withLpMap (f : V →ₛₗ[σ] V') : ⇑(withLpMap p f) = WithLp.map p f :=
  rfl

@[simp]
theorem withLpMap_id : withLpMap p (LinearMap.id (R := K) (M := V)) = LinearMap.id :=
  rfl

@[simp]
theorem withLpMap_comp (f : V' →ₛₗ[τ] V'') (g : V →ₛₗ[σ] V') :
    withLpMap p (f ∘ₛₗ g) = withLpMap p f ∘ₛₗ withLpMap p g :=
  rfl

end LinearMap

namespace LinearEquiv

/-- Lift a (semi)linear equivalence to `WithLp`. -/
def withLpCongr (f : V ≃ₛₗ[σ] V') : WithLp p V ≃ₛₗ[σ] WithLp p V' :=
  (WithLp.linearEquiv p K V).trans <| f.trans <| (WithLp.linearEquiv p K' V').symm

@[simp]
theorem coe_withLpCongr (f : V ≃ₛₗ[σ] V') : ⇑(withLpCongr p f) = WithLp.map p f :=
  rfl

@[simp]
theorem withLpCongr_symm (f : V ≃ₛₗ[σ] V') : (withLpCongr p f).symm = withLpCongr p f.symm :=
  rfl

@[simp]
theorem withLpCongr_refl :
    withLpCongr p (LinearEquiv.refl K V) = LinearEquiv.refl K _ :=
  rfl

theorem withLpCongr_trans (f : V ≃ₛₗ[σ] V') (g : V' ≃ₛₗ[τ] V'') :
    withLpCongr p (f.trans g) = (withLpCongr p f).trans (withLpCongr p g) :=
  rfl

end LinearEquiv

end
