/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.Lift
public import Mathlib.Data.Int.Notation

/-!
# Equivalence between types

In this file we continue the work on equivalences begun in `Mathlib/Logic/Equiv/Defs.lean`, defining
a lot of equivalences between various types and operations on these equivalences.

More definitions of this kind can be found in other files.
E.g., `Mathlib/Algebra/Equiv/TransferInstance.lean` does it for many algebraic type classes like
`Group`, `Module`, etc.

## Tags

equivalence, congruence, bijective map
-/

@[expose] public section

universe u v w z

open Function

-- Unless required to be `Type*`, all variables in this file are `Sort*`
variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

/-- The product over `Option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
def piOptionEquivProd {α} {β : Option α → Type*} :
    (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a) where
  toFun f := (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl

section subtypeCongr

/-- Combines an `Equiv` between two subtypes with an `Equiv` between their complements to form a
  permutation. -/
def subtypeCongr {α} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α :=
  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))

variable {ε : Type*} {p : ε → Prop} [DecidablePred p]
variable (ep ep' : Perm { a // p a }) (en en' : Perm { a // ¬p a })

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def Perm.subtypeCongr : Equiv.Perm ε :=
  permCongr (sumCompl p) (sumCongr ep en)

theorem Perm.subtypeCongr.apply (a : ε) : ep.subtypeCongr en a =
    if h : p a then (ep ⟨a, h⟩ : ε) else en ⟨a, h⟩ := by
  by_cases h : p a <;> simp [Perm.subtypeCongr, h]

@[simp]
theorem Perm.subtypeCongr.left_apply {a : ε} (h : p a) : ep.subtypeCongr en a = ep ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]

@[simp]
theorem Perm.subtypeCongr.left_apply_subtype (a : { a // p a }) : ep.subtypeCongr en a = ep a :=
    Perm.subtypeCongr.left_apply ep en a.property

@[simp]
theorem Perm.subtypeCongr.right_apply {a : ε} (h : ¬p a) : ep.subtypeCongr en a = en ⟨a, h⟩ := by
  simp [Perm.subtypeCongr.apply, h]

@[simp]
theorem Perm.subtypeCongr.right_apply_subtype (a : { a // ¬p a }) : ep.subtypeCongr en a = en a :=
  Perm.subtypeCongr.right_apply ep en a.property

@[simp]
theorem Perm.subtypeCongr.refl :
    Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε := by
  ext x
  by_cases h : p x <;> simp [h]

@[simp]
theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm := by
  ext x
  by_cases h : p x
  · have : p (ep.symm ⟨x, h⟩) := Subtype.property _
    simp [h, symm_apply_eq, this]
  · have : ¬p (en.symm ⟨x, h⟩) := Subtype.property (en.symm _)
    simp [h, symm_apply_eq, this]

@[simp]
theorem Perm.subtypeCongr.trans :
    (ep.subtypeCongr en).trans (ep'.subtypeCongr en')
    = Perm.subtypeCongr (ep.trans ep') (en.trans en') := by
  ext x
  by_cases h : p x
  · have : p (ep ⟨x, h⟩) := Subtype.property _
    simp [h, this]
  · have : ¬p (en ⟨x, h⟩) := Subtype.property (en _)
    simp [h, this]

end subtypeCongr

section subtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtypePreimage : { x : α → β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } → β) where
  toFun (x : { x : α → β // x ∘ Subtype.val = x₀ }) a := (x : α → β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨_, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.val_injective <|
      funext fun a => by
        dsimp only
        split_ifs
        · rw [← hx]; rfl
        · rfl
  right_inv x :=
    funext fun ⟨a, h⟩ =>
      show dite (p a) _ _ = _ by
        dsimp only
        rw [dif_neg h]

theorem subtypePreimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h

theorem subtypePreimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h

end subtypePreimage

section

/-- A family of equivalences `∀ a, β₁ a ≃ β₂ a` generates an equivalence between `∀ a, β₁ a` and
`∀ a, β₂ a`. -/
@[simps (attr := grind =)]
def piCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ (∀ a, β₂ a) :=
  ⟨Pi.map fun a ↦ F a, Pi.map fun a ↦ (F a).symm, fun H => funext <| by simp,
    fun H => funext <| by simp⟩

@[simp]
lemma piCongrRight_refl {β : α → Sort*} : piCongrRight (fun a ↦ .refl (β a)) = .refl (∀ a, β a) :=
  rfl

/-- Given `φ : α → β → Sort*`, we have an equivalence between `∀ a b, φ a b` and `∀ b a, φ a b`.
This is `Function.swap` as an `Equiv`. -/
@[simps apply]
def piComm (φ : α → β → Sort*) : (∀ a b, φ a b) ≃ ∀ b a, φ a b :=
  ⟨swap, swap, fun _ => rfl, fun _ => rfl⟩

@[simp]
theorem piComm_symm {φ : α → β → Sort*} : (piComm φ).symm = (piComm <| swap φ) :=
  rfl

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `Sigma.curry` and `Sigma.uncurry` together as an equiv. -/
def piCurry {α} {β : α → Type*} (γ : ∀ a, β a → Type*) :
    (∀ x : Σ i, β i, γ x.1 x.2) ≃ ∀ a b, γ a b where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry

-- `simps` overapplies these but `simps -fullyApplied` under-applies them
@[simp] theorem piCurry_apply {α} {β : α → Type*} (γ : ∀ a, β a → Type*)
    (f : ∀ x : Σ i, β i, γ x.1 x.2) :
    piCurry γ f = Sigma.curry f :=
  rfl

@[simp] theorem piCurry_symm_apply {α} {β : α → Type*} (γ : ∀ a, β a → Type*) (f : ∀ a b, γ a b) :
    (piCurry γ).symm f = Sigma.uncurry f :=
  rfl

end

section prodCongr

variable {α₁ α₂ β₁ β₂ : Type*} (e : α₁ → β₁ ≃ β₂)

-- See also `Equiv.ofPreimageEquiv`.
/-- A family of equivalences between fibers gives an equivalence between domains. -/
@[simps!]
def ofFiberEquiv {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
  (sigmaFiberEquiv f).symm.trans <| (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)

theorem ofFiberEquiv_map {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).property

end prodCongr

section

open Sum

/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
def sigmaNatSucc (f : ℕ → Type u) : (Σ n, f n) ≃ f 0 ⊕ Σ n, f (n + 1) :=
  ⟨fun x =>
    @Sigma.casesOn ℕ f (fun _ => f 0 ⊕ Σ n, f (n + 1)) x fun n =>
      @Nat.casesOn (fun i => f i → f 0 ⊕ Σ n : ℕ, f (n + 1)) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩

end

section

open Sum Nat

/-- The set of natural numbers is equivalent to `ℕ ⊕ PUnit`. -/
def natEquivNatSumPUnit : ℕ ≃ ℕ ⊕ PUnit where
  toFun n := Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- `ℕ ⊕ PUnit` is equivalent to `ℕ`. -/
def natSumPUnitEquivNat : ℕ ⊕ PUnit ≃ ℕ :=
  natEquivNatSumPUnit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ ℕ ⊕ ℕ where
  toFun z := Int.casesOn z inl inr
  invFun := Sum.elim Int.ofNat Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl

end

/-- If `α` is equivalent to `β`, then `Unique α` is equivalent to `Unique β`. -/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where
  toFun h := @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `α` is equivalent to `β`, then `IsEmpty α` is equivalent to `IsEmpty β`. -/
theorem isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩

protected theorem isEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.isEmpty_congr.mpr ‹_›

section

open Subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `Perm.subtypePerm`. -/
@[simps apply]
def subtypeEquiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ { b : β // q b } where
  toFun a := ⟨e a, (h _).mp a.property⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.property)⟩
  left_inv a := Subtype.ext <| by simp
  right_inv b := Subtype.ext <| by simp

lemma coe_subtypeEquiv_eq_map {X Y} {p : X → Prop} {q : Y → Prop} (e : X ≃ Y)
    (h : ∀ x, p x ↔ q (e x)) : ⇑(e.subtypeEquiv h) = Subtype.map e (h · |>.mp) :=
  rfl

@[simp]
theorem subtypeEquiv_refl {p : α → Prop} (h : ∀ a, p a ↔ p (Equiv.refl _ a) := fun _ => Iff.rfl) :
    (Equiv.refl α).subtypeEquiv h = Equiv.refl { a : α // p a } := by
  ext
  rfl

-- We use `as_aux_lemma` here to avoid creating large proof terms when using `simp`
@[simp]
theorem subtypeEquiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) :
    (e.subtypeEquiv h).symm = e.symm.subtypeEquiv (by as_aux_lemma => grind) :=
  rfl

@[simp]
theorem subtypeEquiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : ∀ a : α, p a ↔ q (e a)) (h' : ∀ b : β, q b ↔ r (f b)) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h')
    = (e.trans f).subtypeEquiv (by as_aux_lemma => exact fun a => (h a).trans (h' <| e a)) :=
  rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps!]
def subtypeEquivRight {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equiv.refl _) e

lemma subtypeEquivRight_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // p x }) : subtypeEquivRight e z = ⟨z, (e z.1).mp z.2⟩ := rfl

lemma subtypeEquivRight_symm_apply {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    (z : { x // q x }) : (subtypeEquivRight e).symm z = ⟨z, (e z.1).mpr z.2⟩ := rfl

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtypeEquivOfSubtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtypeEquiv e <| by simp

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtypeEquivOfSubtype' {p : α → Prop} (e : α ≃ β) :
    { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtypeEquivProp {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equiv.refl α) fun _ => h ▸ Iff.rfl

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
def subtypeSubtypeEquivSubtypeExists (p : α → Prop) (q : Subtype p → Prop) :
    Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a.1, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps!]
def subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α → Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtypeSubtypeEquivSubtypeExists p _).trans <|
    subtypeEquivRight fun x => @exists_prop (q x) (p x)

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps!]
def subtypeSubtypeEquivSubtype {α} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtypeSubtypeEquivSubtypeInter p _).trans <| subtypeEquivRight fun _ => and_iff_right_of_imp h

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symm_apply]
def subtypeUnivEquiv {α} {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun _ => Subtype.ext rfl, fun _ => rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtypeSigmaEquiv {α} (p : α → Type v) (q : α → Prop) : { y : Sigma p // q y.1 } ≃ Σ x :
    Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun _ => rfl,
    fun _ => rfl⟩

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigmaSubtypeEquivOfSubset {α} (p : α → Type v) (q : α → Prop) (h : ∀ x, p x → q x) :
    (Σ x : Subtype q, p x) ≃ Σ x : α, p x :=
  (subtypeSigmaEquiv p q).symm.trans <| subtypeUnivEquiv fun x => h x.1 x.2

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigmaSubtypeFiberEquiv {α β : Type*} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
    (Σ y : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σ y : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun _ ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigmaSubtypeFiberEquivSubtype {α β : Type*} (f : α → β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (f x)) : (Σ y : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σ y : Subtype q, { x : α // f x = y }) ≃ Σ y :
        Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } := by {
          apply sigmaCongrRight
          intro y
          apply Equiv.symm
          refine (subtypeSubtypeEquivSubtypeExists _ _).trans (subtypeEquivRight ?_)
          intro x
          exact ⟨fun ⟨hp, h'⟩ => congr_arg Subtype.val h', fun h' => ⟨(h x).2 (h'.symm ▸ y.2),
            Subtype.ext h'⟩⟩ }
    _ ≃ Subtype p := sigmaFiberEquiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)

/-- A sigma type over an `Option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigmaOptionEquivOfSome {α} (p : Option α → Type v) (h : p none → False) :
    (Σ x : Option α, p x) ≃ Σ x : α, p (some x) :=
  haveI h' : ∀ x, p x → x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n
    · intro _
      exact rfl
  (sigmaSubtypeEquivOfSubset _ _ h').symm.trans (sigmaCongrLeft' (optionIsSomeEquiv α))

/-- The `Pi`-type `∀ i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`Sigma` type such that for all `i` we have `(f i).fst = i`. -/
def piEquivSubtypeSigma (ι) (π : ι → Type*) :
    (∀ i, π i) ≃ { f : ι → Σ i, π i // ∀ i, (f i).1 = i } where
  toFun := fun f => ⟨fun i => ⟨i, f i⟩, fun _ => rfl⟩
  invFun := fun f i => by rw [← f.2 i]; exact (f.1 i).2
  right_inv := fun ⟨f, hf⟩ =>
    Subtype.ext <| funext fun i =>
      Sigma.eq (hf i).symm <| eq_of_heq <| rec_heq_of_heq _ <| by simp

/-- The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the type of functions `∀ a, {b : β a // p a b}`. -/
def subtypePiEquivPi {β : α → Sort v} {p : ∀ a, β a → Prop} :
    { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } where
  toFun := fun f a => ⟨f.1 a, f.2 a⟩
  invFun := fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv := by
    rintro ⟨f, h⟩
    rfl
  right_inv := by
    rintro f
    funext a
    exact Subtype.ext rfl

/-- A sigma of a sigma whose second base does not depend on the first is equivalent
to a sigma whose base is a product. -/
@[simps!]
def sigmaAssocProd {α β : Type*} {γ : α → β → Type*} :
    (ab : α × β) × γ ab.1 ab.2 ≃ (a : α) × (b : β) × γ a b :=
  sigmaCongrLeft' (sigmaEquivProd _ _).symm |>.trans <| sigmaAssoc γ

/-- A subtype of a sigma which pins down the base of the sigma is equivalent to
the respective fiber. -/
@[simps]
def sigmaSubtype {α : Type*} {β : α → Type*} (a : α) :
    {s : Sigma β // s.1 = a} ≃ β a where
  toFun := fun ⟨⟨_, b⟩, h⟩ => h ▸ b
  invFun b := ⟨⟨a, b⟩, rfl⟩
  left_inv := fun ⟨a, h⟩ ↦ by cases h; simp
  right_inv b := by simp


section
attribute [local simp] Trans.trans sigmaAssoc subtypeSigmaEquiv uniqueSigma eqRec_eq_cast

/-- A subtype of a dependent triple which pins down both bases is equivalent to the
respective fiber. -/
@[simps! +simpRhs apply]
def sigmaSigmaSubtype {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    (p : (a : α) × β a → Prop) [uniq : Unique {ab // p ab}] {a : α} {b : β a} (h : p ⟨a, b⟩) :
    {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩} ≃ γ a b :=
  calc {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩}
  _ ≃ _ := subtypeEquiv (p := fun ⟨a, b, c⟩ ↦ p ⟨a, b⟩) (q := (p ·.1))
    (sigmaAssoc γ).symm fun s ↦ by simp [sigmaAssoc]
  _ ≃ _ := subtypeSigmaEquiv _ _
  _ ≃ _ := uniqueSigma (fun ab ↦ γ (Sigma.fst <| Subtype.val ab) (Sigma.snd <| Subtype.val ab))
  _ ≃ γ a b := Equiv.cast <| by rw [← show ⟨⟨a, b⟩, h⟩ = uniq.default from uniq.uniq _]

@[simp]
lemma sigmaSigmaSubtype_symm_apply {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    (p : (a : α) × β a → Prop) [uniq : Unique {ab // p ab}]
    {a : α} {b : β a} (c : γ a b) (h : p ⟨a, b⟩) :
    (sigmaSigmaSubtype p h).symm c = ⟨⟨a, ⟨b, c⟩⟩, h⟩ := by
  rw [Equiv.symm_apply_eq]; simp

/-- A specialization of `sigmaSigmaSubtype` to the case where the second base
does not depend on the first, and the property being checked for is simple
equality. Useful e.g. when `γ` is `Hom` inside a category. -/
def sigmaSigmaSubtypeEq {α β : Type*} {γ : α → β → Type*} (a : α) (b : β) :
    {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b} ≃ γ a b :=
  have : Unique (@Subtype ((_ : α) × β) (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b)) := {
    default := ⟨⟨a, b⟩, ⟨rfl, rfl⟩⟩
    uniq := by rintro ⟨⟨a', b'⟩, ⟨rfl, rfl⟩⟩; rfl }
  sigmaSigmaSubtype (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b) ⟨rfl, rfl⟩

@[simp]
lemma sigmaSigmaSubtypeEq_apply {α β : Type*} {γ : α → β → Type*} {a : α} {b : β}
    (s : {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b}) :
    sigmaSigmaSubtypeEq a b s = cast (congrArg₂ γ s.2.1 s.2.2) s.1.2.2 := by
  simp [sigmaSigmaSubtypeEq]

@[simp]
lemma sigmaSigmaSubtypeEq_symm_apply {α β : Type*} {γ : α → β → Type*} {a : α} {b : β} (c : γ a b) :
    (sigmaSigmaSubtypeEq a b).symm c = ⟨⟨a, ⟨b, c⟩⟩, ⟨rfl, rfl⟩⟩ := by
  simp [sigmaSigmaSubtypeEq]

end

end

section subtypeEquivCodomain

variable {X Y : Sort*} [DecidableEq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    { g : X → Y // g ∘ (↑) = f } ≃ Y :=
  (subtypePreimage _ f).trans <|
    @funUnique { x' // ¬x' ≠ x } _ <|
      show Unique { x' // ¬x' ≠ x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from {
            default := ⟨x, rfl⟩, uniq := fun ⟨_, h⟩ => Subtype.val_injective h })
          (subtypeEquivRight fun _ => not_not)

@[simp]
theorem coe_subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    (subtypeEquivCodomain f : _ → Y) =
      fun g : { g : X → Y // g ∘ (↑) = f } => (g : X → Y) x :=
  rfl

@[simp]
theorem subtypeEquivCodomain_apply (f : { x' // x' ≠ x } → Y) (g) :
    subtypeEquivCodomain f g = (g : X → Y) x :=
  rfl

theorem coe_subtypeEquivCodomain_symm (f : { x' // x' ≠ x } → Y) :
    ((subtypeEquivCodomain f).symm : Y → _) = fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y, by grind⟩ :=
  rfl

@[simp]
theorem subtypeEquivCodomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl

theorem subtypeEquivCodomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)

theorem subtypeEquivCodomain_symm_apply_ne
    (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) (h : x' ≠ x) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h

end subtypeEquivCodomain

instance : CanLift (α → β) (α ≃ β) (↑) Bijective where prf f hf := ⟨ofBijective f hf, rfl⟩

section

variable {α' β' : Type*} (e : Perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/-- Extend the domain of `e : Equiv.Perm α` to one that is over `β` via `f : α → Subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `Set.range f` fixed. For this use-case `Equiv` given by `f` can
be constructed by `Equiv.of_leftInverse'` or `Equiv.of_leftInverse` when there is a known
inverse, or `Equiv.ofInjective` in the general case.
-/
def Perm.extendDomain : Perm β' :=
  (permCongr f e).subtypeCongr (Equiv.refl _)

@[simp]
theorem Perm.extendDomain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by
  simp [Perm.extendDomain]

theorem Perm.extendDomain_apply_subtype {b : β'} (h : p b) :
    e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by
  simp [Perm.extendDomain, h]

theorem Perm.extendDomain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [Perm.extendDomain, h]

@[simp]
theorem Perm.extendDomain_refl : Perm.extendDomain (Equiv.refl _) f = Equiv.refl _ := by
  simp [Perm.extendDomain]

@[simp]
theorem Perm.extendDomain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl

theorem Perm.extendDomain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [Perm.extendDomain, permCongr_trans]

end

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtypeQuotientEquivQuotientSubtype (p₁ : α → Prop) {s₁ : Setoid α} {s₂ : Setoid (Subtype p₁)}
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂.r x y ↔ s₁.r x y) : {x // p₂ x} ≃ Quotient s₂ where
  toFun a :=
    Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab => hfunext (by rw [Quotient.sound hab]) fun _ _ _ =>
        heq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun _ _ hab =>
      Subtype.ext (Quotient.sound ((h _ _).1 hab))
  left_inv := by exact fun ⟨a, ha⟩ => Quotient.inductionOn a (fun b hb => rfl) ha
  right_inv a := by exact Quotient.inductionOn a fun ⟨a, ha⟩ => rfl

@[simp]
theorem subtypeQuotientEquivQuotientSubtype_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y)
    (x hx) : subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl

@[simp]
theorem subtypeQuotientEquivQuotientSubtype_symm_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y) (x) :
    (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.property⟩ :=
  rfl

section Swap

variable [DecidableEq α]

/-- A helper function for `Equiv.swap`. -/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r

theorem swapCore_self (r a : α) : swapCore a a r = r := by
  unfold swapCore
  split_ifs <;> simp [*]

theorem swapCore_swapCore (r a b : α) : swapCore a b (swapCore a b r) = r := by
  unfold swapCore; split_ifs <;> grind

theorem swapCore_comm (r a b : α) : swapCore a b r = swapCore b a r := by
  unfold swapCore; split_ifs <;> grind

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b,
    fun r => swapCore_swapCore r a b⟩

@[simp]
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext fun r => swapCore_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swapCore_comm r _ _

@[aesop simp, grind =]
theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl

@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl

@[simp]
theorem swap_apply_right (a b : α) : swap a b b = a := by
  grind

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x := by
  grind

theorem eq_or_eq_of_swap_apply_ne_self {a b x : α} (h : swap a b x ≠ x) : x = a ∨ x = b := by
  contrapose! h
  exact swap_apply_of_ne_of_ne h.1 h.2

@[simp]
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext fun _ => swapCore_swapCore _ _ _

@[simp]
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl

@[simp]
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y :=
  ⟨fun h => (Equiv.refl _).injective (by grind), by grind⟩

theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x := by
  cases π
  rfl

theorem swap_eq_update (i j : α) : (Equiv.swap i j : α → α) = update (update id j i) i j := by
  grind

theorem comp_swap_eq_update (i j : α) (f : α → β) :
    f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) := by
  grind

@[simp]
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) := by
  grind

@[simp]
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm

@[simp]
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  grind

/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) :
    v (swap i j k) = v k := by
  grind

theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  grind

theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) := by
  grind

namespace Perm

@[simp]
theorem sumCongr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) := by
  aesop

@[simp]
theorem sumCongr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  aesop

end Perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f

@[simp]
theorem setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b := by
  simp [setValue, swap_apply_left]

end Swap

end Equiv

namespace Function.Involutive

/-- Convert an involutive function `f` to a permutation with `toFun = invFun = f`. -/
def toPerm (f : α → α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.leftInverse, h.rightInverse⟩

@[simp]
theorem coe_toPerm {f : α → α} (h : Involutive f) : (h.toPerm f : α → α) = f :=
  rfl

@[simp]
theorem toPerm_symm {f : α → α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl

theorem toPerm_involutive {f : α → α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h

theorem symm_eq_self_of_involutive (f : Equiv.Perm α) (h : Involutive f) : f.symm = f :=
  DFunLike.coe_injective (h.leftInverse_iff.mp f.left_inv)

end Function.Involutive

theorem PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply

theorem Function.Injective.map_swap [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) :
    f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) := by
  conv_rhs => rw [Equiv.swap_apply_def]
  split_ifs with h₁ h₂
  · -- We can't yet use `grind` here because of https://github.com/leanprover/lean4/issues/11088
    rw [hf h₁, Equiv.swap_apply_left]
  · rw [hf h₂, Equiv.swap_apply_right]
  · grind

namespace Equiv

section

/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps apply, simps -isSimp symm_apply]
def piCongrLeft' (P : α → Sort*) (e : α ≃ β) : (∀ a, P a) ≃ ∀ b, P (e.symm b) where
  toFun f x := f (e.symm x)
  invFun f x := (e.symm_apply_apply x).ndrec (f (e x))
  left_inv f := by grind
  right_inv f := by grind

/-- Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't typecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. For that reason,
we have to explicitly substitute along `e.symm (e a) = a` in the statement of this lemma. -/
add_decl_doc Equiv.piCongrLeft'_symm_apply

/-- This lemma is impractical to state in the dependent case. -/
@[simp]
theorem piCongrLeft'_symm (P : Sort*) (e : α ≃ β) :
    (piCongrLeft' (fun _ => P) e).symm = piCongrLeft' _ e.symm := by ext; simp [piCongrLeft']

/-- Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't typecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. This lemma is a way
around it in the case where `a` is of the form `e.symm b`, so we can use `g b` instead of
`g (e (e.symm b))`. -/
@[simp]
lemma piCongrLeft'_symm_apply_apply (P : α → Sort*) (e : α ≃ β) (g : ∀ b, P (e.symm b)) (b : β) :
    (piCongrLeft' P e).symm g (e.symm b) = g b := by
  rw [piCongrLeft'_symm_apply, ← heq_iff_eq, eqRec_heq_iff_heq]
  exact congr_arg_heq _ (e.apply_symm_apply _)

@[simp]
lemma piCongrLeft'_refl (P : α → Sort*) : piCongrLeft' P (.refl α) = .refl (∀ a, P a) := rfl

end

section

variable (P : β → Sort w) (e : α ≃ β)

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def piCongrLeft : (∀ a, P (e a)) ≃ ∀ b, P b :=
  (piCongrLeft' P e.symm).symm

/-- Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typecheck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. For that reason,
we have to explicitly substitute along `e (e.symm b) = b` in the statement of this lemma. -/
lemma piCongrLeft_apply (f : ∀ a, P (e a)) (b : β) :
    (piCongrLeft P e) f b = e.apply_symm_apply b ▸ f (e.symm b) :=
  rfl

@[simp, grind =]
lemma piCongrLeft_symm_apply (g : ∀ b, P b) (a : α) :
    (piCongrLeft P e).symm g a = g (e a) :=
  piCongrLeft'_apply P e.symm g a

@[simp]
lemma piCongrLeft_refl (P : α → Sort*) : piCongrLeft P (.refl α) = .refl (∀ a, P a) :=
  rfl

/-- Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typecheck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. This lemma is a way
around it in the case where `b` is of the form `e a`, so we can use `f a` instead of
`f (e.symm (e a))`. -/
@[simp, grind =]
lemma piCongrLeft_apply_apply (f : ∀ a, P (e a)) (a : α) :
    (piCongrLeft P e) f (e a) = f a :=
  piCongrLeft'_symm_apply_apply P e.symm f a

open Sum

lemma piCongrLeft_apply_eq_cast {P : β → Sort v} {e : α ≃ β}
    (f : (a : α) → P (e a)) (b : β) :
    piCongrLeft P e f b = cast (congr_arg P (e.apply_symm_apply b)) (f (e.symm b)) :=
  eqRec_eq_cast _ _

theorem piCongrLeft_sumInl {ι ι' ι''} (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inl i)) = f i := by
  grind

theorem piCongrLeft_sumInr {ι ι' ι''} (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inr j)) = g j := by
  grind

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ a : α, W a ≃ Z (h₁ a))

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def piCongr : (∀ a, W a) ≃ ∀ b, Z b :=
  (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)

@[simp]
theorem coe_piCongr_symm :
    ((h₁.piCongr h₂).symm : (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp, grind =]
theorem piCongr_symm_apply (f : ∀ b, Z b) :
    (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp, grind =]
theorem piCongr_apply_apply (f : ∀ a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) := by
  rw [piCongr, trans_apply, piCongrLeft_apply_apply, piCongrRight_apply, Pi.map_apply]

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ b : β, W (h₁.symm b) ≃ Z b)

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def piCongr' : (∀ a, W a) ≃ ∀ b, Z b :=
  (piCongr h₁.symm fun b => (h₂ b).symm).symm

@[simp]
theorem coe_piCongr' :
    (h₁.piCongr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b <| f <| h₁.symm b :=
  rfl

theorem piCongr'_apply (f : ∀ a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b <| f <| h₁.symm b :=
  rfl

@[simp]
theorem piCongr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) := by
  simp [piCongr', piCongr_apply_apply]

end

/-- Transport dependent functions through an equality of sets. -/
@[simps!] def piCongrSet {α} {W : α → Sort w} {s t : Set α} (h : s = t) :
    (∀ i : {i // i ∈ s}, W i) ≃ (∀ i : {i // i ∈ t}, W i) where
  toFun f i := f ⟨i, h ▸ i.2⟩
  invFun f i := f ⟨i, h.symm ▸ i.2⟩

lemma eq_conj {α α' β β' : Sort*} (ε₁ : α ≃ α') (ε₂ : β' ≃ β)
    (f : α → β) (f' : α' → β') : ε₂.symm ∘ f ∘ ε₁.symm = f' ↔ f = ε₂ ∘ f' ∘ ε₁ := by
  rw [Equiv.symm_comp_eq, Equiv.comp_symm_eq, Function.comp_assoc]

section BinaryOp

variable {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

theorem semiconj_conj (f : α₁ → α₁) : Semiconj e f (e.conj f) := fun x => by simp

theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by simp [arrowCongr]

instance [Std.Associative f] : Std.Associative (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isAssociative_right e.surjective

instance [Std.IdempotentOp f] : Std.IdempotentOp (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isIdempotent_right e.surjective

end BinaryOp

section ULift

@[simp]
theorem ulift_symm_down {α} (x : α) : (Equiv.ulift.{u, v}.symm x).down = x :=
  rfl

end ULift

end Equiv

theorem Function.Injective.swap_apply
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  Eq.symm (map_swap hf x y z)

theorem Function.Injective.swap_comp
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext fun _ => hf.swap_apply _ _ _

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
functions between them. -/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A nonempty subsingleton type is (noncomputably) equivalent to `PUnit`. -/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton [h : Nonempty α] [Subsingleton α] :
    α ≃ PUnit :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

/-- `Unique (Unique α)` is equivalent to `Unique α`. -/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }

/-- If `Unique β`, then `Unique α` is equivalent to `α ≃ β`. -/
def uniqueEquivEquivUnique (α : Sort u) (β : Sort v) [Unique β] : Unique α ≃ (α ≃ β) :=
  equivOfSubsingletonOfSubsingleton (fun _ => Equiv.ofUnique _ _) Equiv.unique

namespace Function

variable {α' : Sort*}

theorem update_comp_equiv [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) :
    update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]

theorem update_apply_equiv_apply [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'

theorem piCongrLeft'_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ a, P a) (b : β) (x : P (e.symm b)) :
    e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x := by
  ext b'
  rcases eq_or_ne b' b with (rfl | h) <;> simp_all

theorem piCongrLeft'_symm_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [(e.piCongrLeft' P).symm_apply_eq, piCongrLeft'_update]

end Function
