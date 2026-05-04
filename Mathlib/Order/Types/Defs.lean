/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Order types

Order types are defined as the quotient of linear orders under order isomorphism.
They are preordered by order embeddings.

## Main definitions

* `OrderType`: the type of order types (in a given universe)
* `OrderType.type α`: given a type `α` with a linear order, this is the corresponding OrderType,

A preorder with a bottom element is registered on order types, where `⊥` is
`0`, the order type corresponding to the empty type.

## Notation

The following are notations in the `OrderType` namespace:

* `ω` is a notation for the order type of `ℕ` with its natural order.

## References

* <https://en.wikipedia.org/wiki/Order_type>
* [Dauben, J. W., Georg Cantor: His Mathematics and Philosophy of the Infinite. Princeton,
  NJ: Princeton University Press, 1990.][dauben_1990]
* [Enderton, Herbert B., Elements of Set Theory. United Kingdom: Academic Press,
  1977.][enderton_1977]

## Tags

order type, order isomorphism, linear order
-/

public noncomputable section

open Function Set Equiv Order

universe u v
variable {α β : Type u} [LinearOrder α] [LinearOrder β] {δ : Sort v}

/-- Equivalence relation on linear orders on arbitrary types in universe `u`, given by order
isomorphism. -/
@[implicit_reducible]
def OrderType.instSetoid : Setoid LinOrd where
  r := fun lin_ord₁ lin_ord₂ ↦ Nonempty (lin_ord₁ ≃o lin_ord₂)
  iseqv := ⟨fun _ ↦ ⟨.refl _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩⟩

/-- `OrderType.{u}` is the type of linear orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
def OrderType : Type (u + 1) :=
  Quotient OrderType.instSetoid

namespace OrderType

/-- A "canonical" type order-isomorphic to the order type `o`, living in the same universe.
This is defined through the axiom of choice. -/
def ToType (o : OrderType) : Type u :=
  o.out.carrier

/-- The instance for some arbitrary linear order on `Type u` , order isomorphic within
order type `o`. -/
@[no_expose]
instance (o : OrderType) : LinearOrder o.ToType :=
  o.out.str

/-! ### Basic properties of the order type -/

/-- The order type of the linear order on `α`. -/
def type (α : Type u) [LinearOrder α] : OrderType :=
  ⟦⟨α⟩⟧

instance : Zero OrderType where
  zero := type PEmpty

instance : Inhabited OrderType :=
  ⟨0⟩

instance : One OrderType where
  one := type PUnit

@[simp]
theorem type_toType (o : OrderType) : type o.ToType = o := surjInv_eq Quot.exists_rep o

theorem type_eq_type : type α = type β ↔ Nonempty (α ≃o β) :=
  Quotient.eq'

theorem type_congr (h : α ≃o β) : type α = type β :=
  type_eq_type.2 ⟨h⟩

alias _root_.OrderIso.type_congr := type_congr

@[simp]
theorem type_of_isEmpty [IsEmpty α] : type α = 0 :=
  type_congr <| .ofIsEmpty α PEmpty

theorem type_eq_zero : type α = 0 ↔ IsEmpty α where
  mp h :=
    let ⟨s⟩ := type_eq_type.1 h
    s.toEquiv.isEmpty
  mpr := @type_of_isEmpty α _

theorem type_ne_zero_iff : type α ≠ 0 ↔ Nonempty α := by simp [type_eq_zero]

@[simp]
theorem type_ne_zero [h : Nonempty α] : type α ≠ 0 :=
  type_ne_zero_iff.2 h

@[simp]
theorem type_of_unique [Nonempty α] [Subsingleton α] : type α = 1 := by
  cases nonempty_unique α
  exact (OrderIso.ofUnique α _).type_congr

theorem type_eq_one : type α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h ↦ let ⟨s⟩ := type_eq_type.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ ↦ type_of_unique⟩

@[simp]
private theorem isEmpty_toType_iff {o : OrderType} : IsEmpty o.ToType ↔ o = 0 := by
  rw [← @type_eq_zero o.ToType, type_toType]

@[simp]
private theorem nonempty_toType_iff {o : OrderType} : Nonempty o.ToType ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff o.ToType, type_toType]

instance : Nontrivial OrderType.{u} :=
  ⟨⟨1, 0, type_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to `OrderType`. -/
@[elab_as_elim]
theorem inductionOn {C : OrderType → Prop} (o : OrderType)
    (H : ∀ α [LinearOrder α], C (type α)) : C o :=
  Quot.inductionOn o (fun α ↦ H α)

/-- `Quotient.inductionOn₂` specialized to `OrderType`. -/
@[elab_as_elim]
theorem inductionOn₂ {C : OrderType → OrderType → Prop} (o₁ o₂ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β], C (type α) (type β)) : C o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun α β ↦ H α β

/-- `Quotient.inductionOn₃` specialized to `OrderType`. -/
@[elab_as_elim]
theorem inductionOn₃ {C : OrderType → OrderType → OrderType → Prop} (o₁ o₂ o₃ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β] γ [LinearOrder γ],
      C (type α) (type β) (type γ)) : C o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun α β γ ↦
    H α β γ

/-- To define a function on `OrderType`, it suffices to define it on all linear orders.
-/
def liftOn (o : OrderType) (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) : δ :=
  Quotient.liftOn o (fun w ↦ f w)
    fun w₁ w₂ h ↦ c w₁ w₂ (Quotient.sound h)

/-- `Quotient.liftOn₂` specialized to `OrderType`. -/
def liftOn₂ (o₁ o₂ : OrderType) (f : ∀ (α) [LinearOrder α] (β) [LinearOrder β], δ)
    (c : ∀ (α₁) [LinearOrder α₁] (β₁) [LinearOrder β₁] (α₂) [LinearOrder α₂] (β₂) [LinearOrder β₂],
      type α₁ = type α₂ → type β₁ = type β₂ → f α₁ β₁ = f α₂ β₂) : δ :=
  Quotient.liftOn₂ o₁ o₂ (fun w v ↦ f w v)
    fun w₁ w₂ v₁ v₂ hw hv ↦ c w₁ w₂ v₁ v₂ (Quotient.sound hw) (Quotient.sound hv)

@[simp]
theorem liftOn_type (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) {γ} [LinearOrder γ] :
    liftOn (type γ) f c = f γ := by rfl

@[simp]
theorem liftOn₂_type {α : Type u} {β : Type v} {δ : Type*} [LinearOrder α] [LinearOrder β]
     (f : ∀ (α) [LinearOrder α] (β) [LinearOrder β], δ)
     (c : ∀ (α₁) [LinearOrder α₁] (β₁) [LinearOrder β₁] (α₂) [LinearOrder α₂] (β₂) [LinearOrder β₂],
       type α₁ = type α₂ → type β₁ = type β₂ → f α₁ β₁ = f α₂ β₂) :
    liftOn₂ (type α) (type β) f c = f α β := by rfl

/-! ### The order on `OrderType` -/

/--
The order is defined so that `type α ≤ type β` iff there exists an order embedding `α ↪o β`.
-/
@[no_expose]
instance : Preorder OrderType where
  le o₁ o₂ :=
    Quotient.liftOn₂ o₁ o₂ (fun r s ↦ Nonempty (r ↪o s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ ↦ propext
      ⟨fun ⟨h⟩ ↦ ⟨(f.symm.toOrderEmbedding.trans h).trans g.toOrderEmbedding⟩, fun ⟨h⟩ ↦
        ⟨(f.toOrderEmbedding.trans h).trans g.symm.toOrderEmbedding⟩⟩
  le_refl o := inductionOn o fun α _ ↦ ⟨(OrderIso.refl _).toOrderEmbedding⟩
  le_trans o₁ o₂ o₃ := inductionOn₃ o₁ o₂ o₃ fun _ _ _ _ _ _ ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩

instance : NeZero (1 : OrderType) :=
  ⟨type_ne_zero⟩

theorem type_le_type_iff : type α ≤ type β ↔ Nonempty (α ↪o β) :=
  .rfl

theorem type_le_type (h : α ↪o β) : type α ≤ type β :=
  ⟨h⟩

theorem type_lt_type (h : α ↪o β) (hne : IsEmpty (β ↪o α)) : type α < type β :=
  ⟨⟨h⟩, not_nonempty_iff.mpr hne⟩

alias _root_.OrderEmbedding.type_le_type := type_le_type

@[simp]
protected theorem zero_le (o : OrderType) : 0 ≤ o :=
  inductionOn o fun _ ↦ OrderEmbedding.ofIsEmpty.type_le_type

instance : OrderBot OrderType where
  bot := 0
  bot_le := OrderType.zero_le

@[defeq, simp]
theorem bot_eq_zero : (⊥ : OrderType) = 0 :=
  rfl

@[simp]
protected theorem not_lt_zero {o : OrderType} : ¬o < 0 :=
  not_lt_bot

@[simp]
theorem pos_iff_ne_zero {o : OrderType} : 0 < o ↔ o ≠ 0 where
  mp := ne_bot_of_gt
  mpr ho := by
    have := nonempty_toType_iff.2 ho
    rw [← type_toType o]
    exact ⟨⟨Function.Embedding.ofIsEmpty, nofun⟩, fun ⟨f⟩ ↦ IsEmpty.elim inferInstance f.toFun⟩

/-- The universe lift operation on order types. You can specify the universes explicitly with
  `lift.{u, v} : OrderType.{v} → OrderType.{max v u}` -/
@[pp_with_univ]
def lift (o : OrderType.{v}) : OrderType.{max v u} :=
  o.liftOn (fun α _ ↦ type (ULift α)) fun _α _ _β _ e ↦
    ((ULift.orderIso.trans (type_eq_type.mp e).some).trans ULift.orderIso.symm).type_congr

@[simp]
theorem type_ulift : type (ULift.{v, u} α) = lift.{v} (type α) := (rfl)

/-- An order type lifted to a lower or equal universe equals itself. -/
theorem lift_id' (o : OrderType.{max u v}) : lift.{u} o = o :=
  inductionOn o fun _ ↦ type_congr ULift.orderIso

/-- An order type lifted to the same universe equals itself. -/
@[simp]
theorem lift_id (o : OrderType) : lift.{u, u} o = o :=
  lift_id'.{u, u} o

/-- An order type lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (o : OrderType.{u}) : lift.{0} o = o :=
  lift_id'.{0, u} o

@[simp]
theorem lift_lift.{u_1} (o : OrderType.{u_1}) : lift.{u} (lift.{v} o) = lift.{max v u} o :=
  inductionOn o fun _ ↦
    (ULift.orderIso.trans <| ULift.orderIso.trans ULift.orderIso.symm).type_congr

theorem lift_type_eq_iff : lift (type α) = lift (type β) ↔ Nonempty (α ≃o β) := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ congrArg lift <| type_congr h⟩
  rw [← type_ulift, ← type_ulift, type_eq_type] at h
  exact ⟨(ULift.orderIso.symm.trans h.some).trans ULift.orderIso⟩

theorem lift_type_le_iff : lift (type α) ≤ lift (type β) ↔ Nonempty (α ↪o β) := by
 refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ type_le_type <| (ULift.orderIso.toOrderEmbedding.trans h).trans
   ULift.orderIso.symm.toOrderEmbedding⟩
 rw [← type_ulift, ← type_ulift, type_le_type_iff] at h
 exact ⟨(ULift.orderIso.symm.toOrderEmbedding.trans h.some).trans ULift.orderIso.toOrderEmbedding⟩

/-- `ω` is the first infinite order type, defined as the order type of `ℕ`. -/
@[expose]
def omega0 : OrderType := lift <| type ℕ

@[inherit_doc]
scoped notation "ω" => OrderType.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

@[simp]
theorem type_nat : type ℕ = omega0 := type_congr ⟨Equiv.ulift.symm, @fun _ _ ↦ by
  simp only [ulift_symm_apply, ULift.up_le]⟩

end OrderType
