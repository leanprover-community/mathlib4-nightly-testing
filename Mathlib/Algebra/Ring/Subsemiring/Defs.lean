/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `subtype` and `inclusion`
ring homomorphisms.
-/

@[expose] public section

assert_not_exists RelIso

universe u v w

section AddSubmonoidWithOneClass

/-- `AddSubmonoidWithOneClass S R` says `S` is a type of subsets `s ≤ R` that contain `0`, `1`,
and are closed under `(+)` -/
class AddSubmonoidWithOneClass (S : Type*) (R : outParam Type*) [AddMonoidWithOne R]
  [SetLike S R] : Prop extends AddSubmonoidClass S R, OneMemClass S R

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

@[simp, aesop safe (rule_sets := [SetLike])]
theorem natCast_mem [AddSubmonoidWithOneClass S R] (n : ℕ) : (n : R) ∈ s := by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

@[simp, aesop safe (rule_sets := [SetLike])]
lemma ofNat_mem [AddSubmonoidWithOneClass S R] (s : S) (n : ℕ) [n.AtLeastTwo] :
    ofNat(n) ∈ s := by
  rw [← Nat.cast_ofNat]; exact natCast_mem s n

instance (priority := 74) AddSubmonoidWithOneClass.toAddMonoidWithOne
    [AddSubmonoidWithOneClass S R] : AddMonoidWithOne s :=
  { AddSubmonoidClass.toAddMonoid s with
    one := ⟨_, one_mem s⟩
    natCast := fun n => ⟨n, natCast_mem s n⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun _ => Subtype.ext (Nat.cast_succ _) }

end AddSubmonoidWithOneClass

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

section SubsemiringClass

/-- `SubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative and an additive submonoid. -/
class SubsemiringClass (S : Type*) (R : outParam (Type u)) [NonAssocSemiring R]
  [SetLike S R] : Prop extends SubmonoidClass S R, AddSubmonoidClass S R

-- See note [lower instance priority]
instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type*)
    (R : Type u) {_ : NonAssocSemiring R} [SetLike S R] [h : SubsemiringClass S R] :
    AddSubmonoidWithOneClass S R :=
  { h with }

instance (priority := 100) SubsemiringClass.nonUnitalSubsemiringClass (S : Type*)
    (R : Type u) [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R] :
    NonUnitalSubsemiringClass S R where
  mul_mem := mul_mem

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

-- Prefer subclasses of `NonAssocSemiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s := fast_instance%
  Subtype.coe_injective.nonAssocSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/-- A subsemiring of a `NonAssocCommSemiring` inherits a `NonAssocCommSemiring` structure -/
instance (priority := 75) toNonAssocCommSemiring {R} [NonAssocCommSemiring R] [SetLike S R]
    [SubsemiringClass S R] : NonAssocCommSemiring s := fast_instance%
  Subtype.coe_injective.nonAssocCommSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

@[simp]
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

variable {s} in
@[simp]
lemma subtype_apply (x : s) :
    SubsemiringClass.subtype s x = x := rfl

lemma subtype_injective :
    Function.Injective (SubsemiringClass.subtype s) := fun _ ↦ by
  simp

-- Prefer subclasses of `Semiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance (priority := 75) toSemiring {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] :
    Semiring s := fast_instance%
  Subtype.coe_injective.semiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
instance toCommSemiring {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    CommSemiring s := fast_instance%
  Subtype.coe_injective.commSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S]

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R

/-- Reinterpret a `Subsemiring` as a `Submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `Subsemiring` as an `AddSubmonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

instance : SetLike (Subsemiring R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

instance : PartialOrder (Subsemiring R) := .ofSetLike (Subsemiring R) R

initialize_simps_projections Subsemiring (carrier → coe, as_prefix coe)

/-- The actual `Subsemiring` obtained from an element of a `SubsemiringClass`. -/
@[simps]
def ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R]
    (s : S) : Subsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _

instance (priority := 100) : CanLift (Set R) (Subsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ 1 ∈ s ∧
      ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2 },
      rfl ⟩

instance : SubsemiringClass (Subsemiring R) R where
  zero_mem := zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

/-- Turn a `Subsemiring` into a `NonUnitalSubsemiring` by forgetting that it contains `1`. -/
@[reducible]
def toNonUnitalSubsemiring (S : Subsemiring R) : NonUnitalSubsemiring R where __ := S

@[simp]
theorem mem_toSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
lemma mem_toNonUnitalSubsemiring {S : Subsemiring R} {x : R} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S := .rfl

theorem mem_carrier {s : Subsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
lemma coe_toNonUnitalSubsemiring (S : Subsemiring R) : (S.toNonUnitalSubsemiring : Set R) = S := rfl

@[simp]
theorem mem_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) {x : R} :
    x ∈ mk toSubmonoid add_mem zero_mem ↔ x ∈ toSubmonoid := .rfl

@[simp]
theorem coe_set_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) :
    (mk toSubmonoid add_mem zero_mem : Set R) = toSubmonoid := rfl

/-- Two subsemirings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubmonoid]
protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }

theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subsemiring R → Submonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)

theorem toAddSubmonoid_injective :
    Function.Injective (toAddSubmonoid : Subsemiring R → AddSubmonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)

lemma toNonUnitalSubsemiring_injective :
    Function.Injective (toNonUnitalSubsemiring : Subsemiring R → _) :=
  fun S₁ S₂ h => SetLike.ext'_iff.2
    (show (S₁.toNonUnitalSubsemiring : Set R) = S₂ from SetLike.ext'_iff.1 h)

lemma toNonUnitalSubsemiring_inj {S₁ S₂ : Subsemiring R} :
    S₁.toNonUnitalSubsemiring = S₂.toNonUnitalSubsemiring ↔ S₁ = S₂ :=
  toNonUnitalSubsemiring_injective.eq_iff

lemma one_mem_toNonUnitalSubsemiring (S : Subsemiring R) : (1 : R) ∈ S.toNonUnitalSubsemiring :=
  S.one_mem

set_option backward.simpa.using.reducibleClose false in
/-- Construct a `Subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
@[simps coe]
protected def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : Subsemiring R where
  carrier := s
  zero_mem' := by exact ha ▸ sa.zero_mem
  one_mem' := by exact hm ▸ sm.one_mem
  add_mem' {x y} := by simpa only [← ha] using sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using sm.mul_mem

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
    {x : R} : x ∈ Subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_toAddSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

/-- A subsemiring contains the semiring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem s

/-- A subsemiring contains the semiring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem s

/-- A subsemiring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subsemiring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance toNonAssocSemiring : NonAssocSemiring s :=
  SubsemiringClass.toNonAssocSemiring _

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = (1 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

protected theorem pow_mem {R : Type*} [Semiring R] (s : Subsemiring R) {x : R} (hx : x ∈ s)
    (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ _} h :=
    (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h).imp Subtype.ext Subtype.ext

/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance toSemiring {R} [Semiring R] (s : Subsemiring R) : Semiring s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]
theorem coe_pow {R} [Semiring R] (s : Subsemiring R) (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x : R) ^ n := rfl

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
instance toCommSemiring {R} [CommSemiring R] (s : Subsemiring R) : CommSemiring s :=
  { s.toSemiring with mul_comm := fun _ _ => Subtype.ext <| mul_comm _ _ }

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }

variable {s} in
@[simp]
lemma subtype_apply (x : s) :
    s.subtype x = x := rfl

lemma subtype_injective :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype : ⇑s.subtype = ((↑) : s → R) :=
  rfl

protected theorem nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) : n • x ∈ s :=
  nsmul_mem hx n

@[simp]
theorem coe_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s :=
  rfl

@[simp]
theorem coe_carrier_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid.carrier : Set R) = s :=
  rfl

theorem mem_toAddSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl

theorem coe_toAddSubmonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/-- The subsemiring `R` of the semiring `R`. -/
instance : Top (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subsemiring R) :=
  Set.mem_univ x

@[simp, norm_cast]
theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ :=
  rfl

end Subsemiring

namespace Subsemiring

/-- The inf of two subsemirings is their intersection. -/
instance : Min (Subsemiring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubmonoid ⊓ t.toAddSubmonoid with carrier := s ∩ t }⟩

@[simp, norm_cast]
theorem coe_inf (p p' : Subsemiring R) : ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : Subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl


end Subsemiring

namespace RingHom

variable {s : Subsemiring R} {σR : Type*} [SetLike σR R] [SubsemiringClass σR R]

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def domRestrict (f : R →+* S) (s : σR) : s →+* S :=
  f.comp <| SubsemiringClass.subtype s

@[simp]
theorem restrict_apply (f : R →+* S) {s : σR} (x : s) : f.domRestrict s x = f x :=
  rfl

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eqLocusS (f g : R →+* S) : Subsemiring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocusM g with carrier := { x | f x = g x } }

@[simp]
theorem mem_eqLocusS {f g : R →+* S} {x : R} : x ∈ f.eqLocusS g ↔ f x = g x := Iff.rfl

@[simp]
theorem eqLocusS_same (f : R →+* S) : f.eqLocusS f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

end RingHom

/-- Turn a non-unital subsemiring containing `1` into a subsemiring. -/
def NonUnitalSubsemiring.toSubsemiring (S : NonUnitalSubsemiring R) (h1 : 1 ∈ S) :
    Subsemiring R where
  __ := S
  one_mem' := h1

lemma Subsemiring.toNonUnitalSubsemiring_toSubsemiring (S : Subsemiring R) :
    S.toNonUnitalSubsemiring.toSubsemiring S.one_mem = S := rfl

lemma NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring (S : NonUnitalSubsemiring R) (h1) :
    (NonUnitalSubsemiring.toSubsemiring S h1).toNonUnitalSubsemiring = S := rfl
