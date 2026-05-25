/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.RE
public import Mathlib.Data.Set.Subsingleton

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

public section

open Encodable Denumerable
open Computable Part
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace ComputablePred

variable {α : Type*} [Primcodable α]

/-- **Rice's Theorem** -/
theorem rice (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => eval c ∈ C) {f g} (hf : Nat.Partrec f)
    (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C := by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂
          ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : eval c ∈ C <;> simp_all

theorem rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ := by
  classical exact
      have hC : ∀ f, f ∈ C ↔ eval f ∈ eval '' C := fun f =>
        ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
      ⟨fun h =>
        or_iff_not_imp_left.2 fun C0 =>
          Set.eq_univ_of_forall fun cg =>
            let ⟨cf, fC⟩ := Set.nonempty_iff_ne_empty.2 C0
            (hC _).2 <|
              rice (eval '' C) (h.of_eq hC)
                (Partrec.nat_iff.1 <| eval_part.comp (const cf) Computable.id)
                (Partrec.nat_iff.1 <| eval_part.comp (const cg) Computable.id) ((hC _).1 fC),
        fun h => by {
          obtain rfl | rfl := h <;> simpa [ComputablePred, Set.mem_empty_iff_false] using
            Computable.const _}⟩

/-- The Halting problem is recursively enumerable -/
theorem halting_problem_re (n) : REPred fun c => (eval c n).Dom :=
  (eval_part.comp Computable.id (Computable.const _)).dom_re

/-- The **Halting problem** is not computable -/
theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom
  | h => rice { f | (f n).Dom } h Nat.Partrec.zero Nat.Partrec.none trivial

theorem halting_problem_not_re (n) : ¬REPred fun c => ¬(eval c n).Dom
  | h => halting_problem _ <| computable_iff_re_compl_re'.2 ⟨halting_problem_re _, h⟩

end ComputablePred

namespace Nat

open Vector Part

/-- A simplified basis for `Partrec`. -/
inductive Partrec' : ∀ {n}, (List.Vector ℕ n →. ℕ) → Prop
  | prim {n f} : @Primrec' n f → @Partrec' n f
  | comp {m n f} (g : Fin n → List.Vector ℕ m →. ℕ) :
    Partrec' f → (∀ i, Partrec' (g i)) →
      Partrec' fun v => (List.Vector.mOfFn fun i => g i v) >>= f
  | rfind {n} {f : List.Vector ℕ (n + 1) → ℕ} :
    @Partrec' (n + 1) f → Partrec' fun v => rfind fun n => some (f (n ::ᵥ v) = 0)

end Nat

namespace Nat.Partrec'

open List.Vector Partrec Computable

open Nat.Partrec'

theorem to_part {n f} (pf : @Partrec' n f) : Partrec f := by
  induction pf with
  | prim hf => exact hf.to_prim.to_comp
  | comp _ _ _ hf hg => exact (Partrec.vector_mOfFn hg).bind (hf.comp snd)
  | rfind _ hf =>
    have := hf.comp (vector_cons.comp snd fst)
    have :=
      ((Primrec.eq.decide.comp _root_.Primrec.id (_root_.Primrec.const 0)).to_comp.comp
        this).to₂.partrec₂
    exact _root_.Partrec.rfind this

theorem of_eq {n} {f g : List.Vector ℕ n →. ℕ} (hf : Partrec' f) (H : ∀ i, f i = g i) :
    Partrec' g :=
  (funext H : f = g) ▸ hf

theorem of_prim {n} {f : List.Vector ℕ n → ℕ} (hf : Primrec f) : @Partrec' n f :=
  prim (Nat.Primrec'.of_prim hf)

theorem head {n : ℕ} : @Partrec' n.succ (@head ℕ n) :=
  prim Nat.Primrec'.head

set_option backward.isDefEq.respectTransparency false in
theorem tail {n f} (hf : @Partrec' n f) : @Partrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @prim _ _ <| Nat.Primrec'.get i.succ).of_eq fun v => by
    rw [← ofFn_get v.tail, funext (get_tail_succ v)]
    simp

set_option backward.isDefEq.respectTransparency false in
protected theorem bind {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g) :
    @Partrec' n fun v => (f v).bind fun a => g (a ::ᵥ v) :=
  (@comp n (n + 1) g (Fin.cases f (fun i v => some (v.get i))) hg <|
      Fin.cases (by simpa using hf) (fun i => by simpa using prim (Nat.Primrec'.get i))).of_eq
    fun v => by simp [mOfFn, Part.bind_assoc, pure]

protected theorem map {n f} {g : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' n f)
    (hg : @Partrec' (n + 1) g) : @Partrec' n fun v => (f v).map fun a => g (a ::ᵥ v) := by
  simpa [(Part.bind_some_eq_map _ _).symm] using hf.bind hg

/-- Analogous to `Nat.Partrec'` for `ℕ`-valued functions, a predicate for partial recursive
  vector-valued functions. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) :=
  ∀ i, Partrec' fun v => (f v).get i

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim <| hf i

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

protected theorem cons {n m} {f : List.Vector ℕ n → ℕ} {g} (hf : @Partrec' n f)
    (hg : @Vec n m g) : Vec fun v => f v ::ᵥ g v := fun i =>
  Fin.cases (by simpa using hf) (fun i => by simp only [hg i, get_cons_succ]) i

theorem idv {n} : @Vec n n id :=
  Vec.prim Nat.Primrec'.idv

set_option backward.isDefEq.respectTransparency false in
theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) : Partrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

theorem comp₁ {n} (f : ℕ →. ℕ) {g : List.Vector ℕ n → ℕ} (hf : @Partrec' 1 fun v => f v.head)
    (hg : @Partrec' n g) : @Partrec' n fun v => f (g v) := by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)

theorem rfindOpt {n} {f : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' (n + 1) f) :
    @Partrec' n fun v => Nat.rfindOpt fun a => ofNat (Option ℕ) (f (a ::ᵥ v)) :=
  ((rfind <|
        (of_prim (Primrec.nat_sub.comp (_root_.Primrec.const 1) Primrec.vector_head)).comp₁
          (fun n => Part.some (1 - n)) hf).bind
    ((prim Nat.Primrec'.pred).comp₁ Nat.pred hf)).of_eq
    fun v =>
    Part.ext fun b => by
      simp only [Nat.rfindOpt, Nat.sub_eq_zero_iff_le, PFun.coe_val, Part.mem_bind_iff,
        Part.mem_some_iff, Option.mem_def, Part.mem_coe]
      refine
        exists_congr fun a => (and_congr (iff_of_eq ?_) Iff.rfl).trans (and_congr_right fun h => ?_)
      · congr
        funext n
        cases f (n ::ᵥ v) <;> simp <;> rfl
      · have := Nat.rfind_spec h
        simp only [Part.coe_some, Part.mem_some_iff] at this
        revert this; rcases f (a ::ᵥ v) with - | c <;> intro this
        · cases this
        rw [← Option.some_inj, eq_comm]
        rfl

open Nat.Partrec.Code

theorem of_part : ∀ {n f}, Partrec f → @Partrec' n f :=
  @(suffices ∀ f, Nat.Partrec f → @Partrec' 1 fun v => f v.head from fun {n f} hf => by
      let g := fun n₁ =>
        (Part.ofOption (decode (α := List.Vector ℕ n) n₁)).bind (fun a => Part.map encode (f a))
      exact
        (comp₁ g (this g hf) (prim Nat.Primrec'.encode)).of_eq fun i => by
          dsimp only [g]; simp [encodek, Part.map_id']
    fun f hf => by
    obtain ⟨c, rfl⟩ := exists_code.1 hf
    simpa [eval_eq_rfindOpt] using
      rfindOpt <|
        of_prim <|
          Primrec.encode_iff.2 <|
            primrec_evaln.comp <|
              (Primrec.vector_head.pair (_root_.Primrec.const c)).pair <|
                Primrec.vector_head.comp Primrec.vector_tail)

theorem part_iff {n f} : @Partrec' n f ↔ Partrec f :=
  ⟨to_part, of_part⟩

theorem part_iff₁ {f : ℕ →. ℕ} : (@Partrec' 1 fun v => f v.head) ↔ Partrec f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| (Primrec.vector_ofFn fun _ => _root_.Primrec.id).to_comp).of_eq fun v => by
        simp only [id, head_ofFn],
      fun h => h.comp vector_head⟩

theorem part_iff₂ {f : ℕ → ℕ →. ℕ} : (@Partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (const nil)).of_eq fun v => by
        simp only [head_cons, tail_cons],
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩

theorem vec_iff {m n f} : @Vec m n f ↔ Computable f :=
  ⟨fun h => by simpa only [ofFn_get] using vector_ofFn fun i => to_part (h i), fun h i =>
    of_part <| vector_get.comp h (const i)⟩

end Nat.Partrec'
