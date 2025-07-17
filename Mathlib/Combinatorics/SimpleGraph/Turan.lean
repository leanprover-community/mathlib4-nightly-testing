/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.Finset.Sym
import Mathlib.Order.ConditionallyCompleteLattice.Basic

import Batteries.Tactic.ShowUnused

/-!
# Turán's theorem
-/

set_option warn.sorry false

section Mathlib.Combinatorics.SimpleGraph.Basic

open Finset Function

universe u v w

/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop

initialize_simps_projections SimpleGraph (Adj → adj)

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G : SimpleGraph V) {a b c u v w : V} {e : Sym2 V}

theorem adj_injective : Injective (Adj : SimpleGraph V → V → V → Prop) := sorry

section Order

/-- The relation that one `SimpleGraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (SimpleGraph V) :=
  ⟨IsSubgraph⟩

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (SimpleGraph V) where
  max x y :=
    { Adj := x.Adj ⊔ y.Adj }

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (SimpleGraph V) where
  min x y :=
    { Adj := x.Adj ⊓ y.Adj }

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (SimpleGraph V) :=
  { show DistribLattice (SimpleGraph V) from
      adj_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl with
    le := fun G H => ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }


end Order

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

/-- The edges of G consist of the unordered pairs of vertices related by
`G.Adj`. This is the order embedding; for the edge set of a particular graph, see
`SimpleGraph.edgeSet`.

The way `edgeSet` is defined is such that `mem_edgeSet` is proved by `Iff.rfl`.
(That is, `s(v, w) ∈ G.edgeSet` is definitionally equal to `G.Adj v w`.)
-/
-- Porting note: We need a separate definition so that dot notation works.
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel sorry) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G

variable (G₁ G₂)

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred sorry

end EdgeSet

end SimpleGraph

end Mathlib.Combinatorics.SimpleGraph.Basic

section Mathlib.Combinatorics.SimpleGraph.Finite
namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {e : Sym2 V}
variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edgeSet` of the graph as a `Finset`. -/
abbrev edgeFinset : Finset (Sym2 V) := Set.toFinset G.edgeSet

end SimpleGraph
end Mathlib.Combinatorics.SimpleGraph.Finite

section Mathlib.Combinatorics.SimpleGraph.Clique

open Finset Fintype Function

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

/-! ### `n`-cliques -/

section NClique

variable {n : ℕ} {s : Finset α}

/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (G : SimpleGraph α) (n : ℕ) (s : Finset α) : Prop where

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : ℕ}

/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t

end CliqueFree

end SimpleGraph
end Mathlib.Combinatorics.SimpleGraph.Clique

section Mathlib.Order.Partition.Finpartition
open Finset Function

variable {α : Type*}

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
structure Finpartition [Lattice α] [OrderBot α] (a : α) where
  /-- The elements of the finite partition of `a` -/
  parts : Finset α

/-! ### Finite partitions of finsets -/

namespace Finpartition

variable [DecidableEq α] {s t u : Finset α} (P : Finpartition s) {a : α}

theorem existsUnique_mem (ha : a ∈ s) : ∃! t, t ∈ P.parts ∧ a ∈ t := by sorry

/-- The part of the finpartition that `a` lies in. -/
def part (a : α) : Finset α := if ha : a ∈ s then choose (hp := P.existsUnique_mem ha) else ∅

theorem exists_subset_part_bijOn : ∃ r ⊆ s, Set.BijOn P.part r P.parts := by sorry

theorem card_parts_le_card : #P.parts ≤ #s := by sorry

section SetSetoid

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
def ofSetSetoid (s : Setoid α) (x : Finset α) [DecidableRel s.r] : Finpartition x where
  parts := x.image fun a ↦ {b ∈ x | s.r a b}

end SetSetoid

section Setoid

variable [Fintype α]

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
def ofSetoid (s : Setoid α) [DecidableRel s.r] : Finpartition (univ : Finset α) :=
  ofSetSetoid s univ

end Setoid

end Finpartition

end Mathlib.Order.Partition.Finpartition

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n r : ℕ}

variable (G) in
/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → #H.edgeFinset ≤ #G.edgeFinset

namespace IsTuranMaximal

variable {s t u : V}

variable (h : G.IsTuranMaximal r)
include h

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
theorem equivalence_not_adj : Equivalence (¬G.Adj · ·) where
  refl := sorry
  symm := sorry
  trans := sorry

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `equivalence_not_adj`. -/
def setoid : Setoid V := ⟨_, h.equivalence_not_adj⟩

instance : DecidableRel h.setoid.r :=
  inferInstanceAs <| DecidableRel (¬G.Adj · ·)

/-- The finpartition derived from `h.setoid`. -/
def finpartition [DecidableEq V] : Finpartition (univ : Finset V) := Finpartition.ofSetoid h.setoid

lemma not_adj_iff_part_eq [DecidableEq V] :
    ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t := by sorry

/--
error: (kernel) application type mismatch
  @IsTuranMaximal V inst✝³ G inst✝¹
argument has type
  DecidableRel (@Adj V G✝)
but function has type
  [DecidableRel (@Adj V G)] → ℕ → Prop
-/
#guard_msgs in
theorem card_parts_extracted_1_11 [DecidableEq V] :
  let fp := h.finpartition;
  #fp.parts < #(Finset.univ (α := V)) ∧ #fp.parts < r →
    ∀ (x y : V),
      x ≠ y → fp.part x = fp.part y →
      ∀ ⦃z : Finset V⦄, #z = r → ∃ x ∈ ↑z, ∃ y ∈ ↑z, x ≠ y ∧ ¬G.Adj x y := by
  intro fp l x y hn he z zc
  simp [h.not_adj_iff_part_eq] ---- <-- ERROR IS HERE
  exact exists_ne_map_eq_of_card_lt_of_maps_to (zc.symm ▸ l.2) fun a _ ↦ sorry

end IsTuranMaximal

end SimpleGraph

#show_unused SimpleGraph.IsTuranMaximal.card_parts_extracted_1_11
#min_imports
