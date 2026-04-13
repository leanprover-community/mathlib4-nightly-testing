/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Multigraphs

A multigraph is a set of vertices and a set of edges,
together with incidence data that associates each edge `e`
with an unordered pair `s(x,y)` of vertices called the *ends* of `e`.
The pair of `e` and `s(x,y)` is called a *link*.
The vertices `x` and `y` may be equal, in which case `e` is a *loop*.
There may be more than one edge with the same ends.

If a multigraph has no loops and has at most one edge for every given ends, it is called *simple*,
and these objects are also formalized as `SimpleGraph`.

This module defines `Graph α β` for a vertex type `α` and an edge type `β`,
and gives basic API for incidence, adjacency and extensionality.
The design broadly follows [Chou1994].

## Main definitions

For `G : Graph α β`, ...

* `V(G)` denotes the vertex set of `G` as a term in `Set α`.
* `E(G)` denotes the edge set of `G` as a term in `Set β`.
* `G.IsLink e x y` means that the edge `e : β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : β` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.
* `G.incidenceSet x` is the set of edges incident to `x`.
* `G.loopSet x` is the set of loops with both ends equal to `x`.
* `G.copy` creates a definitional copy of a graph with propositionally equal data.
* `G.Compatible H` means that `G` and `H` agree on the incidence relation for their shared edges.
* `Graph.noEdge V` is the graph with vertex set `V` and no edges.
* `Graph.bouquet v E` is the graph with vertex set `{v}` and edge set `E`,
  where every edge is a loop at `v`.
* `Graph.banana u v E` is the graph with vertex set `{u, v}` and edge set `E`,
  where every edge connects `u` and `v`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`V(G) : Set α` and `E(G) : Set β`, within ambient types, rather than being types themselves.
This mimics the 'embedded set' design used in `Matroid`, which seems to be more convenient for
formalizing real-world proofs in combinatorics.

A specific advantage is that this allows subgraphs of `G : Graph α β` to also exist on
an equal footing with `G` as terms in `Graph α β`,
and so there is no need for a `Graph.subgraph` type and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation.

## Notation

Reflecting written mathematics, we use the compact notations `V(G)` and `E(G)` to
refer to the `vertexSet` and `edgeSet` of `G : Graph α β`.
If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right` in names.
-/
set_option backward.defeq.atInstanceTransparency false

@[expose] public section

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

/-- A multigraph with vertices of type `α` and edges of type `β`,
as described by vertex and edge sets `vertexSet : Set α` and `edgeSet : Set β`,
and a predicate `IsLink` describing whether an edge `e : β` has vertices `x y : α` as its ends.

The `edgeSet` structure field can be inferred from `IsLink`
via `edge_mem_iff_exists_isLink` (and this structure provides default values
for `edgeSet` and `edge_mem_iff_exists_isLink` that use `IsLink`).
While the field is not strictly necessary, when defining a graph we often
immediately know what the edge set should be,
and furthermore having `edgeSet` separate can be convenient for
definitional equality reasons.
-/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

initialize_simps_projections Graph (IsLink → isLink)

namespace Graph

variable {G H : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => Graph.edgeSet G

/-! ### Edge-vertex-vertex incidence -/

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he

protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h.edge_mem h

lemma IsLink.left_mem (h : G.IsLink e x y) : x ∈ V(G) :=
  G.left_mem_of_isLink h

lemma IsLink.right_mem (h : G.IsLink e x y) : y ∈ V(G) :=
  h.symm.left_mem

lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  ⟨.symm, .symm⟩

lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext G.edge_mem_iff_exists_isLink

lemma IsLink.left_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_isLink_of_isLink h h'

lemma IsLink.right_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : y = z ∨ y = w :=
  h.symm.left_eq_or_eq h'

lemma IsLink.left_eq_of_right_ne (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) :
    x = w :=
  (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id

lemma IsLink.right_unique (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

lemma IsLink.left_unique (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y :=
  h.symm.right_unique h'.symm

lemma IsLink.eq_and_eq_or_eq_and_eq {x' y' : α} (h : G.IsLink e x y)
    (h' : G.IsLink e x' y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]

lemma IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x, y) = s(x', y') := by
  rw [h.isLink_iff, Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/-- The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
is one or both of the ends of the edge `e`.
In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`. -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.IsLink e x y

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) :=
  h.choose_spec.edge_mem

@[simp]
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
lemma Inc.vertex_mem (h : G.Inc e x) : x ∈ V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `y` cannot be inferred by `simp`.
lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq h'

lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

lemma IsLink.isLink_iff_eq (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
  ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

/-- Given a proof that the edge `e` is incident with the vertex `x` in `G`,
noncomputably find the other end of `e`. (If `e` is a loop, this is equal to `x` itself). -/
protected noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
lemma Inc.isLink_other (h : G.Inc e x) : G.IsLink e x h.other :=
  h.choose_spec

@[simp]
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.isLink_other.inc_right

lemma Inc.eq_or_eq_or_eq (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! ⟨hxy, hxz, hyz⟩
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hxy.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hxz.symm
  exact hyz rfl

lemma inc_eq_inc_iff_isLink_eq_isLink {G₁ G₂ : Graph α β} :
    G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc, isLink_iff_inc, h]
  · simp [funext_iff, Inc, h]

/-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

@[simp]
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem

/-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`. -/
def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := ∃ y ≠ x, G.IsLink e x y

lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x :=
  h.choose_spec.2.inc_left

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloopAt x h

lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x :=
  ⟨fun h ↦ ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ ↦ ⟨y, mt (fun h ↦ h ▸ hy) hn, hy⟩⟩

lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge whose ends are the vertices `x` and `y`. -/
def Adj (G : Graph α β) (x y : α) : Prop := ∃ e, G.IsLink e x y

@[symm]
protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

instance : Std.Symm G.Adj where
  symm _ _ := Adj.symm

lemma adj_comm (x y) : G.Adj x y ↔ G.Adj y x :=
  ⟨.symm, .symm⟩

-- Cannot be @[simp] because `y` cannot be inferred by `simp`.
lemma Adj.left_mem (h : G.Adj x y) : x ∈ V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
lemma Adj.right_mem (h : G.Adj x y) : y ∈ V(G) :=
  h.symm.left_mem

lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩

/-! ### Extensionality -/

/-- `edgeSet` can be determined using `IsLink`, so the graph constructed from `G.vertexSet` and
`G.IsLink` using any value for `edgeSet` is equal to `G` itself. -/
@[simp]
lemma mk_eq_self (G : Graph α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph.mk V(G) G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h') hE
    (fun _ _ _ ↦ IsLink.left_mem) = G := by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp

/-- Two graphs with the same vertex set and binary incidences are equal.
(We use this as the default extensionality lemma rather than adding `@[ext]`
to the definition of `Graph`, so it doesn't require equality of the edge sets.) -/
@[ext]
protected lemma ext {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink, ← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert rfl using 2
  · exact hV.symm
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOf_exists_isLink, h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc, h]

/-- `Graph.copy` produces a graph equal to `G` but with provided definitional choices
for `vertexSet`, `edgeSet`, and `IsLink`. This is mainly useful for improving
definitional equalities while keeping the same underlying graph. -/
@[simps]
def copy (G : Graph α β) {vertexSet : Set α} {edgeSet : Set β} {IsLink : β → α → α → Prop}
    (hvertexSet : V(G) = vertexSet) (hedgeSet : E(G) = edgeSet)
    (hIsLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  vertexSet := vertexSet
  edgeSet := edgeSet
  IsLink := IsLink
  isLink_symm e he x y := by
    simp_rw [← hIsLink]
    apply G.isLink_symm (hedgeSet ▸ he)
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← hIsLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← hIsLink, ← hedgeSet]
    exact G.edge_mem_iff_exists_isLink
  left_mem_of_isLink := by
    simp_rw [← hIsLink, ← hvertexSet]
    exact G.left_mem_of_isLink

@[simp]
lemma copy_eq (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop}
    (hV : V(G) = V) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all

/-! ### Sets of edges or loops incident to a vertex -/

/-- `G.incidenceSet x` is the set of edges incident to `x` in `G`. -/
def incidenceSet (x : α) : Set β := {e | G.Inc e x}

@[simp]
theorem mem_incidenceSet (x : α) (e : β) : e ∈ G.incidenceSet x ↔ G.Inc e x :=
  Iff.rfl

theorem incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x ⊆ E(G) :=
  fun _ ⟨_, hy⟩ ↦ hy.edge_mem

/-- `G.loopSet x` is the set of loops at `x` in `G`. -/
def loopSet (x : α) : Set β := {e | G.IsLoopAt e x}

@[simp]
theorem mem_loopSet (x : α) (e : β) : e ∈ G.loopSet x ↔ G.IsLoopAt e x :=
  Iff.rfl

/-- The loopSet is included in the incidenceSet. -/
theorem loopSet_subset_incidenceSet (x : α) : G.loopSet x ⊆ G.incidenceSet x := fun _ he ↦ ⟨x, he⟩

/-!
### Compatibility of Graphs

We define two graphs to be `Compatible` if for each edge belonging to their shared edge set,
the incidence relation (i.e., which pairs of vertices it links) is the same in both graphs.
-/

/-- Two graphs are compatible if their shared edges have the same ends in both graphs. -/
def Compatible (G H : Graph α β) : Prop :=
  ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y

lemma Compatible.isLink_congr (heG : e ∈ E(G)) (heH : e ∈ E(H)) (h : G.Compatible H) {x y : α} :
    G.IsLink e x y ↔ H.IsLink e x y :=
  h heG heH x y

lemma Compatible.refl (G : Graph α β) : G.Compatible G :=
  fun _ _ _ _ _ => .rfl

@[simp]
lemma Compatible.rfl {G : Graph α β} : G.Compatible G := .refl _

instance : Std.Refl (Compatible : Graph α β → Graph α β → Prop) where
  refl _ := .rfl

@[symm]
lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ heH heG x y => (h heG heH x y).symm

instance : Std.Symm (Compatible : Graph α β → Graph α β → Prop) where
  symm _ _ := Compatible.symm

lemma IsLink.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLink e x y) :
    H.IsLink e x y :=
  (hGH h.edge_mem heH x y).mp h

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H :=
  fun _ heG heH _ _ ↦ h.notMem_of_mem_left heG heH |>.elim

lemma Inc.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.Inc e x) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

lemma IsLoopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLoopAt e x) :
    H.IsLoopAt e x :=
  IsLink.of_compatible hGH heH h

lemma IsNonloopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsNonloopAt e x) :
    H.IsNonloopAt e x := by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

/-! ### Graphs with no edges -/

/-- The graph with vertex set `vertexSet` and no edges -/
@[simps (attr := grind =)]
def noEdge (vertexSet : Set α) (β : Type*) : Graph α β where
  vertexSet := vertexSet
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

variable {vertexSet : Set α} {edgeSet : Set β}

lemma edgeSet_eq_empty : E(G) = ∅ ↔ G = noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext rfl ?_, fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this

/-! ### Graphs with two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps (attr := grind =)]
def banana (u v : α) (edgeSet : Set β) : Graph α β where
  vertexSet := {u, v}
  edgeSet := edgeSet
  IsLink e x y := e ∈ edgeSet ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm _ _ _ := by aesop
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma banana_inc : (banana u v edgeSet).Inc e x ↔ e ∈ edgeSet ∧ (x = u ∨ x = v) := by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

lemma banana_comm (u v : α) (edgeSet : Set β) : banana u v edgeSet = banana v u edgeSet :=
  Graph.ext_inc (pair_comm ..) <| by simp [or_comm]

@[simp]
lemma banana_isNonloopAt :
    (banana u v edgeSet).IsNonloopAt e x ↔ e ∈ edgeSet ∧ (x = u ∨ x = v) ∧ u ≠ v := by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc]
  aesop

@[simp]
lemma banana_isLoopAt : (banana u v edgeSet).IsLoopAt e x ↔ e ∈ edgeSet ∧ x = u ∧ u = v := by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]
lemma banana_adj : (banana u v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ s(x, y) = s(u, v) := by
  simp only [Adj, banana_isLink, exists_and_right, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, and_congr_left_iff]
  exact fun _ ↦ Iff.rfl

@[simp]
lemma banana_empty : banana u v ∅ = Graph.noEdge {u, v} β := by
  ext <;> simp

/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex. This is an abbreviation for the special case
  of `banana` where the two vertices are the same. Most lemmas about `bouquet` should instead be
  proved using `banana` instead. -/
abbrev bouquet (v : α) (edgeSet : Set β) : Graph α β :=
  banana v v edgeSet

lemma bouquet_vertexSet (v : α) (edgeSet : Set β) : V(bouquet v edgeSet) = {v} := by simp

lemma bouquet_isLink (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).IsLink e x y ↔ e ∈ edgeSet ∧ x = v ∧ y = v := by simp

lemma bouquet_inc (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).Inc e x ↔ e ∈ edgeSet ∧ x = v := by simp

lemma bouquet_adj (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ x = v ∧ y = v := by simp

lemma bouquet_isLoopAt (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).IsLoopAt e x ↔ e ∈ edgeSet ∧ x = v := by simp

lemma not_isNonloopAt_bouquet : ¬ (bouquet v edgeSet).IsNonloopAt e x := by
  simp +contextual [IsNonloopAt, eq_comm]

/-- Every graph on just one vertex is a bouquet on that vertex. -/
lemma eq_bouquet_of_subsingleton (hv : v ∈ V(G)) (hss : V(G).Subsingleton) :
    G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc] at h
  obtain ⟨z,w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

lemma eq_bouquet_iff : G = bouquet v E(G) ↔ V(G) = {v} :=
  ⟨fun h ↦ h ▸ bouquet_vertexSet v _,
    fun h ↦ eq_bouquet_of_subsingleton (by simp [h]) (by simp [h])⟩

/-- Every graph on just one vertex is a bouquet on that vertex. -/
lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) : ∃ x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet_of_subsingleton hne.some_mem hss⟩

lemma bouquet_empty (v : α) : bouquet v ∅ = noEdge {v} β := by simp

end Graph
