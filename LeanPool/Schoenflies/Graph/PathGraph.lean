/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Graph.Walk
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Data.Set.Finite.Basic

/-!
# A path presented as a graph

`Schoenflies/Graph/Walk.lean` says what it means for an edge list to *run* through a graph.
This file says what it means for a graph to *be* a path, and — the point of the file —
constructs one.

## Why the object exists

An ear is a path that gets glued onto a graph, so it has to be a graph itself, not a walk
inside one. `Graph.IsPathGraph P u W v` says that `P`'s own edges, listed in the order `W`,
form a path from `u` to `v` and that `P`'s vertices are exactly the ones that path visits.
The list `W` is an index of the predicate rather than an existential: its **order** is part
of the claim, and it is what lets every later argument cut the path at a vertex without first
having to sort anything.

Mathlib's `Graph α β` carries a `Set β` of edges, not a list, so the correspondence between
the two is a clause of the definition (`Graph.IsPathGraph.edgeSet_eq`) rather than something
a list-based graph would give for free.

## Constructing one

`Graph.pathGraphOf G u W` is the subgraph of `G` spanned by the walk `W` from `u`: the
vertices the walk visits, and its own edges. Everything else in the file is a hypothesis of
the form `IsPathGraph`; this is where one is produced, and it is what an ear decomposition
runs on — a path found inside a big graph has to be turned into a graph before it can be
unioned back in.

## What the ear argument actually asks

Always the same thing: **whatever vertex is deleted, every remaining vertex of the path still
reaches one of the two ends** (`Graph.IsPathGraph.reaches_an_end`). The proof is uniform in
the deleted vertex `c`, with no case split on whether `c` is an end, an interior vertex or
off the path at all:

* if `c` is on the path, cut there (`Graph.IsPath.split`); each remaining vertex lies on one
  of the two halves, and a half runs to its far end without meeting the cut, because the
  split's last clause says the far half never returns to the source;
* if `c` is not on the path, cut at the vertex itself and reverse the near half.

Both branches go through the same two lemmas, `Graph.IsPath.reaches_target_of_ne_source` and
its mirror, so the interior case has no separate content.

## Blueprint

* `Graph.IsPathGraph` — the object called "a path `P`" in Lemma
  `lem:subdivision-ear-preserve` (b) ("if `P` is a path whose distinct endpoints lie in `G`
  … then `G ∪ P` is 2-connected") and "an ear" in Lemma `lem:relative-ear`.
* `Graph.IsPathGraph.reaches_an_end` — the blueprint's "every component of `P - x` is
  attached to `G - x` at one of the two endpoints of `P`; when `x` is an endpoint, the
  remainder of `P` is attached at the other endpoint", both sentences at once.
* `Graph.pathGraphOf` — the "shortest path through `L` between two such neighbors is an ear"
  of `lem:relative-ear`: a path of the ambient graph, presented as a graph.

Nothing here mentions 2-connectivity; the union of a 2-connected graph with an ear is a
later module.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`, so that `h.reaches_an_end` and
`G.pathGraphOf u W` resolve by dot notation.
-/

public section

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H P : Graph α β} {u v w x y c : α} {e : β} {W W₁ W₂ : List β}

/-! ### Walks and vertex deletion

Mathlib's `Graph.deleteVerts` takes a set; a single deleted vertex is `{c}`. -/

/-- Pushing the visited set down an inclusion: a subgraph's edges have ends the big graph's
edges have too. This is the direction the freshness clause of a path travels in, and the
whole content of `Graph.IsPath.anti`. -/
theorem coveredVertices_anti (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨e, he, y, hy⟩ ↦ ⟨e, he, y, hy.mono hHG⟩

theorem walkVertices_anti (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_anti hHG)

/-- **A walk that never visits `c` survives the deletion of `c`.** Every deletion argument in
the ear layer reduces to this. -/
theorem IsWalk.avoiding (h : G.IsWalk u W v) (hc : c ∉ G.walkVertices u W) :
    (G.deleteVerts {c}).IsWalk u W v := by
  induction h with
  | @nil x hx =>
    refine .nil ?_
    rw [vertexSet_deleteVerts]
    exact ⟨hx, by rintro (rfl : x = c); exact hc mem_walkVertices_self⟩
  | @cons u w v e W hl _ ih =>
    have hw : w ∈ G.walkVertices u (e :: W) :=
      mem_walkVertices_cons_of_mem hl mem_walkVertices_self
    have hcw : c ∉ G.walkVertices w W := fun h ↦ hc (mem_walkVertices_cons_of_mem hl h)
    refine .cons ?_ (ih hcw)
    rw [deleteVerts_isLink]
    refine ⟨hl, ?_, ?_⟩
    · rintro (rfl : u ∈ ({c} : Set α))
      exact hc mem_walkVertices_self
    · rintro (rfl : w ∈ ({c} : Set α))
      exact hc hw

/-- Reversal does not change which vertices a walk visits — but it does change the source, so
this is not `Graph.walkVertices_reverse`, which keeps it. -/
theorem IsWalk.reverse_walkVertices (h : G.IsWalk u W v) :
    G.walkVertices v W.reverse = G.walkVertices u W := by
  have h₁ : v ∈ G.walkVertices u W := h.target_mem_walkVertices
  have h₂ : u ∈ G.walkVertices v W := by
    have := h.reverse.target_mem_walkVertices
    rwa [walkVertices_reverse] at this
  rw [walkVertices_reverse]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_) <;>
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
  exacts [h₁, mem_walkVertices_of_mem_covered hcov, h₂, mem_walkVertices_of_mem_covered hcov]

/-- Splitting the visited set along a concatenation. Purely about lists: no walk is needed,
and the middle vertex `w` is arbitrary. -/
theorem walkVertices_append_subset :
    G.walkVertices u (W₁ ++ W₂) ⊆ G.walkVertices u W₁ ∪ G.walkVertices w W₂ := by
  rintro y hy
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  · rw [coveredVertices_append] at hcov
    exact hcov.imp mem_walkVertices_of_mem_covered mem_walkVertices_of_mem_covered

/-! ### Reaching an end of a path after a deletion -/

/-- A vertex of a path other than its source still reaches the target once the source is
deleted: cut the path at the vertex, and the far half never returns to the source. -/
theorem IsPath.reaches_target_of_ne_source (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxu : x ≠ u) : (G.deleteVerts {u}).Reaches x v := by
  obtain ⟨-, W₂, -, -, h₂, hback⟩ := h.split hx
  exact ⟨W₂, h₂.isWalk.avoiding (hback.resolve_left hxu)⟩

/-- The mirror image, run on the reversed path. -/
theorem IsPath.reaches_source_of_ne_target (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxv : x ≠ v) : (G.deleteVerts {v}).Reaches x u :=
  h.reverse.reaches_target_of_ne_source (by rwa [h.isWalk.reverse_walkVertices]) hxv

/-- **Deleting any vertex leaves every other vertex of a path able to reach an end.**
Uniform in the deleted vertex `c`: if `c` is on the path the path is cut there and each
remaining vertex sits on a half that runs to that half's far end; if `c` is off the path the
path is cut at the vertex itself and its near half, reversed, runs to the source. -/
theorem IsPath.reaches_an_end (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W)
    (hxc : x ≠ c) :
    (G.deleteVerts {c}).Reaches x u ∨ (G.deleteVerts {c}).Reaches x v := by
  by_cases hc : c ∈ G.walkVertices u W
  · obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := h.split hc
    rcases walkVertices_append_subset (w := c) hx with hx₁ | hx₂
    · exact Or.inl (h₁.reaches_source_of_ne_target hx₁ hxc)
    · exact Or.inr (h₂.reaches_target_of_ne_source hx₂ hxc)
  · -- The deletion misses the path entirely, so the near half survives whole.
    obtain ⟨W₁, W₂, rfl, h₁, -, -⟩ := h.split hx
    refine Or.inl ⟨W₁.reverse, h₁.reverse.isWalk.avoiding ?_⟩
    rw [h₁.isWalk.reverse_walkVertices]
    exact fun hmem ↦ hc (walkVertices_mono (List.subset_append_left _ _) hmem)

/-! ### A graph that is a path -/

/-- `P.IsPathGraph u W v` : the graph `P` *is* the path from `u` to `v` along `W`. Its own
edges are exactly the entries of `W`, and its vertices are exactly the ones that path visits.

The edge list is an index rather than an existential because its order is used: an argument
that deletes a vertex cuts `W` in two, and a graph whose edges were only a set would have to
recover the order first. -/
structure IsPathGraph (P : Graph α β) (u : α) (W : List β) (v : α) : Prop where
  /-- The graph's own edges, in the given order, form a path from one end to the other. -/
  isPath : P.IsPath u W v
  /-- The graph has no edges beyond that path's. -/
  edgeSet_eq : E(P) = {e | e ∈ W}
  /-- The graph has no vertices beyond the ones that path visits. -/
  vertexSet_eq : V(P) = P.walkVertices u W

namespace IsPathGraph

theorem isWalk (h : P.IsPathGraph u W v) : P.IsWalk u W v := h.isPath.isWalk

/-- A vertex of a path graph is visited by its path. -/
theorem mem_walkVertices (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) :
    x ∈ P.walkVertices u W := h.vertexSet_eq ▸ hx

/-- Conversely, whatever the path visits is a vertex. -/
theorem mem_vertexSet (h : P.IsPathGraph u W v) (hx : x ∈ P.walkVertices u W) : x ∈ V(P) :=
  h.vertexSet_eq ▸ hx

theorem mem_edgeSet (h : P.IsPathGraph u W v) (he : e ∈ W) : e ∈ E(P) := by
  rw [h.edgeSet_eq]; exact he

theorem mem_list (h : P.IsPathGraph u W v) (he : e ∈ E(P)) : e ∈ W := by
  rw [h.edgeSet_eq] at he; exact he

theorem source_mem (h : P.IsPathGraph u W v) : u ∈ V(P) := h.isPath.left_mem

theorem target_mem (h : P.IsPathGraph u W v) : v ∈ V(P) := h.isPath.right_mem

/-- A path graph read from the other end. -/
theorem reverse (h : P.IsPathGraph u W v) : P.IsPathGraph v W.reverse u where
  isPath := h.isPath.reverse
  edgeSet_eq := by rw [h.edgeSet_eq]; ext e; simp
  vertexSet_eq := by rw [h.isWalk.reverse_walkVertices]; exact h.vertexSet_eq

/-- A path graph is connected: every vertex is visited, so the path's own prefix runs to it
from the source. -/
theorem connected (h : P.IsPathGraph u W v) : P.Connected := by
  refine Connected.of_hub h.source_mem fun x hx ↦ ?_
  obtain ⟨W₁, -, -, h₁, -, -⟩ := h.isPath.split (h.mem_walkVertices hx)
  exact ⟨W₁, h₁.isWalk⟩

/-- **Whatever vertex is deleted, every remaining vertex of a path graph still reaches one of
its two ends.** This is what the ear argument turns on: the ear's two ends are the only
vertices it shares with the graph it is glued to, so a surviving vertex of the ear has to
reach one of them inside the ear itself. -/
theorem reaches_an_end (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) (hxc : x ≠ c) :
    (P.deleteVerts {c}).Reaches x u ∨ (P.deleteVerts {c}).Reaches x v :=
  h.isPath.reaches_an_end (h.mem_walkVertices hx) hxc

end IsPathGraph

/-! ### Constructing a path graph -/

/-- **The subgraph of `G` spanned by the walk `W` from `u`**: the vertices that walk visits,
carrying exactly the walk's own edges.

This is the construction an ear decomposition needs — a path found inside a big graph, turned
into a graph of its own so that it can be unioned back in. It is built from Mathlib's
`Graph.domRestrict` and `Graph.induce`, so that `Graph.pathGraphOf_le` is almost free. -/
def pathGraphOf (G : Graph α β) (u : α) (W : List β) : Graph α β :=
  (G.restrict {e | e ∈ W}).induce (G.walkVertices u W)

@[simp]
theorem pathGraphOf_vertexSet : V(G.pathGraphOf u W) = G.walkVertices u W := rfl

@[simp]
theorem pathGraphOf_isLink :
    (G.pathGraphOf u W).IsLink e x y ↔
      e ∈ W ∧ G.IsLink e x y ∧ x ∈ G.walkVertices u W ∧ y ∈ G.walkVertices u W := by
  simp only [pathGraphOf, induce_isLink, restrict_isLink, Set.mem_ofPred_eq]
  tauto

theorem mem_vertexSet_pathGraphOf_self : u ∈ V(G.pathGraphOf u W) := mem_walkVertices_self

/-- The spanned subgraph really is a subgraph. -/
theorem pathGraphOf_le (h : G.IsWalk u W v) : G.pathGraphOf u W ≤ G :=
  le_trans (induce_le h.walkVertices_subset) restrict_le

/-- Its edges are exactly the walk's. One inclusion is the definition; the other needs the
walk, to know that an entry of `W` is an edge of `G` at all and that its ends are visited. -/
theorem pathGraphOf_edgeSet (h : G.IsWalk u W v) : E(G.pathGraphOf u W) = {e | e ∈ W} := by
  ext f
  rw [edgeSet_eq_setOfPred_exists_isLink]
  simp only [pathGraphOf_isLink, Set.mem_ofPred_eq]
  refine ⟨fun ⟨_, _, hf, _⟩ ↦ hf, fun hf ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hf)
  exact ⟨a, b, hf, hab, mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_left⟩,
    mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_right⟩⟩

/-- The spanned subgraph visits the same vertices as the ambient graph does along `W`: its
edges are the same edges, joining the same pairs. No walk is needed — an end of an edge of
`W` is visited by definition, so it survives the induced subgraph. -/
theorem coveredVertices_pathGraphOf :
    (G.pathGraphOf u W).coveredVertices W = G.coveredVertices W := by
  refine Set.Subset.antisymm (fun z ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, (pathGraphOf_isLink.1 hy).2.1⟩)
    fun z ⟨f, hf, y, hy⟩ ↦ ?_
  · exact ⟨f, hf, y, pathGraphOf_isLink.2 ⟨hf, hy,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_left⟩,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_right⟩⟩⟩

theorem walkVertices_pathGraphOf :
    (G.pathGraphOf u W).walkVertices u W = G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_pathGraphOf]

/-- The walk runs inside the subgraph it spans. -/
theorem IsWalk.pathGraphOf (h : G.IsWalk u W v) : (G.pathGraphOf u W).IsWalk u W v :=
  h.anti (pathGraphOf_le h) mem_vertexSet_pathGraphOf_self
    fun _ he ↦ (pathGraphOf_edgeSet h) ▸ he

/-- The path runs inside the subgraph it spans. -/
theorem IsPath.pathGraphOf (h : G.IsPath u W v) : (G.pathGraphOf u W).IsPath u W v :=
  h.anti (pathGraphOf_le h.isWalk) mem_vertexSet_pathGraphOf_self
    fun _ he ↦ (pathGraphOf_edgeSet h.isWalk) ▸ he

/-- **A path of `G` spans a path graph.** This is the construction the whole file exists
for: the object every `Graph.IsPathGraph` hypothesis elsewhere is discharged by. -/
theorem IsPath.isPathGraph_pathGraphOf (h : G.IsPath u W v) :
    (G.pathGraphOf u W).IsPathGraph u W v where
  isPath := h.pathGraphOf
  edgeSet_eq := pathGraphOf_edgeSet h.isWalk
  vertexSet_eq := by rw [pathGraphOf_vertexSet, walkVertices_pathGraphOf]

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

/-- A step of a walk adds exactly one vertex to the visited set. -/
theorem walkVertices_cons (hl : G.IsLink e u w) :
    G.walkVertices u (e :: W) = insert u (G.walkVertices w W) := by
  ext x
  constructor
  · intro hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    exacts [Set.mem_insert _ _, Set.mem_insert_of_mem _ hx']
  · intro hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx'
    exacts [mem_walkVertices_self, mem_walkVertices_cons_of_mem hl hx']

theorem IsWalk.finite_walkVertices (h : G.IsWalk u W v) : (G.walkVertices u W).Finite := by
  induction h with
  | nil => rw [walkVertices_nil]; exact Set.finite_singleton _
  | @cons u w v e W hl _ ih => rw [walkVertices_cons hl]; exact Set.Finite.insert u ih

/-- The graph spanned by a walk has finitely many vertices, whatever the ambient graph.
Stated as a `Set.Finite` rather than as a `Graph.Finite` instance so that this file does not
have to depend on `Schoenflies/Graph/Degree.lean`; the two halves build one in a line. -/
theorem IsWalk.finite_vertexSet_pathGraphOf (h : G.IsWalk u W v) :
    V(G.pathGraphOf u W).Finite := by
  simpa using h.finite_walkVertices

theorem IsWalk.finite_edgeSet_pathGraphOf (h : G.IsWalk u W v) :
    E(G.pathGraphOf u W).Finite := by
  rw [pathGraphOf_edgeSet h]; exact List.finite_toSet W

end Graph
