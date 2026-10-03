/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Data.Set.Card
public import LeanPool.Schoenflies.Graph.Walk

/-!
# Vertex deletion and 2-connectivity

Deleting a vertex from Mathlib's multigraph `Graph α β`, and the blueprint's notion of a
2-connected graph.

## Vertex deletion is Mathlib's

Mathlib already has it: `Graph.deleteVerts G X = G.induce (V(G) \ X)`, in
`Mathlib/Combinatorics/Graph/Delete.lean`, with `V(G.deleteVerts X) = V(G) \ X` and
`E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X}` — an edge with an end in
`X` is gone, which is exactly what is wanted. Nothing here redefines it; `G.deleteVerts {x}`
is the deletion of one vertex, and what this file adds is the transfer of *walks* across it,
which Mathlib has no notion of.

Two of those transfers are the whole story, and both are corollaries of `Graph.IsWalk.anti`:

* `Graph.IsWalk.deleteVerts_singleton` — a walk that never visits `x` is a walk of `G - x`.
  The edges of such a walk automatically survive, because the ends of an edge of a walk are
  vertices the walk visits.
* `Graph.IsWalk.notMem_of_inc_of_deleteVerts` — a walk **in** `G - x` cannot have used an
  edge at `x`; there are none left to use. This is how an argument that routes around a
  vertex ends up avoiding a named edge, and it is what makes `Graph.IsTwoConnected.no_bridge`
  short.

Deleting a vertex the graph does not have changes nothing — `G.deleteVerts {x} = G` on the
nose (`Graph.deleteVerts_singleton_eq_self`), since `V(G) \ {x} = V(G)`. That equation is
what makes the union lemma's hard case disappear.

## At least three vertices

The counting clause of 2-connectivity is carried by `Graph.HasThreeVertices`, "three pairwise
distinct vertices", rather than by `3 ≤ V(G).ncard`. The two agree on a finite graph, but the
existential form is **monotone with no finiteness hypothesis** (`Graph.HasThreeVertices.mono`),
and monotonicity is precisely what `Graph.IsTwoConnected.union` needs: the union of two graphs
is not known to be finite at the point where its third vertex is produced. `Set.ncard` is `0`
on an infinite set, so `3 ≤ V(G).ncard` would additionally make every infinite graph fail to
be 2-connected, which is not the intent of the convention.

What consumers actually use is never the clause itself but `Graph.HasThreeVertices.exists_ne_ne`
— any two vertices leave a third over. `Graph.hasThreeVertices_iff_ncard` is the bridge back to
the count, for a consumer that has one.

## The convention, verbatim, and what it costs

`Graph.IsTwoConnected` is the blueprint's definition word for word (§"Plane graphs and the
utility graph"): at least three vertices, connected, and still connected after any one vertex
is deleted. Two consequences the blueprint calls out are recorded here as theorems rather
than as prose:

* the one-edge graph is **not** 2-connected, and
* a two-vertex cycle — two parallel edges — is a cycle without being 2-connected.

Both are instances of `Graph.not_isTwoConnected_banana`: `Graph.banana u v F` has only the two
vertices `u` and `v` whatever `F` is, so it fails the counting clause. Two-vertex cycles do
occur in the development, as face boundaries inside a larger 2-connected graph, and this is
the theorem that says they are not themselves 2-connected. (No cycle is *named* here: this
file must not depend on the cycle module.)

## Union

Mathlib's `Mathlib/Combinatorics/Graph/Lattice.lean` provides only the *infimum* of two
graphs — there is no union in this version of Mathlib — so `Graph.union` is defined here. On
an edge belonging to both graphs, `G`'s ends win:

```
(G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
```

which makes the definition total. It has to be resolved somehow: two graphs may disagree
about the ends of a shared edge name, and then no graph has both as subgraphs. When the two
graphs are `Graph.Compatible` — in particular when both are subgraphs of one graph, via
`Graph.Compatible.of_le_le`, which is the only way the plane layer forms unions — the
disjunction collapses to the naive one (`Graph.Compatible.union_isLink`) and both graphs are
subgraphs of the union.

## Blueprint

* `Graph.IsTwoConnected` — the definition in §"Plane graphs and the utility graph": "a finite
  graph is *2-connected* if it has at least three vertices, is connected, and remains
  connected after deletion of any one vertex".
* `Graph.IsTwoConnected.no_cut_vertex` — "with this convention a 2-connected graph has no cut
  vertex".
* `Graph.not_isTwoConnected_banana` — "the one-edge graph is not 2-connected", and the same
  computation for the two-vertex cycle of the next paragraph.
* `Graph.IsTwoConnected.no_bridge` — "A 2-connected graph has no bridge", the step of
  `lem:subdivision-ear-preserve` (a) that the ear decomposition runs on. Stated as "deleting
  the edge leaves its ends connected", which is the form `lem:cycle-criterion` consumes; the
  cycle itself is built elsewhere.
* `Graph.IsTwoConnected.union` — `lem:union-two-connected`, "if two finite 2-connected graphs
  have at least two vertices in common, their union is 2-connected".
-/

public section

open Set

variable {α β : Type*} {G H K G₁ G₂ : Graph α β} {a b s t u v w x y z : α} {e f : β}
  {W : List β} {X : Set α} {F : Set β}

namespace Graph

/-! ### Deleting one vertex -/

theorem mem_deleteVerts_singleton : y ∈ V(G.deleteVerts {x}) ↔ y ∈ V(G) ∧ y ≠ x := by
  simp

theorem mem_deleteVerts_singleton_of_ne (hy : y ∈ V(G)) (hyx : y ≠ x) :
    y ∈ V(G.deleteVerts {x}) :=
  mem_deleteVerts_singleton.2 ⟨hy, hyx⟩

/-- Deleting a vertex the graph does not have leaves the graph alone — on the nose, not merely
up to isomorphism, because `V(G) \ {x}` is literally `V(G)`. -/
theorem deleteVerts_singleton_eq_self (hx : x ∉ V(G)) : G.deleteVerts {x} = G := by
  refine Graph.ext (by simp [sdiff_singleton_eq_self hx]) fun e u v ↦ ?_
  rw [deleteVerts_isLink]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by
    simpa only [mem_singleton_iff] using ne_of_mem_of_not_mem h.left_mem hx, by
    simpa only [mem_singleton_iff] using ne_of_mem_of_not_mem h.right_mem hx⟩⟩

/-- Deleting the same vertices from both sides of an inclusion keeps it. -/
theorem deleteVerts_mono (h : G ≤ H) (X : Set α) : G.deleteVerts X ≤ H.deleteVerts X where
  vertexSet_mono := by
    simp only [vertexSet_deleteVerts]
    exact sdiff_subset_sdiff_left h.vertexSet_mono
  isLink_mono e x y hl := by
    rw [deleteVerts_isLink] at hl ⊢
    exact ⟨h.isLink_mono hl.1, hl.2.1, hl.2.2⟩

/-! ### Walks across a vertex deletion -/

/-- **A walk that never visits `x` survives the deletion of `x`.** Its edges need no separate
argument: the two ends of an edge the walk takes are vertices the walk visits. -/
theorem IsWalk.deleteVerts_singleton (h : G.IsWalk u W v) (hx : x ∉ G.walkVertices u W) :
    (G.deleteVerts {x}).IsWalk u W v := by
  have hux : u ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_self)
  refine h.anti deleteVerts_le (mem_deleteVerts_singleton_of_ne h.left_mem hux) fun g hg ↦ ?_
  obtain ⟨c, d, hcd⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
  have hc : c ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_left⟩)
  have hd : d ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_right⟩)
  rw [edgeSet_deleteVerts]
  exact ⟨c, d, hcd, by simpa using hc, by simpa using hd⟩

/-- **A walk in `G - x` never takes an edge at `x`** — there are none left to take. -/
theorem IsWalk.notMem_of_inc_of_deleteVerts (h : (G.deleteVerts {x}).IsWalk u W v)
    (hx : G.Inc e x) : e ∉ W := by
  intro he
  have hmem := h.edge_mem he
  rw [edgeSet_deleteVerts] at hmem
  obtain ⟨c, d, hcd, hc, hd⟩ := hmem
  obtain ⟨y, hy⟩ := hx
  rcases hy.left_eq_or_eq hcd with rfl | rfl
  exacts [hc rfl, hd rfl]

/-- The bridge between the two deletions: a walk that routes around a vertex `x` cannot have
used an edge incident to `x`, so it is still there after that edge is deleted. -/
theorem Reaches.deleteEdges_of_deleteVerts (h : (G.deleteVerts {x}).Reaches u v)
    (hx : G.Inc e x) : (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨P, hP⟩ := h
  have he : e ∉ P := hP.notMem_of_inc_of_deleteVerts hx
  exact ⟨P, (hP.mono deleteVerts_le).deleteEdges fun g hg hgF ↦ he (mem_singleton_iff.1 hgF ▸ hg)⟩

/-- Connectedness is unharmed by deleting a vertex the graph does not have. -/
theorem Connected.deleteVerts_singleton_of_notMem (h : G.Connected) (hx : x ∉ V(G)) :
    (G.deleteVerts {x}).Connected := by
  rwa [deleteVerts_singleton_eq_self hx]

/-! ### Cut vertices -/

/-- A vertex whose deletion disconnects the graph. -/
def IsCutVertex (G : Graph α β) (x : α) : Prop :=
  x ∈ V(G) ∧ ¬ (G.deleteVerts {x}).Connected

/-! ### At least three vertices -/

/-- The graph has three pairwise distinct vertices. Stated existentially rather than as
`3 ≤ V(G).ncard` so that it is monotone with no finiteness hypothesis. -/
@[expose] def HasThreeVertices (G : Graph α β) : Prop :=
  ∃ a ∈ V(G), ∃ b ∈ V(G), ∃ c ∈ V(G), a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- On a graph with finitely many vertices the clause is the count it is named for. Kept so
that a consumer holding a cardinality is not stranded; nothing in this file uses it. -/
theorem hasThreeVertices_iff_ncard (hV : V(G).Finite) : G.HasThreeVertices ↔ 3 ≤ V(G).ncard :=
  (Set.two_lt_ncard hV).symm

theorem HasThreeVertices.mono (h : G.HasThreeVertices) (hV : V(G) ⊆ V(H)) :
    H.HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  exact ⟨p, hV hp, q, hV hq, r, hV hr, hpq, hpr, hqr⟩

/-- **Any two vertices leave a third over.** This, and not the counting clause itself, is what
every consumer of 2-connectivity uses; the two named vertices need not even be vertices of the
graph. -/
theorem HasThreeVertices.exists_ne_ne (h : G.HasThreeVertices) (u v : α) :
    ∃ w ∈ V(G), w ≠ u ∧ w ≠ v := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  by_contra hcon
  push Not at hcon
  -- Every vertex is `u` or `v`, so the three distinct ones cannot all fit.
  have key : ∀ z ∈ V(G), z = u ∨ z = v := fun z hz ↦ (em (z = u)).imp id (hcon z hz)
  rcases key p hp with rfl | rfl <;> rcases key q hq with rfl | rfl <;>
    rcases key r hr with rfl | rfl <;> simp_all

/-! ### Two-connectivity -/

/-- **The blueprint's convention, verbatim**: at least three vertices, connected, and still
connected after any one vertex is deleted. -/
structure IsTwoConnected (G : Graph α β) : Prop where
  /-- The graph has at least three vertices. -/
  hasThreeVertices : G.HasThreeVertices
  /-- The graph is connected. -/
  connected : G.Connected
  /-- Deleting any one vertex leaves it connected. -/
  deleteVerts_connected : ∀ ⦃x⦄, x ∈ V(G) → (G.deleteVerts {x}).Connected

/-- The deletion clause with its hypothesis dropped: deleting a vertex the graph does not have
changes nothing, so no consumer has to check membership first. -/
theorem IsTwoConnected.deleteVerts_connected' (h : G.IsTwoConnected) (x : α) :
    (G.deleteVerts {x}).Connected := by
  by_cases hx : x ∈ V(G)
  · exact h.deleteVerts_connected hx
  · exact h.connected.deleteVerts_singleton_of_notMem hx

/-- With this convention a 2-connected graph has no cut vertex. -/
theorem IsTwoConnected.no_cut_vertex (h : G.IsTwoConnected) (x : α) : ¬ G.IsCutVertex x :=
  fun hcut ↦ hcut.2 (h.deleteVerts_connected hcut.1)

/-- **A graph on two vertices is never 2-connected**, whatever edges it carries. Two
consequences of the convention at once: the one-edge graph is not 2-connected, and a
two-vertex cycle — two parallel edges, `F` a pair — is a cycle without being 2-connected.
Such cycles do occur in the development, as face boundaries inside a larger 2-connected
graph. -/
theorem not_isTwoConnected_banana (u v : α) (F : Set β) : ¬ (banana u v F).IsTwoConnected := by
  intro h
  obtain ⟨w, hw, hwu, hwv⟩ := h.hasThreeVertices.exists_ne_ne u v
  -- `V(banana u v F)` is `{u, v}` by definition.
  rcases (hw : w ∈ ({u, v} : Set α)) with rfl | rfl
  exacts [hwu rfl, hwv rfl]

/-- **A 2-connected graph has no bridge**, in the form "deleting an edge leaves its two ends
connected" — the hypothesis of the cycle criterion.

The blueprint's proof names the two components of `G - e` and finds a vertex of one of them
other than its endpoint. This proof routes around instead, and never mentions a component: a
third vertex `w` exists; the graph without `v` still joins `u` to `w`, and the graph without
`u` still joins `w` to `v`; and a walk that survives a vertex deletion cannot have used an
edge there, so neither walk used `e`. A loop needs no argument at all. -/
theorem IsTwoConnected.no_bridge (h : G.IsTwoConnected) (hl : G.IsLink e u v) :
    (G.deleteEdges {e}).Reaches u v := by
  rcases eq_or_ne u v with rfl | huv
  · exact Reaches.refl (by simpa using hl.left_mem)
  obtain ⟨w, hw, hwu, hwv⟩ := h.hasThreeVertices.exists_ne_ne u v
  have h₁ : (G.deleteVerts {v}).Reaches u w :=
    (h.deleteVerts_connected' v).reaches (mem_deleteVerts_singleton_of_ne hl.left_mem huv)
      (mem_deleteVerts_singleton_of_ne hw hwv)
  have h₂ : (G.deleteVerts {u}).Reaches w v :=
    (h.deleteVerts_connected' u).reaches (mem_deleteVerts_singleton_of_ne hw hwu)
      (mem_deleteVerts_singleton_of_ne hl.right_mem (Ne.symm huv))
  exact (h₁.deleteEdges_of_deleteVerts hl.inc_right).trans
    (h₂.deleteEdges_of_deleteVerts hl.inc_left)

/-! ### The union of two graphs -/

/-- The union of two graphs. On an edge belonging to both, `G`'s ends win — a resolution is
needed, since two graphs may disagree about the ends of a shared edge name; for
`Graph.Compatible` graphs, which is the only case the development forms, the disjunction
collapses to the naive one. -/
@[expose] protected def union (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
  isLink_symm e _ :=
    { symm := by
        rintro x y (hxy | ⟨he, hxy⟩)
        exacts [Or.inl hxy.symm, Or.inr ⟨he, hxy.symm⟩] }
  eq_or_eq_of_isLink_of_isLink := by
    rintro g x y c d (hxy | ⟨hg, hxy⟩) (hcd | ⟨hg', hcd⟩)
    · exact hxy.left_eq_or_eq hcd
    · exact absurd hxy.edge_mem hg'
    · exact absurd hcd.edge_mem hg
    · exact hxy.left_eq_or_eq hcd
  edge_mem_iff_exists_isLink g := by
    constructor
    · rintro (hg | hg)
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
        exact ⟨x, y, Or.inl hxy⟩
      · by_cases hgG : g ∈ E(G)
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hgG
          exact ⟨x, y, Or.inl hxy⟩
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
          exact ⟨x, y, Or.inr ⟨hgG, hxy⟩⟩
    · rintro ⟨x, y, (hxy | ⟨-, hxy⟩)⟩
      exacts [Or.inl hxy.edge_mem, Or.inr hxy.edge_mem]
  left_mem_of_isLink := by
    rintro g x y (hxy | ⟨-, hxy⟩)
    exacts [Or.inl hxy.left_mem, Or.inr hxy.left_mem]

@[simp]
theorem vertexSet_union (G H : Graph α β) : V(G.union H) = V(G) ∪ V(H) := rfl

@[simp]
theorem edgeSet_union (G H : Graph α β) : E(G.union H) = E(G) ∪ E(H) := rfl

theorem union_isLink :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y) := Iff.rfl

theorem left_le_union (G H : Graph α β) : G ≤ G.union H where
  vertexSet_mono := subset_union_left
  isLink_mono _ _ _ h := Or.inl h

/-- Two subgraphs of one graph have their union inside it. -/
theorem union_le (hGK : G ≤ K) (hHK : H ≤ K) : G.union H ≤ K where
  vertexSet_mono := Set.union_subset hGK.vertexSet_mono hHK.vertexSet_mono
  isLink_mono := by
    rintro g p q (h | ⟨-, h⟩)
    exacts [hGK.isLink_mono h, hHK.isLink_mono h]

/-- The right-hand graph is a subgraph of the union only when the two agree about their shared
edges — without that, no graph has both as subgraphs. -/
theorem Compatible.right_le_union (h : G.Compatible H) : H ≤ G.union H where
  vertexSet_mono := subset_union_right
  isLink_mono e x y hxy := by
    by_cases hg : e ∈ E(G)
    · exact Or.inl ((h.isLink_congr hg hxy.edge_mem).2 hxy)
    · exact Or.inr ⟨hg, hxy⟩

/-- For compatible graphs the union is the naive one. -/
theorem Compatible.union_isLink (h : G.Compatible H) :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  refine ⟨fun hxy ↦ hxy.imp id (·.2), fun hxy ↦ ?_⟩
  rcases hxy with hxy | hxy
  · exact Or.inl hxy
  · exact h.right_le_union.isLink_mono hxy

/-- **Two connected parts covering a graph and sharing a vertex make it connected.** Used
twice below — once for the union itself, once for the union with a vertex deleted — and both
times the two parts are `G` and `H` while the whole is not their union on the nose. -/
theorem Connected.of_two_subgraphs (h₁ : G₁ ≤ K) (h₂ : G₂ ≤ K) (hV : V(K) ⊆ V(G₁) ∪ V(G₂))
    (hc₁ : G₁.Connected) (hc₂ : G₂.Connected) (hs₁ : s ∈ V(G₁)) (hs₂ : s ∈ V(G₂)) :
    K.Connected := by
  refine Connected.of_hub (h₁.vertexSet_mono hs₁) fun z hz ↦ ?_
  rcases hV hz with hz' | hz'
  · exact (hc₁.reaches hs₁ hz').mono h₁
  · exact (hc₂.reaches hs₂ hz').mono h₂

theorem Compatible.union_connected (h : G.Compatible H) (hG : G.Connected) (hH : H.Connected)
    (hs : s ∈ V(G)) (hs' : s ∈ V(H)) : (G.union H).Connected :=
  Connected.of_two_subgraphs (left_le_union G H) h.right_le_union subset_rfl hG hH hs hs'

/-- **`lem:union-two-connected`**: two 2-connected graphs with at least two vertices in common
have 2-connected union.

The blueprint's proof is one sentence — after deleting one vertex, each graph remains
connected and at least one common vertex remains. The work is the case where the deleted
vertex belongs to only one of the two graphs: the other graph never had it, so nothing was
deleted from it, and `Graph.deleteVerts_singleton_eq_self` makes that a rewriting step rather
than an argument. -/
theorem IsTwoConnected.union (hcompat : G.Compatible H) (hG : G.IsTwoConnected)
    (hH : H.IsTwoConnected) (hab : a ≠ b) (haG : a ∈ V(G)) (haH : a ∈ V(H)) (hbG : b ∈ V(G))
    (hbH : b ∈ V(H)) : (G.union H).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G H).vertexSet_mono
  connected := hcompat.union_connected hG.connected hH.connected haG haH
  deleteVerts_connected := by
    intro x _
    -- One of the two common vertices survives the deletion.
    obtain ⟨c, hcG, hcH, hcx⟩ : ∃ c, c ∈ V(G) ∧ c ∈ V(H) ∧ c ≠ x := by
      by_cases ha : a = x
      · exact ⟨b, hbG, hbH, by rintro rfl; exact hab ha⟩
      · exact ⟨a, haG, haH, ha⟩
    refine Connected.of_two_subgraphs (G₁ := G.deleteVerts {x}) (G₂ := H.deleteVerts {x})
      (deleteVerts_mono (left_le_union G H) _) (deleteVerts_mono hcompat.right_le_union _)
      ?_ (hG.deleteVerts_connected' x) (hH.deleteVerts_connected' x)
      (mem_deleteVerts_singleton_of_ne hcG hcx) (mem_deleteVerts_singleton_of_ne hcH hcx)
    simp [union_sdiff_distrib]

end Graph
