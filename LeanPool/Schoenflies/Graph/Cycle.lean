/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Mathlib.Combinatorics.Graph.Delete
import LeanPool.Schoenflies.Graph.Walk

/-!
# Cycles, acyclicity and bridges

This file sits directly on `Schoenflies/Graph/Walk.lean` and answers one question: which
edges of a multigraph lie on a cycle. Its main theorem is the blueprint's cycle criterion —
an edge lies on a cycle exactly when deleting it leaves its two ends joined — and a bridge is
read off it.

## A cycle is presented through one of its edges

`G.IsCycleThrough e u v D` is an edge `e` linking `u` to `v`, together with a **path** `D`
from `u` to `v` that does not use `e`. The closed walk is never assembled.

This is not a weakening. Every question the blueprint asks about a cycle is asked *at an
edge* — is this edge on a cycle, does deleting it disconnect its ends, is it a bridge, can it
be deleted from a spanning subgraph — so the edge is always available to present the cycle
through. And presenting it this way is what makes the definition short: the blueprint's
"connected subgraph in which every vertex has degree exactly two" would have to rule out, by
hand, every repetition that a closed walk can contain, whereas `Graph.IsPath` already forbids
them. The blueprint's own proof of the criterion runs in exactly this shape ("take a shortest
walk from `x` to `y` avoiding `e`; a shortest walk repeats no vertex, so it is a simple
path").

**Length two is included, and is why edges are names.** Two parallel edges — the same pair of
ends, two different names — are a cycle: one of them is `e`, the other is the one-edge path
`D`. The blueprint needs those ("two-vertex cycles do occur below, as boundaries of faces
created by overlays and by ears parallel to an existing edge"), and a walk that named
vertices could not tell the two apart.

## Loops

Mathlib's `Graph` allows an edge with both ends equal. **A loop is taken to be a cycle of
length one**, which is the usual convention and also what the blueprint's own definition
gives (a loop contributes two to the degree of its vertex, so the subgraph consisting of a
loop and its vertex is connected with every vertex of degree two). It comes out of the
definition here for free: `G.IsLink e x x` together with the empty path at `x`, which does
not use `e`, is a cycle through `e`. So `Graph.liesOnCycle_of_isLoopAt` needs no proof, no
graph is acyclic while carrying a loop, and no bridge is a loop. Nothing in this file
hypothesises looplessness.

## Deletion

Edge deletion is Mathlib's `Graph.deleteEdges`, not a new definition; `G.deleteEdges {e}` is
the graph with the single name `e` removed. What this file adds is the transfer interface —
a walk or a path survives a deletion exactly when it never took a deleted edge — which is the
whole content of a deletion argument, since which vertices an edge joins is not a question a
subgraph can answer differently. `Graph.IsWalk.anti` from `Walk.lean` is the engine;
`Graph.IsPath.anti` is proved here, since freshness has to be carried down too.

## Blueprint

* `Graph.liesOnCycle_iff_deleteEdges_reaches` — `lem:cycle-criterion`, "in a finite graph, an
  edge lies on a cycle if and only if deleting it does not disconnect its endpoints", both
  directions, with the finiteness the proof does not use dropped. The two halves are
  `Graph.LiesOnCycle.deleteEdges_reaches` and `Graph.LiesOnCycle.of_deleteEdges_reaches`.
* `Graph.IsBridge`, `Graph.isBridge_iff_not_reaches` — the bridges of
  `lem:subdivision-ear-preserve` ("a 2-connected graph has no bridge. Indeed, if `uv` were a
  bridge, the two components of `G - uv` …"), stated as the separation of the two ends.
* `Graph.IsAcyclic`, `Graph.Connected.deleteEdges_singleton` — the acyclicity underneath
  `lem:three-leaf-tree`, and the minimal spanning subgraph of the H5 construction ("take a
  minimal connected subgraph `T_i` spanning the three terminals. It is a tree: an edge of a
  cycle could be deleted"), which is exactly the statement that deleting an edge on a cycle
  keeps the graph connected.
* `Graph.IsPath.chord_liesOnCycle`, `Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices` — the
  step of `lem:three-leaf-tree`'s proof that says "a second neighbor on the path would close
  a cycle"; the form the tree module's longest-path argument consumes.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

namespace Graph

/-! ### Visited vertices along an inclusion

`Walk.lean` proves `walkVertices` monotone in the edge list. It is also monotone in the
graph, which is what pulling a path *down* into a subgraph needs: the freshness clause of a
path speaks about the subgraph's visited set, and that is the smaller one. -/

/-! ### Edge deletion

`Graph.deleteEdges` is Mathlib's. These are the four transfer lemmas every deletion argument
below reduces to. -/

/-- Deleting edges never removes a vertex, so a walk in the deletion is a walk. -/
theorem IsWalk.of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) : G.IsWalk u W v :=
  h.mono deleteEdges_le

/-- Conversely, a walk in the deletion could not have used a deleted name. -/
theorem IsWalk.notMem_of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) (hf : f ∈ W) :
    f ∉ F :=
  (mem_edgeSet_deleteEdges_iff.1 (h.edge_mem hf)).2

theorem IsPath.of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) : G.IsPath u W v :=
  h.mono deleteEdges_le

theorem IsPath.deleteEdges (h : G.IsPath u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsPath u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

theorem IsPath.notMem_of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) (hf : f ∈ W) :
    f ∉ F :=
  h.isWalk.notMem_of_deleteEdges hf

theorem Reaches.of_deleteEdges (h : (G.deleteEdges F).Reaches u v) : G.Reaches u v :=
  h.mono deleteEdges_le

theorem IsWalk.reaches_deleteEdges (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).Reaches u v :=
  ⟨W, h.deleteEdges hW⟩

/-! ### Cycles -/

/-- `G.IsCycleThrough e u v D` : the edge `e` links `u` to `v`, and `D` is a path from `u`
back to `v` that does not use `e`. The cycle is `e` together with `D`; it is presented
through `e` because that is the edge every question is asked about. -/
def IsCycleThrough (G : Graph α β) (e : β) (u v : α) (D : List β) : Prop :=
  G.IsLink e u v ∧ G.IsPath u D v ∧ e ∉ D

/-- `G.LiesOnCycle e` : the edge `e` lies on a cycle of `G`. -/
def LiesOnCycle (G : Graph α β) (e : β) : Prop := ∃ u v D, G.IsCycleThrough e u v D

theorem IsCycleThrough.isLink (h : G.IsCycleThrough e u v D) : G.IsLink e u v := h.1

theorem IsCycleThrough.isPath (h : G.IsCycleThrough e u v D) : G.IsPath u D v := h.2.1

theorem IsCycleThrough.notMem (h : G.IsCycleThrough e u v D) : e ∉ D := h.2.2

theorem IsCycleThrough.liesOnCycle (h : G.IsCycleThrough e u v D) : G.LiesOnCycle e :=
  ⟨u, v, D, h⟩

theorem liesOnCycle_iff : G.LiesOnCycle e ↔ ∃ u v D, G.IsCycleThrough e u v D := Iff.rfl

/-- An edge on a cycle is an edge of the graph. There is no converse hypothesis to carry
around: `Graph.IsLink` already forces it. -/
theorem LiesOnCycle.edge_mem (h : G.LiesOnCycle e) : e ∈ E(G) :=
  let ⟨_, _, _, hc⟩ := h; hc.isLink.edge_mem

/-- **A loop is a cycle of length one.** The path back is the empty one, which trivially
avoids the loop. -/
theorem liesOnCycle_of_isLoopAt (h : G.IsLoopAt e x) : G.LiesOnCycle e :=
  ⟨x, x, [], h, .nil h.left_mem, List.not_mem_nil⟩

/-- **Two parallel edges are a cycle**, on both of them. This is the length-two case, and the
reason a walk names its edges. -/
theorem liesOnCycle_of_parallel (h : G.IsLink e u v) (h' : G.IsLink f u v) (hef : e ≠ f) :
    G.LiesOnCycle e := by
  by_cases huv : u = v
  · subst huv
    exact liesOnCycle_of_isLoopAt h
  exact ⟨u, v, [f], h, .single h' huv, by simpa using hef⟩

/-- A cycle of a subgraph is a cycle of the graph. -/
theorem LiesOnCycle.mono (hHG : H ≤ G) (h : H.LiesOnCycle e) : G.LiesOnCycle e :=
  let ⟨u, v, D, hl, hP, hD⟩ := h
  ⟨u, v, D, hl.mono hHG, hP.mono hHG, hD⟩

/-! ### The cycle criterion

The blueprint's `lem:cycle-criterion`. Both directions are one step each, once the deletion
interface above is in place: forwards, the detour of the cycle is a walk that avoided `e`;
backwards, a path in the deletion cannot have used `e` because `e` is not there. -/

/-- **An edge on a cycle is not needed to join its ends**: the rest of the cycle still does.

The ends are given as an arbitrary pair `u, v` that `e` links, not as the pair the cycle was
presented with — an edge has only two ends, so the two presentations agree up to a swap, and
reachability is symmetric. -/
theorem LiesOnCycle.deleteEdges_reaches (hl : G.IsLink e u v) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨u', v', D, hl', hP, hD⟩ := h
  -- The detour avoids `e` by definition, so it is still there after `e` goes.
  have hR : (G.deleteEdges {e}).Reaches u' v' :=
    hP.isWalk.reaches_deleteEdges fun f hf hmem ↦ hD (Set.mem_singleton_iff.1 hmem ▸ hf)
  rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hR, hR.symm]

/-- **An edge whose deletion leaves its ends joined lies on a cycle.** The route that
survives is a walk of the deletion, hence contains a path of the deletion, and a path of the
deletion cannot have used the name that was deleted. -/
theorem LiesOnCycle.of_deleteEdges_reaches (hl : G.IsLink e u v)
    (h : (G.deleteEdges {e}).Reaches u v) : G.LiesOnCycle e := by
  obtain ⟨D, hD⟩ := h.exists_isPath
  exact ⟨u, v, D, hl, hD.of_deleteEdges, fun hmem ↦ hD.notMem_of_deleteEdges hmem rfl⟩

/-- **The cycle criterion**: an edge lies on a cycle if and only if deleting it does not
disconnect its endpoints. -/
theorem liesOnCycle_iff_deleteEdges_reaches (hl : G.IsLink e u v) :
    G.LiesOnCycle e ↔ (G.deleteEdges {e}).Reaches u v :=
  ⟨LiesOnCycle.deleteEdges_reaches hl, LiesOnCycle.of_deleteEdges_reaches hl⟩

/-- **A walk reroutes around an edge that lies on a cycle**: wherever it took `e`, it can go
the long way round instead. Proved by induction along the walk rather than by splicing the
detour into the edge list, so nothing has to be said about what the spliced list looks
like. -/
theorem IsWalk.reaches_deleteEdges_of_liesOnCycle (h : G.LiesOnCycle e) (hW : G.IsWalk u W v) :
    (G.deleteEdges {e}).Reaches u v := by
  induction hW with
  | nil hx => exact .refl (by simpa using hx)
  | @cons u w v f W hl _ ih =>
    refine Reaches.trans ?_ ih
    by_cases hfe : f = e
    · subst hfe
      exact h.deleteEdges_reaches hl
    · refine (IsWalk.single hl).reaches_deleteEdges fun g hg ↦ ?_
      obtain rfl : g = f := by simpa using hg
      simpa using hfe

/-- **Deleting an edge that lies on a cycle keeps the graph connected** — the blueprint's "it
is a tree: an edge of a cycle could be deleted", which is what makes a minimal connected
spanning subgraph acyclic. -/
theorem Connected.deleteEdges_singleton (hG : G.Connected) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Connected := by
  refine ⟨by simpa using hG.nonempty, fun u hu v hv ↦ ?_⟩
  rw [vertexSet_deleteEdges] at hu hv
  exact (hG.reaches hu hv).choose_spec.reaches_deleteEdges_of_liesOnCycle h

/-! ### Chords

An edge from the source of a path to a vertex the path already visits closes a cycle. This
is the shape in which acyclicity is used: it says a path cannot be extended backwards onto
itself. -/

/-- A chord of a path lies on a cycle: the piece of the path from its source to the far end
of the chord is a path avoiding the chord, so the chord closes it. -/
theorem IsPath.chord_liesOnCycle (hP : G.IsPath u P v) (hl : G.IsLink e u x) (hoff : e ∉ P)
    (hx : x ∈ G.walkVertices u P) : G.LiesOnCycle e := by
  obtain ⟨P₁, P₂, rfl, h₁, -, -⟩ := hP.split hx
  exact ⟨u, x, P₁, hl, h₁, fun hmem ↦ hoff (List.mem_append_left _ hmem)⟩

/-! ### Acyclicity -/

/-- `G.IsAcyclic` : no edge of `G` lies on a cycle. Stated over the edges of `G` because that
is how a tree consumes it — every edge is a bridge — while `Graph.IsAcyclic.not_liesOnCycle`
drops the membership hypothesis for the uses that do not have it to hand. -/
def IsAcyclic (G : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → ¬ G.LiesOnCycle e

/-- Acyclicity with no membership hypothesis: an edge on a cycle would be an edge. -/
theorem IsAcyclic.not_liesOnCycle (h : G.IsAcyclic) (e : β) : ¬ G.LiesOnCycle e :=
  fun hc ↦ h hc.edge_mem hc

theorem isAcyclic_iff : G.IsAcyclic ↔ ∀ e, ¬ G.LiesOnCycle e :=
  ⟨fun h e ↦ h.not_liesOnCycle e, fun h _ _ ↦ h _⟩

/-- **An acyclic graph has no loop.** No hypothesis is needed anywhere else in this layer
because of this: looplessness is a consequence of acyclicity, not a side condition on it. -/
theorem IsAcyclic.not_isLoopAt (h : G.IsAcyclic) (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle e (liesOnCycle_of_isLoopAt hloop)

/-- **An acyclic graph has no parallel edges.** -/
theorem IsAcyclic.eq_of_isLink (h : G.IsAcyclic) (hl : G.IsLink e u v) (hl' : G.IsLink f u v) :
    e = f := by
  by_contra hef
  exact h.not_liesOnCycle e (liesOnCycle_of_parallel hl hl' hef)

/-- A subgraph of an acyclic graph is acyclic. -/
theorem IsAcyclic.anti (hHG : H ≤ G) (h : G.IsAcyclic) : H.IsAcyclic :=
  fun _ _ hc ↦ h.not_liesOnCycle _ (hc.mono hHG)

theorem IsAcyclic.deleteEdges (h : G.IsAcyclic) (F : Set β) : (G.deleteEdges F).IsAcyclic :=
  h.anti deleteEdges_le

/-- **In an acyclic graph, an edge at the source of a path whose far end the path visits is
one of the path's own edges.** This is the blueprint's "a second neighbor on the path would
close a cycle" — the step that makes the end of a longest path a leaf, which is what the tree
module runs on. -/
theorem IsAcyclic.mem_of_isLink_of_mem_walkVertices (hac : G.IsAcyclic) (hP : G.IsPath u P v)
    (hl : G.IsLink e u x) (hx : x ∈ G.walkVertices u P) : e ∈ P := by
  by_contra hoff
  exact hac.not_liesOnCycle e (hP.chord_liesOnCycle hl hoff hx)

/-! ### Bridges -/

/-- `G.IsBridge e` : an edge of `G` that lies on no cycle. Equivalently — and this is the
form every use wants — an edge whose deletion separates its two ends
(`Graph.isBridge_iff_not_reaches`). -/
def IsBridge (G : Graph α β) (e : β) : Prop := e ∈ E(G) ∧ ¬ G.LiesOnCycle e

theorem IsBridge.edge_mem (h : G.IsBridge e) : e ∈ E(G) := h.1

theorem IsBridge.not_liesOnCycle (h : G.IsBridge e) : ¬ G.LiesOnCycle e := h.2

/-- **Deleting a bridge separates its ends.** -/
theorem IsBridge.not_reaches (h : G.IsBridge e) (hl : G.IsLink e u v) :
    ¬ (G.deleteEdges {e}).Reaches u v :=
  fun hR ↦ h.not_liesOnCycle (LiesOnCycle.of_deleteEdges_reaches hl hR)

/-- **An edge whose deletion separates its ends is a bridge.** -/
theorem isBridge_of_not_reaches (hl : G.IsLink e u v)
    (h : ¬ (G.deleteEdges {e}).Reaches u v) : G.IsBridge e :=
  ⟨hl.edge_mem, fun hc ↦ h (hc.deleteEdges_reaches hl)⟩

/-- **A bridge is exactly an edge whose deletion separates its ends** — the cycle criterion,
negated. -/
theorem isBridge_iff_not_reaches (hl : G.IsLink e u v) :
    G.IsBridge e ↔ ¬ (G.deleteEdges {e}).Reaches u v :=
  ⟨fun h ↦ h.not_reaches hl, isBridge_of_not_reaches hl⟩

/-- A bridge is never a loop: a loop is a cycle. -/
theorem IsBridge.not_isLoopAt (h : G.IsBridge e) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle (liesOnCycle_of_isLoopAt hloop)

/-- **A graph is acyclic exactly when every one of its edges is a bridge.** This is the form
the tree module wants acyclicity in: "it is a tree — an edge of a cycle could be deleted"
reads backwards as "no edge can be deleted without separating its ends". -/
theorem isAcyclic_iff_forall_isBridge : G.IsAcyclic ↔ ∀ e ∈ E(G), G.IsBridge e :=
  ⟨fun h _ he ↦ ⟨he, h he⟩, fun h _ he ↦ (h _ he).not_liesOnCycle⟩

theorem IsAcyclic.isBridge (h : G.IsAcyclic) (he : e ∈ E(G)) : G.IsBridge e := ⟨he, h he⟩

end Graph
