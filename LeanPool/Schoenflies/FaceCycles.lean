/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Graph.CycleJordan
import LeanPool.Schoenflies.Graph.RelativeEar
import LeanPool.Schoenflies.Graph.OuterFace
import LeanPool.Schoenflies.Subarc

/-!
# Face cycles: the base cycle, and the faces of a plane graph that grows by ears

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as
its boundary and is one of the two complementary regions of that cycle* — is proved by growing
the graph from a cycle by ears (`Graph.IsTwoConnected.ear_decomposition`) and applying
`thm:polygonal-crosscut` at each step. This file supplies everything in that proof that is not
the crosscut application itself. **The lemma is not proved here**; see "What is missing" below,
which says exactly what is in the way.

## The base cycle

The blueprint's first paragraph, in full. *"First choose a cycle of length at least three.
Such a cycle exists: under our convention the graph has at least three vertices, and every
vertex has at least two distinct neighbors. Indeed, if a vertex `v` had only one distinct
neighbor `w`, then deleting `w` would isolate `v` from some third vertex, contrary to
2-connectivity. Now take a maximal simple path. An endpoint has a neighbor on the path other
than its predecessor, and the resulting closed subpath is a cycle of length at least three."*

`Graph.IsTwoConnected.exists_adj_ne` is the two-neighbours sentence; "take a maximal simple
path" is `Graph.exists_longest_path`, already in `Schoenflies/Graph/Tree.lean` and not rebuilt
here; and `Graph.IsTwoConnected.exists_long_cycle` is the conclusion, packaged as
`Graph.IsLongCycle`, a cycle together with a *named* third vertex. Naming the third vertex
rather than counting is what both consumers want: the counting clause of
`Graph.IsTwoConnected`, and — later — the non-degeneracy of the polygon the cycle draws.

`Graph.cycleGraph` is that cycle as a subgraph, and `Graph.IsLongCycle.isTwoConnected` is
*"the cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`"*. This
is the one place "length at least three" is used: a two-vertex cycle is a `Graph.banana`, and
`Graph.not_isTwoConnected_banana` says it is not 2-connected.

## One step of the induction

Adding an ear removes the ear's own point set from the exterior and changes nothing else:
`Graph.pointSet_union`, `Graph.exterior_union` and `Graph.face_union_eq_of_disjoint` are
*"all other faces are unchanged"*.

`Graph.IsDrawing.exists_face_of_ear` is *"its interior is connected and disjoint from the
current graph, so it lies in one current face `F`"*: the ear's realisation without its two ends
is the interior of an arc, hence connected
(`Schoenflies.IsArcBetween.isConnected_diff`), and it misses the drawing of the current
subgraph altogether (`Graph.IsDrawing.edgesCover_inter_pointSet`).
`Graph.IsDrawing.ends_mem_frontier_face` is the next sentence, *"the ear's two endpoints are
limits of its interior, which lies in `F`, so they lie on `∂F`"* — which is what makes the ear
a crosscut of that face.

`Graph.IsDrawing.mono` — a subgraph of a plane graph is a plane graph, with the same drawing —
is what lets the induction talk about the faces of the current subgraph at all.

## An interface repair

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)`, which `Graph.IsTwoConnected.relative_ear_exists` proves and which
`Graph.IsTwoConnected.relative_grows_by_ear` drops on the way. A geometric consumer needs it:
without it the ear may be drawn right on top of the current subgraph, and
`Graph.IsDrawing.edgesCover_inter_pointSet` is false. `Graph.ear_edges_notMem_or_union_eq`
recovers it in the only form available from the outside — either every edge of the ear is new,
or the ear is a single edge the subgraph already had and the enlarged graph *is* the old graph,
so the step has nothing to prove. The better fix is for the integrator to add the clause to
`relative_grows_by_ear` and to `ear_decomposition`; that would make this lemma unnecessary.

## What is missing

The crosscut application, and therefore `lem:face-cycles` itself. `thm:polygonal-crosscut` is
available as `Schoenflies.IsPolygonalCrosscut` and `Schoenflies.polygonal_crosscut`, whose
hypotheses are stated for `Schoenflies.ClosedPolygon`s: an explicit cyclic vertex list with
`vertex_inj`, `edges_meet` and `corner` (no two consecutive edges collinear). The realisation
of a graph cycle arrives here as a **set** — `Graph.edgesCover drawing (e :: D)` — which
`Graph.IsDrawing.cycle_isJordanCurve` knows to be a Jordan curve and `Graph.polygonal_redrawing`
knows to be polygonal. Turning such a set into a `ClosedPolygon` (enumerate its vertices
cyclically, delete the redundant collinear ones, and derive `vertex_inj` and `edges_meet` from
simplicity) is a construction `main` does not have, and the same construction is needed again
for the two curves `Aᵢ ∪ P` that the crosscut produces. Nothing below pretends to it, and no
statement below is weaker than its blueprint counterpart.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`. The two arc lemmas are stated in
`Schoenflies`, where the rest of the arc theory lives.

## Blueprint

* `Graph.IsTwoConnected.exists_adj_ne` — "every vertex has at least two distinct neighbors".
* `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle` — "the resulting closed subpath
  is a cycle of length at least three".
* `Graph.cycleGraph`, `Graph.IsLongCycle.isTwoConnected` — "the cycle `C` is 2-connected, so
  Lemma `lem:relative-ear` builds the graph from `C`".
* `Graph.ear_edges_notMem_or_union_eq` — the ear's edges are new, or the ear is not an ear.
* `Graph.pointSet_union`, `Graph.exterior_union`, `Graph.face_union_subset`,
  `Graph.face_union_eq_of_disjoint` — "all other faces are unchanged".
* `Graph.IsDrawing.mono` — the current subgraph is itself a plane graph.
* `Schoenflies.IsArcBetween.isConnected_diff`,
  `Schoenflies.IsArcBetween.left_mem_closure_diff`, `…right_mem_closure_diff`,
  `Graph.IsDrawing.edgesCover_inter_pointSet`, `Graph.IsDrawing.exists_face_of_ear`,
  `Graph.IsDrawing.ends_mem_frontier_face` — "its interior is connected and disjoint from the
  current graph, so it lies in one current face `F` … the ear's two endpoints are limits of its
  interior, which lies in `F`, so they lie on `∂F`; the ear is therefore a crosscut of that
  side".
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K B : Graph α β} {u v w x y z c : α} {e f g : β} {D W : List β}

/-! ## Two distinct neighbours -/

/-- **A vertex of a loopless 2-connected graph has a neighbour other than any prescribed
vertex** — in particular it has two distinct neighbours, and neither is itself. -/
theorem IsTwoConnected.exists_adj_ne (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) (hv : v ∈ V(G)) (w : α) :
    ∃ x, G.Adj v x ∧ x ≠ w := by
  rcases eq_or_ne v w with rfl | hvw
  · -- Deleting nothing: a walk to any other vertex leaves along a non-loop.
    obtain ⟨z, hz, hzv, -⟩ := h.hasThreeVertices.exists_ne_ne v v
    obtain ⟨T, hT⟩ := h.connected.reaches hv hz
    cases hT with
    | nil => exact absurd rfl hzv
    | @cons _ y _ g _ hl _ => exact ⟨y, ⟨g, hl⟩, fun hh ↦ hnl (hh ▸ hl)⟩
  · -- Deleting `w`: a walk to a third vertex leaves along an edge that survived it.
    obtain ⟨z, hz, hzv, hzw⟩ := h.hasThreeVertices.exists_ne_ne v w
    obtain ⟨T, hT⟩ := (h.deleteVerts_connected' w).reaches
      (mem_deleteVerts_singleton_of_ne hv hvw) (mem_deleteVerts_singleton_of_ne hz hzw)
    cases hT with
    | nil => exact absurd rfl (Ne.symm hzv)
    | @cons _ y _ g _ hl _ =>
      exact ⟨y, ⟨g, hl.mono deleteVerts_le⟩, (mem_deleteVerts_singleton.1 hl.right_mem).2⟩

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

/-- **A path from a vertex back to itself is empty.** The first step would depart from the
vertex the rest of the path arrives at, which the freshness clause forbids. -/
theorem IsPath.eq_nil_of_eq (h : G.IsPath u W u) : W = [] := by
  cases h with
  | nil => rfl
  | cons _ hT hfresh => exact absurd hT.target_mem_walkVertices hfresh

/-- A cycle with at least three vertices — the blueprint's "cycle of length at least three".
The third vertex is named rather than counted, because that is what both consumers want. -/
structure IsLongCycle (G : Graph α β) (e : β) (u v : α) (D : List β) (w : α) : Prop where
  /-- The edge and the detour form a cycle. -/
  isCycle : G.IsCycleThrough e u v D
  /-- The detour visits a third vertex … -/
  mem : w ∈ G.walkVertices u D
  /-- … distinct from the source of the edge … -/
  ne_left : w ≠ u
  /-- … and from its target. -/
  ne_right : w ≠ v

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem isLink : G.IsLink e u v := h.isCycle.isLink

theorem isPath : G.IsPath u D v := h.isCycle.isPath

theorem notMem : e ∉ D := h.isCycle.notMem

/-- The two ends of the edge are distinct: otherwise the detour would be a path from a vertex
to itself, hence empty, and would visit no third vertex. -/
theorem ne : u ≠ v := by
  rintro rfl
  have hnil : D = [] := h.isPath.eq_nil_of_eq
  have hmem := h.mem
  rw [hnil, walkVertices_nil] at hmem
  exact h.ne_left hmem

end IsLongCycle

/-- **"The resulting closed subpath is a cycle of length at least three."** A finite loopless
2-connected graph has a cycle with three distinct vertices.

Take a maximal path `u —W→ v`. Its source `u` has a neighbour `x` other than the vertex `w₀`
the path first steps to (`Graph.IsTwoConnected.exists_adj_ne`), and `x` lies on the path:
otherwise the edge to it could be prepended, contradicting maximality. Cutting the path at `x`
gives a path from `u` to `x` whose first step is still to `w₀`, and the chord closes it into a
cycle through `u`, `w₀` and `x`. The chord is not an edge of that piece: an edge at `u` in the
tail is what the path's freshness clause forbids, and the first edge is not the chord because
their far ends differ. -/
theorem IsTwoConnected.exists_long_cycle [G.Finite] (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) :
    ∃ g u x D w, G.IsLongCycle g u x D w := by
  obtain ⟨p, hp, -⟩ := h.hasThreeVertices
  obtain ⟨u, v, W, hpath, hmax⟩ := exists_longest_path hp
  -- The maximal path is not empty: an edge at its source could otherwise be prepended.
  obtain ⟨f, W', rfl⟩ : ∃ f W', W = f :: W' := by
    cases hW : W with
    | cons f W' => exact ⟨f, W', rfl⟩
    | nil =>
      obtain ⟨y, ⟨g, hl⟩, hyu⟩ := h.exists_adj_ne hnl hpath.left_mem u
      have hle := hmax _ _ _ (IsPath.single hl.symm hyu)
      rw [hW] at hle
      simp at hle
  obtain ⟨w₀, hl₀, hpath', hfresh⟩ : ∃ w₀, G.IsLink f u w₀ ∧ G.IsPath w₀ W' v ∧
      u ∉ G.walkVertices w₀ W' := by
    cases hpath with
    | cons hl hW hfr => exact ⟨_, hl, hW, hfr⟩
  -- A second neighbour of the source, distinct from the vertex the path first steps to.
  obtain ⟨x, ⟨g, hlg⟩, hxw₀⟩ := h.exists_adj_ne hnl hpath.left_mem w₀
  have hxu : x ≠ u := fun hh ↦ hnl (hh ▸ hlg)
  -- It lies on the path: otherwise the chord would prepend to it.
  have hxW : x ∈ G.walkVertices u (f :: W') := by
    by_contra hx
    have hle := hmax _ _ _ (IsPath.cons hlg.symm hpath hx)
    simp at hle
  obtain ⟨W₁, W₂, hsplit, h₁, -, -⟩ := hpath.split hxW
  have hW₁sub : W₁ ⊆ f :: W' := hsplit ▸ List.subset_append_left _ _
  -- The chord is not an edge of the piece: not the first edge, and not one further along.
  have hgW₁ : g ∉ W₁ := by
    intro hg
    rcases List.mem_cons.1 (hW₁sub hg) with rfl | hg'
    · exact hxw₀ (hlg.right_unique hl₀)
    · exact hfresh (mem_walkVertices_of_mem_covered ⟨g, hg', hlg.inc_left⟩)
  -- The piece starts with the first edge, so it visits the vertex the path first stepped to.
  have hfW₁ : f ∈ W₁ := by
    rcases W₁ with _ | ⟨a, T⟩
    · exact absurd h₁.isWalk.eq_of_nil (Ne.symm hxu)
    · obtain ⟨rfl, -⟩ : f = a ∧ W' = T ++ W₂ := by simpa using hsplit
      exact List.mem_cons_self
  exact ⟨g, u, x, W₁, w₀, ⟨hlg, h₁, hgW₁⟩,
    mem_walkVertices_of_mem_covered ⟨f, hfW₁, hl₀.inc_right⟩,
    fun hh ↦ hnl (hh ▸ hl₀), Ne.symm hxw₀⟩

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

/-- **A path graph grows with its edge list.** General, and not in
`Schoenflies/Graph/PathGraph.lean`; the integrator may want to hoist it. -/
theorem pathGraphOf_mono (h : W ⊆ D) : G.pathGraphOf u W ≤ G.pathGraphOf u D where
  vertexSet_mono := by
    simpa only [pathGraphOf_vertexSet] using walkVertices_mono (u := u) h
  isLink_mono := by
    intro f x y hl
    obtain ⟨hf, hxy, hx, hy⟩ := pathGraphOf_isLink.1 hl
    exact pathGraphOf_isLink.2
      ⟨h hf, hxy, walkVertices_mono h hx, walkVertices_mono h hy⟩

/-- The subgraph of `G` drawn by a cycle: the detour followed by the edge, as a closed walk.
Exported as the object rather than hidden behind an existential — the consumer of
`lem:face-cycles` needs the graph itself, to feed it to the ear decomposition. -/
def cycleGraph (G : Graph α β) (u : α) (e : β) (D : List β) : Graph α β :=
  G.pathGraphOf u (D ++ [e])

/-- The detour spans a path subgraph of the cycle. -/
theorem pathGraphOf_le_cycleGraph : G.pathGraphOf u D ≤ G.cycleGraph u e D :=
  pathGraphOf_mono (List.subset_append_left _ _)

namespace IsCycleThrough

variable (hc : G.IsCycleThrough e u v D)
include hc

/-- Going round: the detour and then the edge is a closed walk at the source. -/
theorem isWalk_round : G.IsWalk u (D ++ [e]) u :=
  hc.isPath.isWalk.append (IsWalk.single hc.isLink.symm)

/-- Closing the cycle adds no vertex: both ends of the edge are already on the detour. -/
theorem walkVertices_round : G.walkVertices u (D ++ [e]) = G.walkVertices u D := by
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (walkVertices_mono (List.subset_append_left _ _))
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with hcov | ⟨g, hg, hinc⟩
  · exact mem_walkVertices_of_mem_covered hcov
  obtain rfl : g = e := by simpa using hg
  rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
  · exact mem_walkVertices_self
  · exact hc.isPath.target_mem_walkVertices

@[simp]
theorem cycleGraph_vertexSet : V(G.cycleGraph u e D) = G.walkVertices u D := by
  rw [cycleGraph, pathGraphOf_vertexSet, hc.walkVertices_round]

theorem cycleGraph_le : G.cycleGraph u e D ≤ G := pathGraphOf_le hc.isWalk_round

theorem cycleGraph_edgeSet : E(G.cycleGraph u e D) = {f | f ∈ D ++ [e]} :=
  pathGraphOf_edgeSet hc.isWalk_round

theorem left_mem_cycleGraph : u ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact mem_walkVertices_self

theorem right_mem_cycleGraph : v ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact hc.isPath.target_mem_walkVertices

/-- The edge of the cycle really is an edge of the cycle graph, joining the same two ends. -/
theorem cycleGraph_isLink : (G.cycleGraph u e D).IsLink e u v :=
  pathGraphOf_isLink.2 ⟨by simp, hc.isLink,
    hc.walkVertices_round ▸ mem_walkVertices_self,
    hc.walkVertices_round ▸ hc.isPath.target_mem_walkVertices⟩

/-- The cycle graph is connected: every vertex it has is visited by the detour, and the
detour's own prefix runs there from the source. -/
theorem cycleGraph_connected : (G.cycleGraph u e D).Connected := by
  refine Connected.of_hub hc.left_mem_cycleGraph fun x hx ↦ ?_
  rw [hc.cycleGraph_vertexSet] at hx
  obtain ⟨W₁, W₂, hcat, h₁, -, -⟩ := hc.isPath.split hx
  refine ⟨W₁, h₁.isWalk.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg ↦ ?_⟩
  rw [hc.cycleGraph_edgeSet]
  exact List.mem_append_left _ (hcat ▸ List.mem_append_left _ hg)

end IsCycleThrough

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem mem_cycleGraph : w ∈ V(G.cycleGraph u e D) := by
  rw [h.isCycle.cycleGraph_vertexSet]; exact h.mem

/-- **A cycle with three vertices is 2-connected**, which is what
`Graph.IsTwoConnected.ear_decomposition` asks of its starting subgraph.

Delete a vertex `c`. One of the two ends of the cycle's edge survives, and it is the hub:
every remaining vertex reaches an end of the *detour* inside the detour
(`Graph.IsPathGraph.reaches_an_end`), an end which — having been reached after the deletion —
survived it too, so the cycle's edge is still there to carry it the rest of the way. -/
theorem isTwoConnected : (G.cycleGraph u e D).IsTwoConnected where
  hasThreeVertices :=
    ⟨u, h.isCycle.left_mem_cycleGraph, v, h.isCycle.right_mem_cycleGraph,
      w, h.mem_cycleGraph, h.ne, Ne.symm h.ne_left, Ne.symm h.ne_right⟩
  connected := h.isCycle.cycleGraph_connected
  deleteVerts_connected := by
    intro c _
    set Kc := G.cycleGraph u e D with hKc
    set Pc := G.pathGraphOf u D with hPc
    have hPK : Pc.deleteVerts {c} ≤ Kc.deleteVerts {c} :=
      deleteVerts_mono pathGraphOf_le_cycleGraph _
    have hPpath : Pc.IsPathGraph u D v := h.isPath.isPathGraph_pathGraphOf
    -- The hub is whichever end of the cycle's edge survived; the argument is symmetric in
    -- the two, so it is done once for a named pair and applied twice.
    have main : ∀ a b : α, Kc.IsLink e a b → a ≠ c →
        (∀ x ∈ V(Kc), x ≠ c →
          (Pc.deleteVerts {c}).Reaches x a ∨ (Pc.deleteVerts {c}).Reaches x b) →
        (Kc.deleteVerts {c}).Connected := by
      intro a b hab hac hends
      refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hab.left_mem hac) fun x hx ↦ ?_
      rw [vertexSet_deleteVerts] at hx
      obtain ⟨hxK, hxc⟩ := hx
      have hxc' : x ≠ c := by simpa using hxc
      rcases hends x hxK hxc' with hr | hr
      · exact (hr.mono hPK).symm
      · -- The far end was reached, so it survived; the cycle's edge joins it to the hub.
        have hbc : b ≠ c := (mem_deleteVerts_singleton.1 (hr.mono hPK).right_mem).2
        have hedge : (Kc.deleteVerts {c}).Reaches b a :=
          ⟨[e], IsWalk.single ((deleteVerts_isLink _ _).2 ⟨hab.symm, by simpa using hbc,
            by simpa using hac⟩)⟩
        exact ((hr.mono hPK).trans hedge).symm
    have hV : ∀ x ∈ V(Kc), x ∈ V(Pc) := fun x hx ↦ by
      rw [hKc, h.isCycle.cycleGraph_vertexSet] at hx; exact hx
    by_cases hcu : u = c
    · -- The source is gone, so the target is the hub.
      refine main v u h.isCycle.cycleGraph_isLink.symm (fun hh ↦ h.ne (hh.trans hcu.symm).symm)
        fun x hx hxc ↦ (hPpath.reaches_an_end (hV x hx) hxc).symm
    · exact main u v h.isCycle.cycleGraph_isLink hcu
        fun x hx hxc ↦ hPpath.reaches_an_end (hV x hx) hxc

end IsLongCycle


/-- A machine check that the two halves fit: the base cycle really is a legal starting point
for `Graph.IsTwoConnected.ear_decomposition`, so a consumer that can do the base case on
`G.cycleGraph u e D` and the ear step gets the conclusion for `G`. Nothing but the two
theorems is used. -/
example {motive : Graph α β → Prop} [G.Finite] (hG : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (base : ∀ (e : β) (u v : α) (D : List β) (w : α), G.IsLongCycle e u v D w →
      motive (G.cycleGraph u e D))
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → B ≤ G → motive B →
      G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  exact hG.ear_decomposition hnl hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    (base e u v D w hcyc)
    fun B a b D' hB _ hBG hmot hpath hab ha hb hint ↦
      step B a b D' hB hBG hmot hpath hab ha hb hint

/-! ## An ear that is not new

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)` that `Graph.IsTwoConnected.relative_ear_exists` proves and that
`Graph.IsTwoConnected.relative_grows_by_ear` drops. A *geometric* consumer needs it: the ear's
drawing has to miss the drawing of the current subgraph, and an edge shared with `B` would sit
right on it.

It is recoverable, and this section recovers it. An edge of the ear that `B` already has must
join the ear's two ends; the ear is then that single edge, and the enlarged graph is the old
one, so the step has nothing to prove. The integrator may prefer to add the clause to
`relative_grows_by_ear` and to `ear_decomposition` instead — that is the better fix, and it
makes this section unnecessary. -/

/-- **An edge of a path incident to its source is the path's first edge**, in the form that
decomposes the path — `Graph.IsPath.eq_head_of_inc_source` says the same about a list already
known to be a cons, and is what does the work here. -/
theorem IsPath.eq_cons_of_inc_left (h : G.IsPath u D v) (hg : g ∈ D) (hinc : G.Inc g u) :
    ∃ w T, D = g :: T ∧ G.IsLink g u w ∧ G.IsPath w T v := by
  cases D with
  | nil => simp at hg
  | cons a T =>
    obtain rfl : g = a := h.eq_head_of_inc_source hg hinc
    cases h with
    | cons hl hT _ => exact ⟨_, T, rfl, hl, hT⟩

/-- **An edge of an ear that the subgraph already has is the whole ear.** Both ends of such an
edge lie in the subgraph, so the ear's freshness clause makes them the ear's own two ends; the
edge is then the ear's first edge and its far end is the ear's target, so nothing follows it.
-/
theorem IsPath.eq_singleton_of_edge_mem (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B))
    (hg : g ∈ D) (hgB : g ∈ E(B)) : D = [g] ∧ G.IsLink g u v := by
  -- Both ends of the edge lie in the subgraph, so both are ends of the path.
  have hends : ∀ y, G.Inc g y → y = u ∨ y = v := by
    intro y hy
    by_contra hcon
    push Not at hcon
    exact hint y (mem_walkVertices_of_mem_covered ⟨g, hg, hy⟩) hcon.1 hcon.2
      (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hy)
  -- The edge is not a loop, so its two ends are exactly the two ends of the path.
  obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (hpath.edge_mem hg)
  have hpqne : p ≠ q := by rintro rfl; exact hpath.not_isLoopAt hg p hpq
  have hincu : G.Inc g u := by
    rcases hends p hpq.inc_left with rfl | rfl
    · exact hpq.inc_left
    · rcases hends q hpq.inc_right with rfl | rfl
      · exact hpq.inc_right
      · exact absurd rfl hpqne
  -- So it is the path's first edge, and its far end is the path's target.
  obtain ⟨w, T, rfl, hl, hT⟩ := hpath.eq_cons_of_inc_left hg hincu
  have hwv : w = v := by
    rcases hends w hl.inc_right with rfl | hh
    · exact absurd hl (hpath.not_isLoopAt List.mem_cons_self _)
    · exact hh
  subst hwv
  exact ⟨by rw [hT.eq_nil_of_eq], hl⟩

/-- **Either every edge of the ear is new, or the ear changes nothing.** The disjunction the
step of `Graph.IsTwoConnected.ear_decomposition` has to open before it can do any geometry. -/
theorem ear_edges_notMem_or_union_eq (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hu : u ∈ V(B)) (hv : v ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B)) :
    (∀ g ∈ D, g ∉ E(B)) ∨ B.union (G.pathGraphOf u D) = B := by
  by_cases hall : ∀ g ∈ D, g ∉ E(B)
  · exact Or.inl hall
  refine Or.inr ?_
  push Not at hall
  obtain ⟨g, hg, hgB⟩ := hall
  obtain ⟨rfl, hl⟩ := hpath.eq_singleton_of_edge_mem hBG huv hint hg hgB
  -- The ear is a single edge the subgraph already carries, joining two of its own vertices.
  refine le_antisymm (union_le le_rfl ?_) (left_le_union _ _)
  refine ⟨fun y hy ↦ ?_, fun f x y hf ↦ ?_⟩
  · rcases mem_walkVertices_iff.1 (pathGraphOf_vertexSet ▸ hy) with rfl | ⟨f, hf, hinc⟩
    · exact hu
    · obtain rfl : f = g := by simpa using hf
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      exacts [hu, hv]
  · obtain ⟨hfg, hxy, -, -⟩ := pathGraphOf_isLink.1 hf
    obtain rfl : f = g := by simpa using hfg
    exact (hBG.isLink_iff hgB).2 hxy

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

section Plane

open Schoenflies

variable {β : Type*} {G B P : Graph Plane β} {drawing : β → ℝ → Plane} {z a b : Plane}
  {S : Set Plane} {D : List β}

/-- What a union of two plane graphs occupies is what the two of them occupy. -/
@[simp]
theorem pointSet_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    pointSet (B.union P) drawing = pointSet B drawing ∪ pointSet P drawing := by
  simp only [pointSet, vertexSet_union, edgeSet_union, Set.biUnion_union]
  ext w
  simp only [Set.mem_union]
  tauto

/-- Adding a graph removes exactly its own point set from the exterior. -/
theorem exterior_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    exterior (B.union P) drawing = exterior B drawing \ pointSet P drawing := by
  rw [exterior, exterior, pointSet_union, Set.compl_union]
  rfl

/-- A face of the enlarged graph lies inside a face of the old one. -/
theorem face_union_subset : face (B.union P) drawing z ⊆ face B drawing z := by
  by_cases hz : z ∈ exterior (B.union P) drawing
  · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hz) fun w hw ↦ ?_
    exact ((exterior_union B P drawing) ▸ face_subset_exterior _ _ _ hw).1
  · rw [face, connectedComponentIn_eq_empty hz]
    exact Set.empty_subset _

/-- **"All other faces are unchanged."** A face the ear does not touch survives the ear. -/
theorem face_union_eq_of_disjoint (hz : z ∈ exterior B drawing)
    (hdis : Disjoint (face B drawing z) (pointSet P drawing)) :
    face (B.union P) drawing z = face B drawing z := by
  refine Set.Subset.antisymm face_union_subset ?_
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_face hz) fun w hw ↦ ?_
  rw [exterior_union]
  exact ⟨face_subset_exterior _ _ _ hw, fun hwP ↦ Set.disjoint_left.1 hdis hw hwP⟩

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face."** The topological half: a nonempty preconnected subset of the exterior lies in one
face. -/
theorem exists_face_of_isPreconnected (hS : IsPreconnected S) (hSne : S.Nonempty)
    (hsub : S ⊆ exterior B drawing) :
    ∃ z ∈ exterior B drawing, S ⊆ face B drawing z := by
  obtain ⟨z, hz⟩ := hSne
  exact ⟨z, hsub hz, hS.subset_connectedComponentIn hz hsub⟩

/-! ### The ear lies in one face

The blueprint's *"its interior is connected and disjoint from the current graph, so it lies in
one current face `F`"*, in full. -/

/- "An arc without its two endpoints is connected" is
`Schoenflies.IsArcBetween.isConnected_diff`, now in `Schoenflies/Subarc.lean`. -/

/-- **The ear's realisation meets the drawing of the current subgraph only in the ear's two
ends.** Two cases, and both come down to the ear's freshness clause: a point of the ear on a
*vertex* of `B` is an end of the edge of the ear it lies on
(`Graph.IsDrawing.vertex_mem_edgeArc`), and a point of the ear on an *edge* of `B` is a vertex
incident with both (`Graph.IsDrawing.edge_inter`) — the two edges being distinct because no
edge of the ear belongs to `B`. Either way the point is a vertex of `B` that the ear visits,
which the freshness clause makes one of the ear's two ends. -/
theorem IsDrawing.edgesCover_inter_pointSet (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    edgesCover drawing D ∩ pointSet B drawing ⊆ {a, b} := by
  -- A vertex of `B` that an edge of the ear is incident with is one of the ear's two ends.
  have key : ∀ p, (∃ f ∈ D, G.Inc f p) → p ∈ V(B) → p = a ∨ p = b := by
    rintro p ⟨f, hf, hinc⟩ hpB
    by_contra hcon
    push Not at hcon
    exact hint p (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hcon.1 hcon.2 hpB
  rintro p ⟨hpD, hpB⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hpD
  have hfG : f ∈ E(G) := hpath.edge_mem hf
  rcases hpB with hpV | hpE
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hfG
    have hinc : G.Inc f p := by
      rcases hG.vertex_mem_edgeArc hxy (hBG.vertexSet_mono hpV) hpf with rfl | rfl
      exacts [hxy.inc_left, hxy.inc_right]
    exact key p ⟨f, hf, hinc⟩ hpV
  · simp only [Set.mem_iUnion, exists_prop] at hpE
    obtain ⟨g, hgB, hpg⟩ := hpE
    have hfg : f ≠ g := fun hh ↦ hnew f hf (hh ▸ hgB)
    obtain ⟨-, hincf, hincg⟩ := hG.edge_inter hfG (hBG.edgeSet_mono hgB) hfg hpf hpg
    exact key p ⟨f, hf, hincf⟩ (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hincg)

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face `F`."** The ear's realisation without its two ends is an arc's interior, hence connected,
and it misses the drawing of `B` altogether, so it lies in a single face. -/
theorem IsDrawing.exists_face_of_ear (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b) (hab : a ≠ b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    ∃ z ∈ exterior B drawing, edgesCover drawing D \ {a, b} ⊆ face B drawing z := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hconn := harc.isConnected_diff
  refine exists_face_of_isPreconnected hconn.isPreconnected hconn.nonempty fun w hw hwB ↦ ?_
  exact hw.2 (hG.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hwB⟩)

/-! ### A subgraph of a plane graph is a plane graph

The induction speaks of the faces of the *current* subgraph, so every step needs the current
subgraph to be a plane graph in its own right. Nothing has to be redrawn: the same drawing
serves. General, and not in `Schoenflies/Graph/Drawing.lean`; the integrator may want to hoist
it. -/

/-- **A subgraph of a plane graph is a plane graph**, with the same drawing. -/
theorem IsDrawing.mono (hG : IsDrawing G drawing) (hBG : B ≤ G) : IsDrawing B drawing where
  edge_param := fun e he ↦ by
    obtain ⟨hc, hi, hl⟩ := hG.edge_param (hBG.edgeSet_mono he)
    exact ⟨hc, hi, (hBG.isLink_iff he).2 hl⟩
  vertex_mem_edgeArc := fun _ _ _ _ hl hv hmem ↦
    hG.vertex_mem_edgeArc (hl.mono hBG) (hBG.vertexSet_mono hv) hmem
  edge_inter := fun e f he hf hef p hpe hpf ↦ by
    obtain ⟨-, hince, hincf⟩ :=
      hG.edge_inter (hBG.edgeSet_mono he) (hBG.edgeSet_mono hf) hef hpe hpf
    obtain ⟨y, hy⟩ := hince
    obtain ⟨y', hy'⟩ := hincf
    exact ⟨mem_vertexSet_of_inc_of_mem_edgeSet hBG he ⟨y, hy⟩,
      ⟨y, (hBG.isLink_iff he).2 hy⟩, ⟨y', (hBG.isLink_iff hf).2 hy'⟩⟩

/-! ### The ear's ends lie on the boundary of the face its interior lies in -/

/- "An endpoint of an arc is a limit of the arc's interior" is
`Schoenflies.IsArcBetween.left_mem_closure_diff` / `…right_mem_closure_diff`, hoisted into
`Schoenflies/Subarc.lean` alongside `…isConnected_diff`. This module had its own copy, with the
same statement as the one in `Schoenflies/AlternatingCrosscuts.lean`; the two modules do not
import each other, so the build accepted both. -/

/-- **"The ear's two endpoints are limits of its interior, which lies in `F`, so they lie on
`∂F`."** This is the hypothesis `thm:polygonal-crosscut` needs of a crosscut: its two ends are
on the boundary curve of the region it cuts. -/
theorem IsDrawing.ends_mem_frontier_face (hG : IsDrawing G drawing)
    (hopen : IsOpen (face B drawing z)) (hpath : G.IsPath a D b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hsub : edgesCover drawing D \ {a, b} ⊆ face B drawing z) :
    a ∈ frontier (face B drawing z) ∧ b ∈ frontier (face B drawing z) := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hnot : ∀ y ∈ V(B), y ∉ face B drawing z := fun y hy hyf ↦
    face_subset_exterior _ _ _ hyf (vertexSet_subset_pointSet hy)
  refine ⟨⟨closure_mono hsub harc.left_mem_closure_diff, ?_⟩,
    ⟨closure_mono hsub harc.right_mem_closure_diff, ?_⟩⟩
  · rw [hopen.interior_eq]; exact hnot a ha
  · rw [hopen.interior_eq]; exact hnot b hb

end Plane

end Graph
