/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Graph.TwoConnected
import LeanPool.Schoenflies.Graph.PathGraph

/-!
# Ears

The ear decomposition: `lem:subdivision-ear-preserve` in both halves, and the step of
`lem:relative-ear` that grows a 2-connected subgraph towards the graph containing it.

## Rerouting is the engine of half (a)

`Graph.Reaches.reroute` says the obvious thing in the one form every consumer wants: if every
edge but `e` survives from `G` into `H`, and whatever `e` joins in `G` is joined in `H` by
other means, then `H` reaches whatever `G` reaches. A walk that took `e` takes the
replacement route instead, and the induction is over the walk.

Its `hends` premise is stated as "**whatever** `e` joins in `G` is joined in `H`", not as "the
two named ends are joined". That is what makes the premise dischargeable in the case where
`e` is not an edge of `G` at all: it is then vacuous. `Graph.Reaches.across_edge_replacement`
is the specialisation the subdivision runs on, and it is where the vacuous case is used — its
`routed` premise carries the three-way choice the blueprint's proof makes in prose:

* reroute along the new path — the deleted vertex is not on it, so the path survives whole;
* reroute around the old graph — the deleted vertex *is* on the path, so the old graph is
  untouched and the replaced edge was not a bridge (`Graph.IsTwoConnected.no_bridge`);
* do not reroute at all — the deleted vertex is an end of the replaced edge, so no surviving
  walk could have taken that edge.

## Half (a) is stated for a path

`Graph.IsTwoConnected.replace_edge_by_path` replaces an edge by a whole path, not by a single
new vertex. Nothing in the argument cares how long the replacement is, and the general form is
what a subdivision needs: subdividing one edge by one vertex is the case where the path has
two edges.

## Half (b) does not need the blueprint's freshness hypothesis

`Graph.IsTwoConnected.ear` attaches an ear, and the blueprint's "whose internal vertices are
new" is **not** assumed — the proof does not use it. What carries the argument is
`Graph.IsPathGraph.reaches_an_end`: whatever vertex is deleted, every remaining vertex of the
path still reaches one of the two ends. The two ends live in a 2-connected graph, at least one
of them survives the deletion, and that survivor is the hub everything routes through.

Half (a) *does* use freshness, and for a real reason: without it the deleted vertex could sit
both on the replacement path and inside the old graph, and then neither of the two routes
between the replaced edge's ends need exist.

## Finding the ear

`Graph.IsTwoConnected.ear_exists` needs neither the components of `G - V(H)` nor a shortest
path, which is what the blueprint's proof reaches for. The ear is *found*: walk out of the
subgraph to a vertex outside it, take the edge where the walk **first** leaves the subgraph
(`Graph.IsWalk.crossing`), and walk back from that edge's outer end to a *different* vertex of
the subgraph inside `G` minus the edge's inner end — a graph that is connected because `G` is
2-connected, and whose walks therefore never touch the inner end. That walk with the crossing
edge in front is a path of `G` between two vertices of the subgraph, and the crossing edge is
one the subgraph did not have.

`Graph.pathGraphOf` turns it into a graph and `Graph.IsTwoConnected.grows_by_ear` glues it on.
Termination — the blueprint's "finiteness terminates the process" — is not here; this is the
single step, and a consumer that counts edges iterates it.

## Looplessness

`Graph.IsTwoConnected.ear_exists` is the one statement here that has to assume the graph has
no loop, and the hypothesis is not bureaucracy: adding a loop to a 2-connected graph leaves it
2-connected, so a 2-connected subgraph missing only a loop grows by no ear at all, and the
conclusion — a path between *distinct* vertices — is false. It is used only in the degenerate
branch where every vertex is already present and the missing object is an edge. A plane
consumer discharges it from its drawing.

## Blueprint

* `Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a), "every
  subdivision of `G` is 2-connected", stated for a replacement path of any length.
* `Graph.IsTwoConnected.ear` — `lem:subdivision-ear-preserve` (b), "if `P` is a path whose
  distinct endpoints lie in `G` … then `G ∪ P` is 2-connected".
* `Graph.IsTwoConnected.ear_exists`, `Graph.IsTwoConnected.grows_by_ear` — the step of
  `lem:relative-ear`, "`G` is obtained from `H` by repeatedly adding paths whose distinct
  endpoints are already present".
* `Graph.Reaches.reroute`, `Graph.Reaches.across_edge_replacement` — the blueprint's "the
  remaining part of the subdivided edge attaches `w` to `u` or `v`" together with "a
  2-connected graph has no bridge", turned into one transfer lemma.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K P : Graph α β} {a b c s t u v x y z : α} {e f : β}
  {W D : List β}

/-! ### The union of two subgraphs

`Graph.union` and the two inclusions *into* it live in `Schoenflies/Graph/TwoConnected.lean`;
this is the inclusion *out of* it, which the ear construction needs in order to know that the
enlarged subgraph is still a subgraph. It is general and belongs beside the other two — the
integrator should hoist it. -/

/-! ### Rerouting one edge -/

/-- **One edge swapped for any route between its ends.** If every edge of `G` other than `e`
links the same pair in `H`, and whatever `e` links in `G` is joined in `H` by some other
means, then `H` reaches whatever `G` reaches: a walk that took `e` takes the replacement route
instead.

The premise about `e` is universally quantified over its ends rather than stated for a named
pair, so that it is *vacuous* when `e` is not an edge of `G` — which is the case a vertex
deletion produces, and the reason this is the shape that gets used. -/
theorem Reaches.reroute (hV : V(G) ⊆ V(H))
    (hE : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → H.IsLink g p q)
    (hends : ∀ ⦃p q⦄, G.IsLink e p q → H.Reaches p q)
    (h : G.Reaches s t) : H.Reaches s t := by
  obtain ⟨R, hR⟩ := h
  induction hR with
  | nil hx => exact Reaches.refl (hV hx)
  | @cons p w q g R hl _ ih =>
    -- Either this step took the replaced edge, or it survives verbatim.
    refine Reaches.trans ?_ ih
    by_cases hg : g = e
    · exact hends (hg ▸ hl)
    · exact Reaches.of_isLink (hE hl hg)

/-- **The form a subdivision needs.** A walk of `G - c` transfers to any graph holding the
surviving edges, provided the replaced edge's ends are joined there *or* that edge was
incident to the deleted vertex — in which case no walk of `G - c` could have taken it, and the
`hends` premise of `Graph.Reaches.reroute` is vacuous.

That disjunction is the blueprint's three-way case analysis: route along the replacement,
route around the old graph, or do not route at all. -/
theorem Reaches.across_edge_replacement (hV : V(G.deleteVerts {c}) ⊆ V(H))
    (hl : G.IsLink e u v)
    (hE : ∀ ⦃g p q⦄, (G.deleteVerts {c}).IsLink g p q → g ≠ e → H.IsLink g p q)
    (routed : H.Reaches u v ∨ G.Inc e c)
    (h : (G.deleteVerts {c}).Reaches s t) : H.Reaches s t := by
  refine Reaches.reroute (e := e) hV hE (fun p q hpq ↦ ?_) h
  rw [deleteVerts_isLink] at hpq
  obtain ⟨hpq, hp, hq⟩ := hpq
  have hpc : p ≠ c := fun hh ↦ hp (by simp [hh])
  have hqc : q ≠ c := fun hh ↦ hq (by simp [hh])
  rcases routed with hr | ⟨w, hw⟩
  · -- The ends are joined in `H`; the step ran between them, one way or the other.
    rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hr, hr.symm]
  · -- The edge met the deleted vertex, so `G - c` does not have it: nothing to prove.
    rcases hw.left_eq_or_eq hpq with hh | hh
    exacts [(hpc hh.symm).elim, (hqc hh.symm).elim]

/-! ### Attaching an ear -/

/-- **`lem:subdivision-ear-preserve` (b): attaching an ear preserves 2-connectivity.** `P` is
a path whose two distinct ends lie in the 2-connected graph `G`; then `G ∪ P` is 2-connected.

The blueprint's hypothesis that the ear's internal vertices are new is **not** needed. Delete
a vertex `c`. One of the ear's two ends survives, and it is the hub: `G - c` is connected and
contains it, and every surviving vertex of the ear reaches one of the two ends inside the ear
(`Graph.IsPathGraph.reaches_an_end`) — an end which, having been reached after the deletion, is
itself not `c`, so it lies in `G - c` too. -/
theorem IsTwoConnected.ear (hG : G.IsTwoConnected) (hcompat : G.Compatible P)
    (hP : P.IsPathGraph u W v) (huv : u ≠ v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G.union P).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G P).vertexSet_mono
  connected := hcompat.union_connected hG.connected hP.connected hu hP.source_mem
  deleteVerts_connected := by
    intro c _
    -- One of the ear's two ends survives the deletion; it is the hub.
    obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
      by_cases hcu : u = c
      · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
      · exact ⟨u, hu, hcu⟩
    have hGle : G.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono (left_le_union G P) _
    have hPle : P.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono hcompat.right_le_union _
    have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
    -- Every surviving vertex of the graph side reaches the hub inside the graph side.
    have key : ∀ x ∈ V(G), x ≠ c → ((G.union P).deleteVerts {c}).Reaches z x := fun x hx hxc ↦
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hzG hzc)
        (mem_deleteVerts_singleton_of_ne hx hxc)).mono hGle
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne
      ((left_le_union G P).vertexSet_mono hzG) hzc) fun x hx ↦ ?_
    rw [vertexSet_deleteVerts] at hx
    obtain ⟨hxS, hxc⟩ := hx
    have hxc' : x ≠ c := by simpa using hxc
    rcases (hxS : x ∈ V(G) ∪ V(P)) with hxG | hxP
    · exact key x hxG hxc'
    · -- On the ear, one of the two ends is still reachable, and it survived the deletion.
      rcases hP.reaches_an_end hxP hxc' with hr | hr
      · have hune : u ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key u hu hune).trans (hr.mono hPle).symm
      · have hvne : v ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key v hv hvne).trans (hr.mono hPle).symm

/-! ### Replacing an edge by a path -/

/-- **`lem:subdivision-ear-preserve` (a): a subdivision of a 2-connected graph is
2-connected.** Stated for a replacement *path* rather than for a single new vertex, because
nothing in the argument cares how long the replacement is; subdividing one edge by one vertex
is the case where `P` has two edges.

Delete a vertex `c`. One end of the replaced edge survives and is the hub. Everything on the
old side reaches it by `Graph.Reaches.across_edge_replacement`, whose `routed` premise is
discharged by the three-way case analysis: if `c` is an end of the replaced edge there is
nothing to route; if `c` is an old vertex then it is not on the path — this is where the
freshness hypothesis `hnew` is used — and the path itself joins the ends; and if `c` is new
then the old graph is untouched and has no bridge. Everything on the path side reaches an end
of the path, and an end reached after the deletion survived it. -/
theorem IsTwoConnected.replace_edge_by_path (hG : G.IsTwoConnected) (hl : G.IsLink e u v)
    (huv : u ≠ v) (hcompat : (G.deleteEdges {e}).Compatible P) (hP : P.IsPathGraph u W v)
    (hnew : ∀ x ∈ V(P), x ≠ u → x ≠ v → x ∉ V(G)) :
    ((G.deleteEdges {e}).union P).IsTwoConnected := by
  set T := G.deleteEdges {e} with hT
  set S := T.union P with hS
  have hTS : T ≤ S := left_le_union T P
  have hPS : P ≤ S := hcompat.right_le_union
  have hVT : V(T) = V(G) := by rw [hT]; simp
  have hu : u ∈ V(G) := hl.left_mem
  have hv : v ∈ V(G) := hl.right_mem
  -- Every old edge but the replaced one links the same pair in the new graph.
  have hGS : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → S.IsLink g p q := by
    intro g p q hg hge
    refine hTS.isLink_mono (show T.IsLink g p q from ?_)
    rw [hT]
    exact ⟨hg, by simpa using hge⟩
  have hVGS : V(G) ⊆ V(S) := by
    rw [hS, vertexSet_union, hVT]
    exact Set.subset_union_left
  -- The replacement route.
  have hPuv : P.Reaches u v := hP.connected.reaches hP.source_mem hP.target_mem
  refine ⟨hG.hasThreeVertices.mono hVGS, ?_, ?_⟩
  · refine Connected.of_hub (hVGS hu) fun x hx ↦ ?_
    rcases (hx : x ∈ V(T) ∪ V(P)) with hxT | hxP
    · refine Reaches.reroute (e := e) hVGS hGS ?_
        (hG.connected.reaches hu (by rwa [hVT] at hxT))
      intro p q hpq
      rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [hPuv.mono hPS, (hPuv.mono hPS).symm]
    · exact (hP.connected.reaches hP.source_mem hxP).mono hPS
  intro c _
  -- One end of the replaced edge survives; it is the hub.
  obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
    by_cases hcu : u = c
    · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
    · exact ⟨u, hu, hcu⟩
  have hTle : T.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hTS _
  have hPle : P.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hPS _
  have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
  -- The replaced edge's ends are still joined, unless the deleted vertex is one of them.
  have routed : (S.deleteVerts {c}).Reaches u v ∨ G.Inc e c := by
    by_cases hcu : c = u
    · exact Or.inr (hcu ▸ hl.inc_left)
    by_cases hcv : c = v
    · exact Or.inr (hcv ▸ hl.inc_right)
    by_cases hcG : c ∈ V(G)
    · -- An old vertex and not an end: the path is untouched, and it joins the ends.
      have hcP : c ∉ V(P) := fun hh ↦ hnew c hh hcu hcv hcG
      have hreach : (P.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcP]; exact hPuv
      exact Or.inl (hreach.mono hPle)
    · -- A new vertex: the old graph is untouched, and it has no bridge.
      have hcT : c ∉ V(T) := by rw [hVT]; exact hcG
      have hreach : (T.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcT, hT]
        exact hG.no_bridge hl
      exact Or.inl (hreach.mono hTle)
  -- Every surviving old vertex reaches the hub.
  have key : ∀ x ∈ V(G), x ≠ c → (S.deleteVerts {c}).Reaches x z := by
    intro x hx hxc
    refine Reaches.across_edge_replacement (e := e) ?_ hl ?_ routed
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hx hxc)
        (mem_deleteVerts_singleton_of_ne hzG hzc))
    · rw [vertexSet_deleteVerts, vertexSet_deleteVerts]
      exact Set.sdiff_subset_sdiff_left hVGS
    · intro g p q hg hge
      rw [deleteVerts_isLink] at hg ⊢
      exact ⟨hGS hg.1 hge, hg.2.1, hg.2.2⟩
  refine Connected.of_hub (mem_deleteVerts_singleton_of_ne (hVGS hzG) hzc) fun x hx ↦ ?_
  rw [vertexSet_deleteVerts] at hx
  obtain ⟨hxS, hxc⟩ := hx
  have hxc' : x ≠ c := by simpa using hxc
  rcases (hxS : x ∈ V(T) ∪ V(P)) with hxT | hxP
  · exact (key x (by rwa [hVT] at hxT) hxc').symm
  · rcases hP.reaches_an_end hxP hxc' with hr | hr
    · have hune : u ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key u hu hune).symm.trans (hr.mono hPle).symm
    · have hvne : v ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key v hv hvne).symm.trans (hr.mono hPle).symm

/-! ### Finding an ear -/

/-- **A 2-connected subgraph that is not all of a 2-connected graph has an ear.** The ear is
found, not chosen: if the subgraph already has every vertex then a missing edge joins two of
them and is an ear by itself; otherwise a walk out of the subgraph crosses its boundary, and
deleting the crossing edge's inner end leaves `G` connected, so the outer end walks back to a
*different* vertex of the subgraph without passing through the first.

The looplessness hypothesis is used only in the first, degenerate branch, and it cannot be
dropped: a 2-connected graph plus a loop is 2-connected, and no ear is missing from it. -/
theorem IsTwoConnected.ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected) (hKG : K ≤ G)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D g, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ g ∈ D ∧ g ∉ E(K) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨o, hoG, hoK⟩ := hout
    -- Walk from the subgraph out to `o`; it crosses the boundary along one of its own edges.
    obtain ⟨anchor, hanchor⟩ := hK.connected.nonempty
    obtain ⟨R, hR⟩ := hG.connected.reaches (hKG.vertexSet_mono hanchor) hoG
    obtain ⟨g, hgR, p, q, hlpq, hpK, hqK⟩ := hR.crossing hanchor hoK
    have hpq : p ≠ q := fun hh ↦ hqK (hh ▸ hpK)
    -- The subgraph has a second vertex to come back to.
    obtain ⟨b, hbK, hbp, -⟩ := hK.hasThreeVertices.exists_ne_ne p p
    have hqG : q ∈ V(G) := hlpq.right_mem
    have hbG : b ∈ V(G) := hKG.vertexSet_mono hbK
    -- Deleting the inner end leaves `G` connected, so the outer end walks back to `b`.
    obtain ⟨D, hD⟩ := ((hG.deleteVerts_connected' p).reaches
      (mem_deleteVerts_singleton_of_ne hqG (Ne.symm hpq))
      (mem_deleteVerts_singleton_of_ne hbG hbp)).exists_isPath
    have hfresh : p ∉ G.walkVertices q D := by
      rintro hmem
      rcases mem_walkVertices_iff.1 hmem with rfl | ⟨g', hg', hinc⟩
      · exact hpq rfl
      · exact hD.isWalk.notMem_of_inc_of_deleteVerts hinc hg'
    refine ⟨p, b, g :: D, g, .cons hlpq (hD.mono deleteVerts_le) hfresh, Ne.symm hbp, hpK,
      hbK, List.mem_cons_self, fun hgK ↦ ?_⟩
    -- The crossing edge is not the subgraph's: its outer end would then be a vertex of it.
    exact hqK ((hKG.isLink_iff hgK).2 hlpq).right_mem
  · -- Every vertex is already there, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨g, hgG, hgK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hgG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    exact ⟨p, q, [g], g, .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      List.mem_cons_self, hgK⟩

/-- **H5: a 2-connected subgraph of a 2-connected graph grows to it by adding ears.** One
step: the subgraph gains an ear and at least one edge, and is still a 2-connected subgraph of
the big graph. Iterating on the number of missing edges is the caller's business — the
blueprint's "finiteness terminates the process". -/
theorem IsTwoConnected.grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ B : Graph α β, B.IsTwoConnected ∧ K ≤ B ∧ B ≤ G ∧ ∃ g ∈ E(B), g ∉ E(K) := by
  obtain ⟨a, b, D, g, hpath, hab, haK, hbK, hgD, hgK⟩ := hG.ear_exists hK hKG hnl hproper
  -- The path, presented as a graph, is the ear.
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  exact ⟨K.union (G.pathGraphOf a D),
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab haK hbK,
    left_le_union _ _, union_le hKG hearle, g,
    Set.mem_union_right _ (hearP.mem_edgeSet hgD), hgK⟩

end Graph
