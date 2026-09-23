/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FiniteTransfer
public import LeanPool.Schoenflies.RealizeSubdivHomeo

/-!
# Common subdivision for finite transfer

This module proves step 1 of finite transfer.  The part of the extension graph supported on the
old source skeleton is extracted as a trace graph.  It is a subdivision of the old skeleton and
remains 2-connected.  Its finitely many vertices are then inserted, one at a time, into both
realizations of the generated pair.  `CellStructure.SubdivData.realizeHomeo` transports every
source subdivision parameter to the matching target edge.

The resulting theorem `Schoenflies.commonSubdivision` discharges the former
`Schoenflies.CommonSubdivision` interface under the same infinite name-supply assumption used by
the ear construction.

## Blueprint

* `Schoenflies.commonSubdivision` — the common-subdivision part of step 1 in the proof of
  `thm:finite-transfer`(a).
* `Schoenflies.finite_transfer_toward_square` — `thm:finite-transfer`(a).
* `Schoenflies.IsPlaneSubdivisionExtension.trace_isTwoConnected` — the trace theorem for two
  arbitrary plane drawings, used when assembling target/mesh overlays.
-/

@[expose] public section

open Set
open scoped Graph

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {e : β} {x y : Plane}

/-- A finite plane graph with nonempty, preconnected point set is combinatorially connected. -/
theorem connected_of_isPreconnected_pointSet [G.Finite]
    (hdraw : IsDrawing G drawing) (hconn : IsPreconnected (pointSet G drawing))
    (hne : V(G).Nonempty) : G.Connected := by
  refine ⟨hne, fun x hx y hy => ?_⟩
  by_contra hxy
  let A : Graph Plane β := G.induce (G.component x)
  let B : Graph Plane β := G.induce (V(G) \ G.component x)
  have hAle : A ≤ G := G.induce_le component_subset_vertexSet
  have hBle : B ≤ G := G.induce_le Set.sdiff_subset
  let _ : A.Finite := Graph.Finite.of_le hAle
  let _ : B.Finite := Graph.Finite.of_le hBle
  have hAclosed : IsClosed (pointSet A drawing) := (hdraw.mono hAle).isClosed_pointSet
  have hBclosed : IsClosed (pointSet B drawing) := (hdraw.mono hBle).isClosed_pointSet
  have hcover : pointSet G drawing ⊆ pointSet A drawing ∪ pointSet B drawing := by
    intro z hz
    rcases hz with hzV | hzE
    · by_cases hzC : z ∈ G.component x
      · exact Or.inl (Or.inl hzC)
      · exact Or.inr (Or.inl ⟨hzV, hzC⟩)
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
      obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
      by_cases huC : u ∈ G.component x
      · have hvC : v ∈ G.component x := mem_component_of_isLink huC huv
        exact Or.inl (Or.inr (Set.mem_iUnion₂_of_mem
          (show e ∈ E(A) by
            rw [edgeSet_eq_setOfPred_exists_isLink]
            exact ⟨u, v, huv, huC, hvC⟩) hze))
      · have hvC : v ∉ G.component x := by
          intro hvC
          exact huC (mem_component_of_isLink hvC huv.symm)
        exact Or.inr (Or.inr (Set.mem_iUnion₂_of_mem
          (show e ∈ E(B) by
            rw [edgeSet_eq_setOfPred_exists_isLink]
            exact ⟨u, v, huv, ⟨huv.left_mem, huC⟩, ⟨huv.right_mem, hvC⟩⟩) hze))
  have hAB : Disjoint (pointSet A drawing) (pointSet B drawing) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    rcases hzA with hzAV | hzAE <;> rcases hzB with hzBV | hzBE
    · exact hzBV.2 hzAV
    · obtain ⟨e, heB, hze⟩ := Set.mem_iUnion₂.1 hzBE
      rw [edgeSet_eq_setOfPred_exists_isLink] at heB
      obtain ⟨u, v, huv, huB, hvB⟩ := heB
      have hzinc := hdraw.vertex_mem_edgeArc huv (component_subset_vertexSet hzAV) hze
      rcases hzinc with rfl | rfl
      exacts [huB.2 hzAV, hvB.2 hzAV]
    · obtain ⟨e, heA, hze⟩ := Set.mem_iUnion₂.1 hzAE
      rw [edgeSet_eq_setOfPred_exists_isLink] at heA
      obtain ⟨u, v, huv, huA, hvA⟩ := heA
      have hzinc := hdraw.vertex_mem_edgeArc huv hzBV.1 hze
      rcases hzinc with rfl | rfl
      exacts [hzBV.2 huA, hzBV.2 hvA]
    · obtain ⟨e, heA, hzeA⟩ := Set.mem_iUnion₂.1 hzAE
      obtain ⟨f, hfB, hzfB⟩ := Set.mem_iUnion₂.1 hzBE
      have heG : e ∈ E(G) := hAle.edgeSet_mono heA
      have hfG : f ∈ E(G) := hBle.edgeSet_mono hfB
      have hef : e ≠ f := by
        intro hef
        subst f
        rw [edgeSet_eq_setOfPred_exists_isLink] at heA hfB
        obtain ⟨u, v, huv, huA, -⟩ := heA
        obtain ⟨u', v', huv', huB, hvB⟩ := hfB
        rcases huv.left_eq_or_eq huv' with h | h
        · exact huB.2 (h ▸ huA)
        · exact hvB.2 (h ▸ huA)
      obtain ⟨hzV, ⟨u, heu⟩, ⟨v, hfv⟩⟩ :=
        hdraw.edge_inter heG hfG hef hzeA hzfB
      rw [edgeSet_eq_setOfPred_exists_isLink] at heA hfB
      obtain ⟨a, b, hab, haA, hbA⟩ := heA
      obtain ⟨c, d, hcd, hcB, hdB⟩ := hfB
      rcases heu.left_eq_or_eq hab with rfl | rfl <;>
        rcases hfv.left_eq_or_eq hcd with rfl | rfl
      all_goals first | exact hcB.2 haA | exact hdB.2 haA | exact hcB.2 hbA | exact hdB.2 hbA
  have hdisj : pointSet G drawing ∩ (pointSet A drawing ∩ pointSet B drawing) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzA, hzB⟩
    exact Set.disjoint_left.1 hAB hzA hzB
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hconn
      _ _ hAclosed hBclosed hcover hdisj) with hsub | hsub
  · have hyB : y ∈ pointSet B drawing := Or.inl ⟨hy, hxy⟩
    exact Set.disjoint_left.1 hAB (hsub (Or.inl hy)) hyB
  · have hxA : x ∈ pointSet A drawing := Or.inl (mem_component_self hx)
    exact Set.disjoint_left.1 hAB hxA (hsub (Or.inl hx))

/-- The part of a drawn graph supported on a prescribed set. -/
def traceGraph (G : Graph Plane β) (drawing : β → ℝ → Plane) (A : Set Plane) :
    Graph Plane β :=
  (G.restrict {e | edgeArc drawing e ⊆ A}).induce (V(G) ∩ A)

/-- The vertices retained by a trace graph. -/
@[simp] theorem traceGraph_vertexSet (A : Set Plane) :
    V(traceGraph G drawing A) = V(G) ∩ A := rfl

/-- A trace edge is exactly an ambient edge whose full arc and endpoints lie in the support. -/
@[simp] theorem traceGraph_isLink (A : Set Plane) :
    (traceGraph G drawing A).IsLink e x y ↔
      edgeArc drawing e ⊆ A ∧ G.IsLink e x y ∧ x ∈ A ∧ y ∈ A := by
  simp only [traceGraph, induce_isLink, restrict_isLink, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hsub, hlink⟩, ⟨-, hxA⟩, ⟨-, hyA⟩⟩
    exact ⟨hsub, hlink, hxA, hyA⟩
  · rintro ⟨hsub, hlink, hxA, hyA⟩
    exact ⟨⟨hsub, hlink⟩, ⟨hlink.left_mem, hxA⟩, ⟨hlink.right_mem, hyA⟩⟩

/-- A trace graph is a subgraph of its ambient graph. -/
theorem traceGraph_le (A : Set Plane) : traceGraph G drawing A ≤ G :=
  le_trans (induce_le Set.inter_subset_left) restrict_le

/-- Enlarging the support enlarges the trace graph. -/
theorem traceGraph_mono {A B : Set Plane} (hAB : A ⊆ B) :
    traceGraph G drawing A ≤ traceGraph G drawing B where
  vertexSet_mono := by
    rw [traceGraph_vertexSet, traceGraph_vertexSet]
    exact Set.inter_subset_inter_right _ hAB
  isLink_mono := by
    intro e x y hlink
    rw [traceGraph_isLink] at hlink ⊢
    exact ⟨hlink.1.trans hAB, hlink.2.1, hAB hlink.2.2.1, hAB hlink.2.2.2⟩

/-- The trace graph occupies only its prescribed support. -/
theorem pointSet_traceGraph_subset (A : Set Plane) :
    pointSet (traceGraph G drawing A) drawing ⊆ A := by
  rintro z (hz | hz)
  · exact hz.2
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
    rw [edgeSet_eq_setOfPred_exists_isLink] at he
    obtain ⟨x, y, hxy⟩ := he
    exact (traceGraph_isLink A).1 hxy |>.1 hze

/-- An absorbed subset of a finite drawing is exactly the point set of its trace graph. -/
theorem pointSet_traceGraph_eq (hdraw : IsDrawing G drawing) (A : Set Plane)
    (hsub : A ⊆ pointSet G drawing)
    (habsorb : ∀ ⦃e⦄, e ∈ E(G) →
      (edgeArc drawing e ∩ (A \ V(G))).Nonempty → edgeArc drawing e ⊆ A) :
    pointSet (traceGraph G drawing A) drawing = A := by
  apply Set.Subset.antisymm (pointSet_traceGraph_subset A)
  intro z hzA
  rcases hsub hzA with hzV | hzE
  · exact Or.inl ⟨hzV, hzA⟩
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
    by_cases hzVG : z ∈ V(G)
    · exact Or.inl ⟨hzVG, hzA⟩
    · have heA : edgeArc drawing e ⊆ A :=
        habsorb he ⟨z, ⟨hze, hzA, hzVG⟩⟩
      exact Or.inr (Set.mem_iUnion₂_of_mem
        (show e ∈ E(traceGraph G drawing A) by
          rw [edgeSet_eq_setOfPred_exists_isLink]
          obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
          have harc := hdraw.edge_isArcBetween hxy
          exact ⟨x, y, (traceGraph_isLink A).2
            ⟨heA, hxy, heA harc.left_mem, heA harc.right_mem⟩⟩)
        hze)

/-- A graph vertex lying on a drawn walk is one of the walk's combinatorial vertices. -/
theorem IsDrawing.mem_walkVertices_of_mem_edgesCover_walk (hdraw : IsDrawing G drawing)
    {u v z : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hzV : z ∈ V(G)) (hz : z ∈ edgesCover drawing W) : z ∈ G.walkVertices u W := by
  obtain ⟨e, heW, hze⟩ := mem_edgesCover_iff.1 hz
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (hW.edge_mem heW)
  rcases hdraw.vertex_mem_edgeArc hxy hzV hze with rfl | rfl
  · exact mem_walkVertices_of_mem_covered ⟨e, heW, hxy.inc_left⟩
  · exact mem_walkVertices_of_mem_covered ⟨e, heW, hxy.inc_right⟩

/-- Adding edges without adding vertices preserves 2-connectivity. -/
theorem IsTwoConnected.spanning_mono {α δ : Type*} {A B : Graph α δ}
    (hA : A.IsTwoConnected) (hAB : A ≤ B) (hV : V(B) ⊆ V(A)) :
    B.IsTwoConnected where
  hasThreeVertices := hA.hasThreeVertices.mono hAB.vertexSet_mono
  connected := by
    obtain ⟨u, hu⟩ := hA.connected.nonempty
    exact Connected.of_hub (hAB.vertexSet_mono hu) fun x hx =>
      (hA.connected.reaches hu (hV hx)).mono hAB
  deleteVerts_connected := by
    intro x _
    have hdel := deleteVerts_mono hAB ({x} : Set α)
    obtain ⟨u, hu⟩ := (hA.deleteVerts_connected' x).nonempty
    exact Connected.of_hub (hdel.vertexSet_mono hu) fun y hy =>
      ((hA.deleteVerts_connected' x).reaches hu (by
        rw [vertexSet_deleteVerts] at hy ⊢
        exact ⟨hV hy.1, hy.2⟩)).mono hdel

end Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S : CellStructure γ} {R : S.Realization}
  {outer dom : Set Plane} {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-- An extension edge meeting the interior of the old skeleton is absorbed by that skeleton. -/
theorem trace_absorb (hH : IsSourceExtension R outer dom H Hdraw) :
    ∀ ⦃f⦄, f ∈ E(H) →
      (edgeArc Hdraw f ∩ (R.skeletonSet \ V(H))).Nonempty →
      edgeArc Hdraw f ⊆ R.skeletonSet := by
  intro f hf hmeet
  obtain ⟨z, hzf, hzskel, hznotH⟩ := hmeet
  rcases hzskel with hzV | hzE
  · exact absurd (hH.vertexSet_subset hzV) hznotH
  · obtain ⟨e, heR, hze⟩ := Set.mem_iUnion₂.1 hzE
    have heS : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at heR
    obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet heS
    have hza : z ≠ R.pos a := by
      intro h
      apply hznotH
      rw [h]
      exact hH.vertexSet_subset (by
        rw [R.vertexSet_graph]
        exact ⟨a, hab.left_mem, rfl⟩)
    have hzb : z ≠ R.pos b := by
      intro h
      apply hznotH
      rw [h]
      exact hH.vertexSet_subset (by
        rw [R.vertexSet_graph]
        exact ⟨b, hab.right_mem, rfl⟩)
    exact (hH.edge_subset heS hf ⟨z, hzf, by
      rw [R.cell_edge hab]
      exact ⟨hze, by simp [hza, hzb]⟩, hznotH⟩).trans
        (Graph.edgeArc_subset_pointSet heR)

/-- The extension trace on the old skeleton occupies exactly the old skeleton. -/
theorem trace_pointSet (hH : IsSourceExtension R outer dom H Hdraw) :
    Graph.pointSet (Graph.traceGraph H Hdraw R.skeletonSet) Hdraw = R.skeletonSet :=
  Graph.pointSet_traceGraph_eq hH.isDrawing R.skeletonSet hH.skeletonSet_subset
    (trace_absorb hH)

/-- The trace supported on one old edge occupies that entire edge arc. -/
theorem edge_trace_pointSet (hH : IsSourceExtension R outer dom H Hdraw)
    {e : γ} (he : e ∈ E(S.skel)) :
    Graph.pointSet (Graph.traceGraph H Hdraw (edgeArc R.drawing e)) Hdraw =
      edgeArc R.drawing e := by
  have heR : e ∈ E(R.graph) := by rwa [R.edgeSet_graph]
  refine Graph.pointSet_traceGraph_eq hH.isDrawing _
    ((Graph.edgeArc_subset_pointSet heR).trans hH.skeletonSet_subset) ?_
  intro f hf hmeet
  obtain ⟨z, hzf, hze, hznotH⟩ := hmeet
  obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet he
  have hza : z ≠ R.pos a := by
    intro h
    apply hznotH
    rw [h]
    exact hH.vertexSet_subset (by
      rw [R.vertexSet_graph]
      exact ⟨a, hab.left_mem, rfl⟩)
  have hzb : z ≠ R.pos b := by
    intro h
    apply hznotH
    rw [h]
    exact hH.vertexSet_subset (by
      rw [R.vertexSet_graph]
      exact ⟨b, hab.right_mem, rfl⟩)
  exact hH.edge_subset he hf ⟨z, hzf, by
    rw [R.cell_edge hab]
    exact ⟨hze, by simp [hza, hzb]⟩, hznotH⟩

/-- Every old edge is the drawn carrier of a path in the extension graph. -/
theorem exists_edge_trace (hH : IsSourceExtension R outer dom H Hdraw)
    {e a b : γ} (hab : S.skel.IsLink e a b) :
    ∃ D : List γ, H.IsPath (R.pos a) D (R.pos b) ∧
      Graph.edgesCover Hdraw D = edgeArc R.drawing e := by
  let K := Graph.traceGraph H Hdraw (edgeArc R.drawing e)
  have hKle : K ≤ H := Graph.traceGraph_le _
  let _ : H.Finite := hH.finite
  let _ : K.Finite := Graph.Finite.of_le hKle
  have hpoint : pointSet K Hdraw = edgeArc R.drawing e :=
    edge_trace_pointSet hH hab.edge_mem
  have haH : R.pos a ∈ V(H) := hH.vertexSet_subset (by
    rw [R.vertexSet_graph]
    exact ⟨a, hab.left_mem, rfl⟩)
  have hbH : R.pos b ∈ V(H) := hH.vertexSet_subset (by
    rw [R.vertexSet_graph]
    exact ⟨b, hab.right_mem, rfl⟩)
  have hOldArc := R.isDrawing.edge_isArcBetween (hab.map R.pos)
  have haK : R.pos a ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haH, hOldArc.left_mem⟩
  have hbK : R.pos b ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbH, hOldArc.right_mem⟩
  have hKconn : K.Connected := Graph.connected_of_isPreconnected_pointSet
    (hH.isDrawing.mono hKle) (hpoint.symm ▸ hOldArc.isArc.isConnected.isPreconnected)
    ⟨R.pos a, haK⟩
  obtain ⟨D, hD⟩ := (hKconn.reaches haK hbK).exists_isPath
  have hDH : H.IsPath (R.pos a) D (R.pos b) := hD.mono hKle
  have hne : R.pos a ≠ R.pos b := R.isDrawing.ne_of_isLink (hab.map R.pos)
  have hPathArc : IsArcBetween (Graph.edgesCover Hdraw D) (R.pos a) (R.pos b) :=
    hH.isDrawing.path_isArcBetween hDH (hDH.ne_nil hne)
  have hcoverSub : Graph.edgesCover Hdraw D ⊆ edgeArc R.drawing e := by
    rw [← hpoint]
    exact Graph.edgesCover_subset_pointSet fun g hg => hD.edge_mem hg
  exact ⟨D, hDH, hPathArc.eq_of_subset_arc hOldArc hOldArc hcoverSub
    (Set.Subset.rfl)⟩

/-- The path tracing an old edge is contained in the trace supported on that edge. -/
theorem pathGraph_edge_trace_le (hH : IsSourceExtension R outer dom H Hdraw)
    {e a b : γ} (hab : S.skel.IsLink e a b) {D : List γ}
    (hD : H.IsPath (R.pos a) D (R.pos b))
    (hcover : Graph.edgesCover Hdraw D = edgeArc R.drawing e) :
    H.pathGraphOf (R.pos a) D ≤
      Graph.traceGraph H Hdraw (edgeArc R.drawing e) := by
  have hne : R.pos a ≠ R.pos b := R.isDrawing.ne_of_isLink (hab.map R.pos)
  have hPpoint : pointSet (H.pathGraphOf (R.pos a) D) Hdraw =
      Graph.edgesCover Hdraw D :=
    hH.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
  have hPle : H.pathGraphOf (R.pos a) D ≤ H := Graph.pathGraphOf_le hD.isWalk
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hPle.vertexSet_mono hz, hcover ▸ hPpoint ▸ (Or.inl hz)⟩
  · intro f x y hlink
    have hfP : f ∈ E(H.pathGraphOf (R.pos a) D) := hlink.edge_mem
    have hfD : f ∈ D := by
      rwa [Graph.pathGraphOf_edgeSet hD.isWalk] at hfP
    have hlinkH : H.IsLink f x y := hPle.isLink_mono hlink
    have hsub : edgeArc Hdraw f ⊆ edgeArc R.drawing e := by
      rw [← hcover]
      exact fun z hz => Graph.mem_edgesCover hfD hz
    have harc := hH.isDrawing.edge_isArcBetween hlinkH
    exact (Graph.traceGraph_isLink _).2
      ⟨hsub, hlinkH, hsub harc.left_mem, hsub harc.right_mem⟩

/-- Every old skeleton vertex belongs to the full skeleton trace. -/
theorem old_vertex_mem_trace (hH : IsSourceExtension R outer dom H Hdraw)
    {a : γ} (ha : a ∈ V(S.skel)) :
    R.pos a ∈ V(Graph.traceGraph H Hdraw R.skeletonSet) := by
  rw [Graph.traceGraph_vertexSet]
  exact ⟨hH.vertexSet_subset (by rw [R.vertexSet_graph]; exact ⟨a, ha, rfl⟩),
    R.pos_mem_skeletonSet ha⟩

/-- An old skeleton walk expands to a reachability witness in the extension trace. -/
theorem reaches_trace_of_isWalk (hH : IsSourceExtension R outer dom H Hdraw)
    {a b : γ} {W : List γ} (hW : S.skel.IsWalk a W b) :
    (Graph.traceGraph H Hdraw R.skeletonSet).Reaches (R.pos a) (R.pos b) := by
  induction hW with
  | nil ha => exact .refl (old_vertex_mem_trace hH ha)
  | @cons a w b e W hlink htail ih =>
    obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hlink
    have hPle : H.pathGraphOf (R.pos a) D ≤
        Graph.traceGraph H Hdraw R.skeletonSet :=
      (pathGraph_edge_trace_le hH hlink hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet
          (by rw [R.edgeSet_graph]; exact hlink.edge_mem)))
    have hreach : (H.pathGraphOf (R.pos a) D).Reaches (R.pos a) (R.pos w) :=
      ⟨D, hD.pathGraphOf.isWalk⟩
    exact (hreach.mono hPle).trans ih

/-- Any two old vertices are joined inside the extension trace. -/
theorem old_vertices_reach_trace (hH : IsSourceExtension R outer dom H Hdraw)
    (hR2 : R.graph.IsTwoConnected) {a b : γ}
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel)) :
    (Graph.traceGraph H Hdraw R.skeletonSet).Reaches (R.pos a) (R.pos b) := by
  have hS2 : S.skel.IsTwoConnected :=
    (Graph.isTwoConnected_map_iff R.injOn_pos).1 hR2
  obtain ⟨W, hW⟩ := hS2.connected.reaches ha hb
  exact reaches_trace_of_isWalk hH hW

/-- Every trace vertex reaches an old skeleton vertex. -/
theorem exists_reaches_old_vertex (hH : IsSourceExtension R outer dom H Hdraw)
    {x : Plane} (hx : x ∈ V(Graph.traceGraph H Hdraw R.skeletonSet)) :
    ∃ a ∈ V(S.skel),
      (Graph.traceGraph H Hdraw R.skeletonSet).Reaches x (R.pos a) := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(R.graph)
  · rw [R.vertexSet_graph] at hxold
    obtain ⟨a, ha, rfl⟩ := hxold
    exact ⟨a, ha, .refl (old_vertex_mem_trace hH ha)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, heR, hxe⟩ := Set.mem_iUnion₂.1 hxE
      have heS : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at heR
      obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet heS
      obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hab
      have hxwalk : x ∈ H.walkVertices (R.pos a) D :=
        hH.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(H.pathGraphOf (R.pos a) D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : H.pathGraphOf (R.pos a) D ≤
          Graph.traceGraph H Hdraw R.skeletonSet :=
        (pathGraph_edge_trace_le hH hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet heR))
      have haP : R.pos a ∈ V(H.pathGraphOf (R.pos a) D) :=
        Graph.mem_vertexSet_pathGraphOf_self
      exact ⟨a, hab.left_mem,
        ((hD.isPathGraph_pathGraphOf.connected.reaches hxP haP).mono hPle)⟩

/-- After deleting a distinct trace vertex, every remaining vertex still reaches an old one. -/
theorem exists_reaches_old_vertex_delete
    (hH : IsSourceExtension R outer dom H Hdraw) {c x : Plane}
    (hx : x ∈ V(Graph.traceGraph H Hdraw R.skeletonSet)) (hxc : x ≠ c) :
    ∃ a ∈ V(S.skel),
      ((Graph.traceGraph H Hdraw R.skeletonSet).deleteVerts {c}).Reaches x (R.pos a) := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(R.graph)
  · rw [R.vertexSet_graph] at hxold
    obtain ⟨a, ha, rfl⟩ := hxold
    exact ⟨a, ha, .refl (Graph.mem_deleteVerts_singleton_of_ne
      (old_vertex_mem_trace hH ha) hxc)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, heR, hxe⟩ := Set.mem_iUnion₂.1 hxE
      have heS : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at heR
      obtain ⟨a, b, hab⟩ := S.skel.exists_isLink_of_mem_edgeSet heS
      obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hab
      have hxwalk : x ∈ H.walkVertices (R.pos a) D :=
        hH.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(H.pathGraphOf (R.pos a) D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : H.pathGraphOf (R.pos a) D ≤
          Graph.traceGraph H Hdraw R.skeletonSet :=
        (pathGraph_edge_trace_le hH hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet heR))
      rcases hD.isPathGraph_pathGraphOf.reaches_an_end hxP hxc with hreach | hreach
      · exact ⟨a, hab.left_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩
      · exact ⟨b, hab.right_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩

/-- An old walk avoiding a vertex expands to a trace walk avoiding its realized point. -/
theorem reaches_trace_delete_of_deleteVerts_isWalk
    (hH : IsSourceExtension R outer dom H Hdraw)
    {z a b : γ} {W : List γ}
    (hzS : z ∈ V(S.skel))
    (hW : (S.skel.deleteVerts {z}).IsWalk a W b) :
    ((Graph.traceGraph H Hdraw R.skeletonSet).deleteVerts {R.pos z}).Reaches
      (R.pos a) (R.pos b) := by
  induction hW with
  | nil ha =>
      rw [Graph.mem_deleteVerts_singleton] at ha
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (old_vertex_mem_trace hH ha.1) (fun h => ha.2 (by
          simpa using R.injOn_pos ha.1 hzS h)))
  | @cons a w b e W hlink htail ih =>
    rw [Graph.deleteVerts_isLink] at hlink
    have hlinkS := hlink.1
    obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hlinkS
    have hne : R.pos a ≠ R.pos w := R.isDrawing.ne_of_isLink (hlinkS.map R.pos)
    have hPpoint : pointSet (H.pathGraphOf (R.pos a) D) Hdraw =
        Graph.edgesCover Hdraw D :=
      hH.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hznot : R.pos z ∉ H.walkVertices (R.pos a) D := by
      intro hz
      have hzarc : R.pos z ∈ edgeArc R.drawing e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      have hzV : R.pos z ∈ V(R.graph) := by
        rw [R.vertexSet_graph]
        exact ⟨z, hzS, rfl⟩
      rcases R.isDrawing.vertex_mem_edgeArc (hlinkS.map R.pos) hzV hzarc with hza | hzw
      · have haz : a ≠ z := by simpa using hlink.2.1
        exact haz (R.injOn_pos hlinkS.left_mem hzS hza.symm)
      · have hwz : w ≠ z := by simpa using hlink.2.2
        exact hwz (R.injOn_pos hlinkS.right_mem hzS hzw.symm)
    have hPle : H.pathGraphOf (R.pos a) D ≤
        Graph.traceGraph H Hdraw R.skeletonSet :=
      (pathGraph_edge_trace_le hH hlinkS hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet
          (by rw [R.edgeSet_graph]; exact hlinkS.edge_mem)))
    have hreach : ((H.pathGraphOf (R.pos a) D).deleteVerts {R.pos z}).Reaches
        (R.pos a) (R.pos w) :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hznot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- An old walk avoiding an edge expands to a trace walk avoiding an interior point of it. -/
theorem reaches_trace_delete_of_deleteEdges_isWalk
    (hH : IsSourceExtension R outer dom H Hdraw)
    {c : Plane} (hcold : c ∉ V(R.graph))
    {e₀ : γ} (he₀ : e₀ ∈ E(S.skel)) (hce₀ : c ∈ edgeArc R.drawing e₀)
    {a b : γ} {W : List γ}
    (hW : (S.skel.deleteEdges {e₀}).IsWalk a W b) :
    ((Graph.traceGraph H Hdraw R.skeletonSet).deleteVerts {c}).Reaches
      (R.pos a) (R.pos b) := by
  induction hW with
  | @nil x hx =>
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (old_vertex_mem_trace hH (by simpa using hx)) (fun h => hcold (by
          rw [R.vertexSet_graph]
          exact ⟨x, by simpa using hx, h⟩)))
  | @cons a w b e W hlink htail ih =>
    change S.skel.IsLink e a w ∧ e ∉ ({e₀} : Set γ) at hlink
    have hlinkS := hlink.1
    have hee₀ : e ≠ e₀ := by simpa using hlink.2
    obtain ⟨D, hD, hcover⟩ := exists_edge_trace hH hlinkS
    have hne : R.pos a ≠ R.pos w := R.isDrawing.ne_of_isLink (hlinkS.map R.pos)
    have hPpoint : pointSet (H.pathGraphOf (R.pos a) D) Hdraw =
        Graph.edgesCover Hdraw D :=
      hH.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hcnot : c ∉ H.walkVertices (R.pos a) D := by
      intro hc
      have hce : c ∈ edgeArc R.drawing e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      exact hcold (R.isDrawing.edge_inter he₀ hlinkS.edge_mem (Ne.symm hee₀)
        hce₀ hce |>.1)
    have hPle : H.pathGraphOf (R.pos a) D ≤
        Graph.traceGraph H Hdraw R.skeletonSet :=
      (pathGraph_edge_trace_le hH hlinkS hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet
          (by rw [R.edgeSet_graph]; exact hlinkS.edge_mem)))
    have hreach : ((H.pathGraphOf (R.pos a) D).deleteVerts {c}).Reaches
        (R.pos a) (R.pos w) :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hcnot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- The part of an extension graph supported on a 2-connected old skeleton is 2-connected. -/
theorem trace_isTwoConnected
    (hH : IsSourceExtension R outer dom H Hdraw)
    (hR2 : R.graph.IsTwoConnected) :
    (Graph.traceGraph H Hdraw R.skeletonSet).IsTwoConnected := by
  let K := Graph.traceGraph H Hdraw R.skeletonSet
  have hS2 : S.skel.IsTwoConnected :=
    (Graph.isTwoConnected_map_iff R.injOn_pos).1 hR2
  have hVold : V(R.graph) ⊆ V(K) := by
    rw [R.vertexSet_graph]
    rintro x ⟨a, ha, rfl⟩
    exact old_vertex_mem_trace hH ha
  refine {
    hasThreeVertices := hR2.hasThreeVertices.mono hVold
    connected := ?_
    deleteVerts_connected := ?_
  }
  · obtain ⟨a, ha⟩ := hS2.connected.nonempty
    refine Graph.Connected.of_hub (old_vertex_mem_trace hH ha) ?_
    intro x hx
    obtain ⟨b, hb, hxb⟩ := exists_reaches_old_vertex hH hx
    exact (old_vertices_reach_trace hH hR2 ha hb).trans hxb.symm
  · intro c hcK
    obtain ⟨p, hpR, hpc, -⟩ := hR2.hasThreeVertices.exists_ne_ne c c
    have hpK : p ∈ V(K) := hVold hpR
    have hpDel : p ∈ V(K.deleteVerts {c}) :=
      Graph.mem_deleteVerts_singleton_of_ne hpK hpc
    refine Graph.Connected.of_hub hpDel ?_
    intro x hx
    rw [Graph.mem_deleteVerts_singleton] at hx
    obtain ⟨a, ha, hxa⟩ := exists_reaches_old_vertex_delete hH hx.1 hx.2
    obtain ⟨b, hb, hpb⟩ := exists_reaches_old_vertex_delete hH hpK hpc
    have habReach : (K.deleteVerts {c}).Reaches (R.pos a) (R.pos b) := by
      by_cases hcold : c ∈ V(R.graph)
      · rw [R.vertexSet_graph] at hcold
        obtain ⟨z, hzS, hzc⟩ := hcold
        have haDel := hxa.right_mem
        have hbDel := hpb.right_mem
        rw [Graph.mem_deleteVerts_singleton] at haDel hbDel
        have haz : a ≠ z := by
          intro h
          apply haDel.2
          rw [h, hzc]
        have hbz : b ≠ z := by
          intro h
          apply hbDel.2
          rw [h, hzc]
        have haSdel : a ∈ V(S.skel.deleteVerts {z}) :=
          Graph.mem_deleteVerts_singleton_of_ne ha haz
        have hbSdel : b ∈ V(S.skel.deleteVerts {z}) :=
          Graph.mem_deleteVerts_singleton_of_ne hb hbz
        obtain ⟨W, hW⟩ := (hS2.deleteVerts_connected hzS).reaches haSdel hbSdel
        simpa [hzc] using reaches_trace_delete_of_deleteVerts_isWalk hH hzS hW
      · have hcskel : c ∈ R.skeletonSet := by
          rw [Graph.traceGraph_vertexSet] at hcK
          exact hcK.2
        rcases hcskel with hcV | hcE
        · exact absurd hcV hcold
        · obtain ⟨e₀, he₀R, hce₀⟩ := Set.mem_iUnion₂.1 hcE
          have he₀ : e₀ ∈ E(S.skel) := by rwa [R.edgeSet_graph] at he₀R
          obtain ⟨u, v, huv⟩ := S.skel.exists_isLink_of_mem_edgeSet he₀
          have hcyc : S.skel.LiesOnCycle e₀ :=
            (Graph.liesOnCycle_iff_deleteEdges_reaches huv).2 (hS2.no_bridge huv)
          have hdel : (S.skel.deleteEdges {e₀}).Connected :=
            hS2.connected.deleteEdges_singleton hcyc
          have haDel : a ∈ V(S.skel.deleteEdges {e₀}) := by simpa using ha
          have hbDel : b ∈ V(S.skel.deleteEdges {e₀}) := by simpa using hb
          obtain ⟨W, hW⟩ := hdel.reaches haDel hbDel
          exact reaches_trace_delete_of_deleteEdges_isWalk hH hcold he₀ hce₀ hW
    exact hpb.trans (habReach.symm.trans hxa.symm)

/-! ## Traces of arbitrary plane subdivisions

The preceding result is phrased for a realized cell structure because that is the interface
used by finite transfer.  Overlay assembly also needs the same fact for an ordinary plane
graph, notably the anchored square mesh.  The proof only uses the local subdivision data
recorded below; in particular it does not use 2-connectivity of the ambient graph. -/

variable {β δ : Type*} {G : Graph Plane β} {Gdraw : β → ℝ → Plane}
  {K : Graph Plane δ} {Kdraw : δ → ℝ → Plane}

/-- The local data saying that `K` contains an edge subdivision of the drawn plane graph `G`.
Crossings with other parts of `K` are allowed at vertices of `K`. -/
structure IsPlaneSubdivisionExtension (G : Graph Plane β) (Gdraw : β → ℝ → Plane)
    (K : Graph Plane δ) (Kdraw : δ → ℝ → Plane) : Prop where
  /-- The ambient graph is finite. -/
  finite : K.Finite
  /-- The old graph is drawn in the plane. -/
  oldIsDrawing : G.IsDrawing Gdraw
  /-- The ambient graph is drawn in the plane. -/
  isDrawing : K.IsDrawing Kdraw
  /-- Every old vertex is an ambient vertex. -/
  vertexSet_subset : V(G) ⊆ V(K)
  /-- The old carrier lies in the ambient carrier. -/
  pointSet_subset : pointSet G Gdraw ⊆ pointSet K Kdraw
  /-- An ambient edge meeting an old edge away from ambient vertices is contained in that old
  edge. -/
  edge_subset : ∀ ⦃e⦄, e ∈ E(G) → ∀ ⦃f⦄, f ∈ E(K) →
    (edgeArc Kdraw f ∩ (edgeArc Gdraw e \ V(K))).Nonempty →
      edgeArc Kdraw f ⊆ edgeArc Gdraw e

namespace IsPlaneSubdivisionExtension

/-- An ambient edge meeting the old carrier away from ambient vertices is absorbed by it. -/
theorem trace_absorb (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw) :
    ∀ ⦃f⦄, f ∈ E(K) →
      (edgeArc Kdraw f ∩ (pointSet G Gdraw \ V(K))).Nonempty →
      edgeArc Kdraw f ⊆ pointSet G Gdraw := by
  intro f hf hmeet
  obtain ⟨z, hzf, hzold, hznotK⟩ := hmeet
  rcases hzold with hzV | hzE
  · exact absurd (h.vertexSet_subset hzV) hznotK
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
    exact (h.edge_subset he hf ⟨z, hzf, hze, hznotK⟩).trans
      (Graph.edgeArc_subset_pointSet he)

/-- The trace on the old carrier occupies exactly that carrier. -/
theorem trace_pointSet (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw) :
    pointSet (Graph.traceGraph K Kdraw (pointSet G Gdraw)) Kdraw = pointSet G Gdraw :=
  Graph.pointSet_traceGraph_eq h.isDrawing _ h.pointSet_subset h.trace_absorb

/-- The trace supported on one old edge occupies the entire old edge. -/
theorem edge_trace_pointSet (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {e : β} (he : e ∈ E(G)) :
    pointSet (Graph.traceGraph K Kdraw (edgeArc Gdraw e)) Kdraw = edgeArc Gdraw e := by
  refine Graph.pointSet_traceGraph_eq h.isDrawing _
    ((Graph.edgeArc_subset_pointSet he).trans h.pointSet_subset) ?_
  intro f hf hmeet
  exact h.edge_subset he hf hmeet

/-- Every old edge is the carrier of an ambient path. -/
theorem exists_edge_trace (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {e : β} {a b : Plane} (hab : G.IsLink e a b) :
    ∃ D : List δ, K.IsPath a D b ∧ edgesCover Kdraw D = edgeArc Gdraw e := by
  let T := Graph.traceGraph K Kdraw (edgeArc Gdraw e)
  have hTK : T ≤ K := Graph.traceGraph_le _
  let _ : K.Finite := h.finite
  let _ : T.Finite := Graph.Finite.of_le hTK
  have hpoint : pointSet T Kdraw = edgeArc Gdraw e := h.edge_trace_pointSet hab.edge_mem
  have haK : a ∈ V(K) := h.vertexSet_subset hab.left_mem
  have hbK : b ∈ V(K) := h.vertexSet_subset hab.right_mem
  have hOldArc := h.oldIsDrawing.edge_isArcBetween hab
  have haT : a ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haK, hOldArc.left_mem⟩
  have hbT : b ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbK, hOldArc.right_mem⟩
  have hTconn : T.Connected := Graph.connected_of_isPreconnected_pointSet
    (h.isDrawing.mono hTK) (hpoint.symm ▸ hOldArc.isArc.isConnected.isPreconnected) ⟨a, haT⟩
  obtain ⟨D, hD⟩ := (hTconn.reaches haT hbT).exists_isPath
  have hDK : K.IsPath a D b := hD.mono hTK
  have hne : a ≠ b := h.oldIsDrawing.ne_of_isLink hab
  have hPathArc : IsArcBetween (edgesCover Kdraw D) a b :=
    h.isDrawing.path_isArcBetween hDK (hDK.ne_nil hne)
  have hcoverSub : edgesCover Kdraw D ⊆ edgeArc Gdraw e := by
    rw [← hpoint]
    exact Graph.edgesCover_subset_pointSet fun g hg => hD.edge_mem hg
  exact ⟨D, hDK, hPathArc.eq_of_subset_arc hOldArc hOldArc hcoverSub Set.Subset.rfl⟩

/-- The path tracing an old edge lies in the trace supported on that edge. -/
theorem pathGraph_edge_trace_le (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {e : β} {a b : Plane} (hab : G.IsLink e a b) {D : List δ}
    (hD : K.IsPath a D b) (hcover : edgesCover Kdraw D = edgeArc Gdraw e) :
    K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (edgeArc Gdraw e) := by
  have hne : a ≠ b := h.oldIsDrawing.ne_of_isLink hab
  have hPpoint : pointSet (K.pathGraphOf a D) Kdraw = edgesCover Kdraw D :=
    h.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
  have hPK : K.pathGraphOf a D ≤ K := Graph.pathGraphOf_le hD.isWalk
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hPK.vertexSet_mono hz, hcover ▸ hPpoint ▸ Or.inl hz⟩
  · intro f x y hlink
    have hfP : f ∈ E(K.pathGraphOf a D) := hlink.edge_mem
    have hfD : f ∈ D := by
      rwa [Graph.pathGraphOf_edgeSet hD.isWalk] at hfP
    have hlinkK : K.IsLink f x y := hPK.isLink_mono hlink
    have hsub : edgeArc Kdraw f ⊆ edgeArc Gdraw e := by
      rw [← hcover]
      exact fun z hz => Graph.mem_edgesCover hfD hz
    have harc := h.isDrawing.edge_isArcBetween hlinkK
    exact (Graph.traceGraph_isLink _).2
      ⟨hsub, hlinkK, hsub harc.left_mem, hsub harc.right_mem⟩

/-- Every old vertex belongs to the full old-carrier trace. -/
theorem old_vertex_mem_trace (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {a : Plane} (ha : a ∈ V(G)) :
    a ∈ V(Graph.traceGraph K Kdraw (pointSet G Gdraw)) := by
  rw [Graph.traceGraph_vertexSet]
  exact ⟨h.vertexSet_subset ha, Or.inl ha⟩

/-- An old walk expands to reachability in the ambient trace. -/
theorem reaches_trace_of_isWalk (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {a b : Plane} {W : List β} (hW : G.IsWalk a W b) :
    (Graph.traceGraph K Kdraw (pointSet G Gdraw)).Reaches a b := by
  induction hW with
  | nil ha => exact .refl (h.old_vertex_mem_trace ha)
  | @cons a w b e W hlink htail ih =>
    obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hlink
    have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
      (h.pathGraph_edge_trace_le hlink hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet hlink.edge_mem))
    have hreach : (K.pathGraphOf a D).Reaches a w := ⟨D, hD.pathGraphOf.isWalk⟩
    exact (hreach.mono hPle).trans ih

/-- Any two old vertices are joined inside the ambient trace. -/
theorem old_vertices_reach_trace (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    (hG2 : G.IsTwoConnected) {a b : Plane} (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    (Graph.traceGraph K Kdraw (pointSet G Gdraw)).Reaches a b := by
  obtain ⟨W, hW⟩ := hG2.connected.reaches ha hb
  exact h.reaches_trace_of_isWalk hW

/-- Every trace vertex reaches an old vertex. -/
theorem exists_reaches_old_vertex (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {x : Plane} (hx : x ∈ V(Graph.traceGraph K Kdraw (pointSet G Gdraw))) :
    ∃ a ∈ V(G), (Graph.traceGraph K Kdraw (pointSet G Gdraw)).Reaches x a := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(G)
  · exact ⟨x, hxold, .refl (h.old_vertex_mem_trace hxold)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxE
      obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet he
      obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hab
      have hxwalk : x ∈ K.walkVertices a D :=
        h.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(K.pathGraphOf a D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
        (h.pathGraph_edge_trace_le hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet he))
      have haP : a ∈ V(K.pathGraphOf a D) := Graph.mem_vertexSet_pathGraphOf_self
      exact ⟨a, hab.left_mem,
        (hD.isPathGraph_pathGraphOf.connected.reaches hxP haP).mono hPle⟩

/-- After deleting a distinct trace vertex, every remaining vertex still reaches an old one. -/
theorem exists_reaches_old_vertex_delete
    (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw) {c x : Plane}
    (hx : x ∈ V(Graph.traceGraph K Kdraw (pointSet G Gdraw))) (hxc : x ≠ c) :
    ∃ a ∈ V(G),
      ((Graph.traceGraph K Kdraw (pointSet G Gdraw)).deleteVerts {c}).Reaches x a := by
  rw [Graph.traceGraph_vertexSet] at hx
  by_cases hxold : x ∈ V(G)
  · exact ⟨x, hxold, .refl (Graph.mem_deleteVerts_singleton_of_ne
      (h.old_vertex_mem_trace hxold) hxc)⟩
  · rcases hx.2 with hxV | hxE
    · exact absurd hxV hxold
    · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxE
      obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet he
      obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hab
      have hxwalk : x ∈ K.walkVertices a D :=
        h.isDrawing.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hx.1 (hcover ▸ hxe)
      have hxP : x ∈ V(K.pathGraphOf a D) := by
        rw [Graph.pathGraphOf_vertexSet]
        exact hxwalk
      have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
        (h.pathGraph_edge_trace_le hab hD hcover).trans
          (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet he))
      rcases hD.isPathGraph_pathGraphOf.reaches_an_end hxP hxc with hreach | hreach
      · exact ⟨a, hab.left_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩
      · exact ⟨b, hab.right_mem, hreach.mono (Graph.deleteVerts_mono hPle _)⟩

/-- An old walk avoiding a vertex expands to a trace walk avoiding that vertex. -/
theorem reaches_trace_delete_of_deleteVerts_isWalk
    (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {z a b : Plane} {W : List β} (hzG : z ∈ V(G))
    (hW : (G.deleteVerts {z}).IsWalk a W b) :
    ((Graph.traceGraph K Kdraw (pointSet G Gdraw)).deleteVerts {z}).Reaches a b := by
  induction hW with
  | nil ha =>
      rw [Graph.mem_deleteVerts_singleton] at ha
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (h.old_vertex_mem_trace ha.1) ha.2)
  | @cons a w b e W hlink htail ih =>
    rw [Graph.deleteVerts_isLink] at hlink
    have hlinkG := hlink.1
    obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hlinkG
    have hne : a ≠ w := h.oldIsDrawing.ne_of_isLink hlinkG
    have hPpoint : pointSet (K.pathGraphOf a D) Kdraw = edgesCover Kdraw D :=
      h.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hznot : z ∉ K.walkVertices a D := by
      intro hz
      have hzarc : z ∈ edgeArc Gdraw e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      rcases h.oldIsDrawing.vertex_mem_edgeArc hlinkG hzG hzarc with hza | hzw
      · exact hlink.2.1 hza.symm
      · exact hlink.2.2 hzw.symm
    have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
      (h.pathGraph_edge_trace_le hlinkG hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet hlinkG.edge_mem))
    have hreach : ((K.pathGraphOf a D).deleteVerts {z}).Reaches a w :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hznot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- An old walk avoiding an edge expands to a trace walk avoiding an interior point of it. -/
theorem reaches_trace_delete_of_deleteEdges_isWalk
    (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    {c : Plane} (hcold : c ∉ V(G)) {e₀ : β} (he₀ : e₀ ∈ E(G))
    (hce₀ : c ∈ edgeArc Gdraw e₀) {a b : Plane} {W : List β}
    (hW : (G.deleteEdges {e₀}).IsWalk a W b) :
    ((Graph.traceGraph K Kdraw (pointSet G Gdraw)).deleteVerts {c}).Reaches a b := by
  induction hW with
  | @nil x hx =>
      exact .refl (Graph.mem_deleteVerts_singleton_of_ne
        (h.old_vertex_mem_trace (by simpa using hx)) (fun hxc => hcold (hxc ▸ by simpa using hx)))
  | @cons a w b e W hlink htail ih =>
    change G.IsLink e a w ∧ e ∉ ({e₀} : Set β) at hlink
    have hlinkG := hlink.1
    have hee₀ : e ≠ e₀ := by simpa using hlink.2
    obtain ⟨D, hD, hcover⟩ := h.exists_edge_trace hlinkG
    have hne : a ≠ w := h.oldIsDrawing.ne_of_isLink hlinkG
    have hPpoint : pointSet (K.pathGraphOf a D) Kdraw = edgesCover Kdraw D :=
      h.isDrawing.pointSet_pathGraphOf hD.isWalk (hD.ne_nil hne)
    have hcnot : c ∉ K.walkVertices a D := by
      intro hc
      have hce : c ∈ edgeArc Gdraw e := by
        rw [← hcover, ← hPpoint]
        exact Or.inl (by rwa [Graph.pathGraphOf_vertexSet])
      exact hcold (h.oldIsDrawing.edge_inter he₀ hlinkG.edge_mem (Ne.symm hee₀)
        hce₀ hce |>.1)
    have hPle : K.pathGraphOf a D ≤ Graph.traceGraph K Kdraw (pointSet G Gdraw) :=
      (h.pathGraph_edge_trace_le hlinkG hD hcover).trans
        (Graph.traceGraph_mono (Graph.edgeArc_subset_pointSet hlinkG.edge_mem))
    have hreach : ((K.pathGraphOf a D).deleteVerts {c}).Reaches a w :=
      ⟨D, hD.pathGraphOf.isWalk.deleteVerts_singleton (by
        rw [Graph.walkVertices_pathGraphOf]
        exact hcnot)⟩
    exact (hreach.mono (Graph.deleteVerts_mono hPle _)).trans ih

/-- The part of an ambient plane graph supported on a 2-connected old graph is 2-connected.
No connectivity assumption on the ambient graph is needed. -/
theorem trace_isTwoConnected (h : IsPlaneSubdivisionExtension G Gdraw K Kdraw)
    (hG2 : G.IsTwoConnected) :
    (Graph.traceGraph K Kdraw (pointSet G Gdraw)).IsTwoConnected := by
  let T := Graph.traceGraph K Kdraw (pointSet G Gdraw)
  have hVold : V(G) ⊆ V(T) := fun _ hz => h.old_vertex_mem_trace hz
  have hthree : T.HasThreeVertices := by
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hG2.hasThreeVertices
    exact ⟨a, hVold ha, b, hVold hb, c, hVold hc, hab, hac, hbc⟩
  refine {
    hasThreeVertices := hthree
    connected := ?_
    deleteVerts_connected := ?_
  }
  · obtain ⟨a, ha⟩ := hG2.connected.nonempty
    refine Graph.Connected.of_hub (h.old_vertex_mem_trace ha) ?_
    intro x hx
    obtain ⟨b, hb, hxb⟩ := h.exists_reaches_old_vertex hx
    exact (h.old_vertices_reach_trace hG2 ha hb).trans hxb.symm
  · intro c hcT
    obtain ⟨p, hpG, hpc, -⟩ := hG2.hasThreeVertices.exists_ne_ne c c
    have hpT : p ∈ V(T) := hVold hpG
    have hpDel : p ∈ V(T.deleteVerts {c}) :=
      Graph.mem_deleteVerts_singleton_of_ne hpT hpc
    refine Graph.Connected.of_hub hpDel ?_
    intro x hx
    rw [Graph.mem_deleteVerts_singleton] at hx
    obtain ⟨a, ha, hxa⟩ := h.exists_reaches_old_vertex_delete hx.1 hx.2
    obtain ⟨b, hb, hpb⟩ := h.exists_reaches_old_vertex_delete hpT hpc
    have habReach : (T.deleteVerts {c}).Reaches a b := by
      by_cases hcold : c ∈ V(G)
      · have haDel := hxa.right_mem
        have hbDel := hpb.right_mem
        rw [Graph.mem_deleteVerts_singleton] at haDel hbDel
        have hac : a ≠ c := haDel.2
        have hbc : b ≠ c := hbDel.2
        have haGdel : a ∈ V(G.deleteVerts {c}) :=
          Graph.mem_deleteVerts_singleton_of_ne ha hac
        have hbGdel : b ∈ V(G.deleteVerts {c}) :=
          Graph.mem_deleteVerts_singleton_of_ne hb hbc
        obtain ⟨W, hW⟩ := (hG2.deleteVerts_connected hcold).reaches haGdel hbGdel
        exact h.reaches_trace_delete_of_deleteVerts_isWalk hcold hW
      · have hcpoint : c ∈ pointSet G Gdraw := by
          rw [Graph.traceGraph_vertexSet] at hcT
          exact hcT.2
        rcases hcpoint with hcV | hcE
        · exact absurd hcV hcold
        · obtain ⟨e₀, he₀, hce₀⟩ := Set.mem_iUnion₂.1 hcE
          obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he₀
          have hcyc : G.LiesOnCycle e₀ :=
            (Graph.liesOnCycle_iff_deleteEdges_reaches huv).2 (hG2.no_bridge huv)
          have hdel : (G.deleteEdges {e₀}).Connected :=
            hG2.connected.deleteEdges_singleton hcyc
          have haDel : a ∈ V(G.deleteEdges {e₀}) := by simpa using ha
          have hbDel : b ∈ V(G.deleteEdges {e₀}) := by simpa using hb
          obtain ⟨W, hW⟩ := hdel.reaches haDel hbDel
          exact h.reaches_trace_delete_of_deleteEdges_isWalk hcold he₀ hce₀ hW
    exact hpb.trans (habReach.symm.trans hxa.symm)

end IsPlaneSubdivisionExtension

end Schoenflies

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- Replace every occurrence of a distinguished edge in a walk by its two-edge subdivision. -/
theorem exists_substWalk_raw {edge left right newEdge₁ newEdge₂ u v : γ}
    {W : List γ} (hl : S.skel.IsLink edge left right)
    (h : S.skel.IsWalk u W v) :
    ∃ W', CellStructure.SubstWalk S edge left right newEdge₁ newEdge₂ u W W' := by
  induction h with
  | nil hx => exact ⟨[], .nil _⟩
  | @cons a w b f W hfw _ ih =>
    obtain ⟨W', hW'⟩ := ih
    by_cases hf : f = edge
    · subst hf
      rcases hl.eq_and_eq_or_eq_and_eq hfw with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · subst h₁; subst h₂; exact ⟨_, .forward hW'⟩
      · subst h₁; subst h₂; exact ⟨_, .backward hW'⟩
    · exact ⟨_, .other hfw hf hW'⟩

/-- Build subdivision data for an edge from three pairwise distinct fresh cell names. -/
theorem exists_subdivData (hcycles : S.BoundaryCycles)
    {edge left right newVertex newEdge₁ newEdge₂ : γ}
    (hl : S.skel.IsLink edge left right)
    (hv : newVertex ∉ S.cells) (he₁ : newEdge₁ ∉ S.cells)
    (he₂ : newEdge₂ ∉ S.cells) (hv₁ : newVertex ≠ newEdge₁)
    (hv₂ : newVertex ≠ newEdge₂) (he₁₂ : newEdge₁ ≠ newEdge₂) :
    ∃ d : S.SubdivData, d.edge = edge ∧ d.left = left ∧ d.right = right ∧
      d.newVertex = newVertex ∧ d.newEdge₁ = newEdge₁ ∧ d.newEdge₂ = newEdge₂ := by
  classical
  have hex : ∀ F : γ, ∃ W' : List γ, F ∈ S.faces → ∃ u,
      S.skel.IsWalk u (S.boundary F) u ∧
        CellStructure.SubstWalk S edge left right newEdge₁ newEdge₂ u
          (S.boundary F) W' := by
    intro F
    by_cases hF : F ∈ S.faces
    · let c := hcycles.faceCycle F hF
      obtain ⟨W', hW'⟩ := exists_substWalk_raw hl c.isWalk
      exact ⟨W', fun _ => ⟨c.target, c.isWalk, hW'⟩⟩
    · exact ⟨[], fun h => (hF h).elim⟩
  choose newBoundary hnewBoundary using hex
  let d : S.SubdivData := {
    edge := edge
    left := left
    right := right
    newVertex := newVertex
    newEdge₁ := newEdge₁
    newEdge₂ := newEdge₂
    isLink := hl
    newVertex_notMem := hv
    newEdge₁_notMem := he₁
    newEdge₂_notMem := he₂
    newVertex_ne₁ := hv₁
    newVertex_ne₂ := hv₂
    newEdge_ne := he₁₂
    newBoundary := newBoundary
    boundary_subst := by
      intro F hF
      exact hnewBoundary F hF
  }
  exact ⟨d, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace SubdivData

/-- Subdividing one edge of a 2-connected skeleton preserves 2-connectivity. -/
theorem skeleton_isTwoConnected {d : S.SubdivData}
    (hS2 : S.skel.IsTwoConnected) (hlr : d.left ≠ d.right) :
    d.skeleton.IsTwoConnected := by
  have htail : d.skeleton.IsPath d.newVertex [d.newEdge₂] d.right :=
    .single d.isLink_newEdge₂ (fun h => d.newVertex_notMem (h ▸ d.right_mem_cells))
  have hfresh : d.left ∉ d.skeleton.walkVertices d.newVertex [d.newEdge₂] := by
    intro h
    rw [Graph.walkVertices_cons d.isLink_newEdge₂, Graph.walkVertices_nil] at h
    rcases h with h | h
    · exact d.newVertex_notMem (h.symm ▸ d.left_mem_cells)
    · exact hlr (by simpa using h)
  have hpath : d.skeleton.IsPath d.left [d.newEdge₁, d.newEdge₂] d.right :=
    .cons d.isLink_newEdge₁ htail hfresh
  let P := d.skeleton.pathGraphOf d.left [d.newEdge₁, d.newEdge₂]
  have hP : P.IsPathGraph d.left [d.newEdge₁, d.newEdge₂] d.right :=
    hpath.isPathGraph_pathGraphOf
  have hdel : S.skel.deleteEdges {d.edge} ≤ d.skeleton := by
    refine ⟨?_, ?_⟩
    · rw [Graph.vertexSet_deleteEdges, d.skeleton_vertexSet]
      exact Set.subset_insert _ _
    · intro e x y hlink
      change S.skel.IsLink e x y ∧ e ∉ ({d.edge} : Set γ) at hlink
      exact d.skeleton_isLink_of_old (by simpa using hlink.2) hlink.1
  have hPle : P ≤ d.skeleton := Graph.pathGraphOf_le hpath.isWalk
  have hcompat : (S.skel.deleteEdges {d.edge}).Compatible P :=
    Graph.Compatible.of_le_le hdel hPle
  have hnew : ∀ x ∈ V(P), x ≠ d.left → x ≠ d.right → x ∉ V(S.skel) := by
    intro x hx hxl hxr hxS
    rw [Graph.pathGraphOf_vertexSet, Graph.walkVertices_cons d.isLink_newEdge₁,
      Graph.walkVertices_cons d.isLink_newEdge₂, Graph.walkVertices_nil] at hx
    rcases hx with rfl | rfl | hx
    · exact hxl rfl
    · exact d.newVertex_notMem (S.mem_cells_of_mem_vertexSet hxS)
    · exact hxr (by simpa using hx)
  have hB2 : ((S.skel.deleteEdges {d.edge}).union P).IsTwoConnected :=
    hS2.replace_edge_by_path d.isLink hlr hcompat hP hnew
  have hBle : (S.skel.deleteEdges {d.edge}).union P ≤ d.skeleton :=
    Graph.union_le hdel hPle
  apply hB2.spanning_mono hBle
  intro x hx
  rw [d.skeleton_vertexSet] at hx
  rcases hx with rfl | hx
  · apply Set.mem_union_right
    rw [Graph.pathGraphOf_vertexSet, Graph.walkVertices_cons d.isLink_newEdge₁,
      Graph.walkVertices_cons d.isLink_newEdge₂, Graph.walkVertices_nil]
    simp
  · exact Set.mem_union_left _ (by simpa using hx)

/-- A geometric edge subdivision leaves the realized outer set unchanged. -/
theorem outerSet_realize {d : S.SubdivData} {R : S.Realization}
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (d.realize R t ht).outerSet = R.outerSet := by
  by_cases he : d.edge ∈ E(S.outerGraph)
  · have hedge : (⋃ f ∈ E(S.outerGraph), Graph.edgeArc R.drawing f) =
        Graph.edgeArc R.drawing d.edge ∪
          ⋃ f ∈ E(S.outerGraph) \ {d.edge}, Graph.edgeArc R.drawing f := by
      rw [← Set.biUnion_insert, Set.insert_sdiff_singleton, Set.insert_eq_of_mem he]
    have hnew : (⋃ f ∈ E(d.outer), Graph.edgeArc (d.realizeDrawing R t) f) =
        Graph.edgeArc R.drawing d.edge ∪
          ⋃ f ∈ E(S.outerGraph) \ {d.edge}, Graph.edgeArc R.drawing f := by
      rw [d.outer_edgeSet_of_mem he, Set.biUnion_insert, Set.biUnion_insert,
        Set.iUnion₂_congr (fun f (hf : f ∈ E(S.outerGraph) \ {d.edge}) =>
          d.edgeArc_of_ne (R := R) (t := t)
            (d.ne_newEdge₁_of_mem_cells
              (S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hf.1)))
            (d.ne_newEdge₂_of_mem_cells
              (S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hf.1)))),
        ← Set.union_assoc, d.edgeArc_new_union ht]
    have hvertex : d.realizePos R t '' V(d.outer) =
        insert (R.drawing d.edge t) (R.pos '' V(S.outerGraph)) := by
      rw [CellStructure.SubdivData.outer, subdivGraph_vertexSet]
      simp only [d.outer_isLink he, and_true, Set.ofPred_eq_eq_singleton,
        Set.image_union, Set.image_singleton, d.realizePos_newVertex]
      rw [Set.union_comm]
      congr 1
      apply Set.image_congr
      intro z hz
      exact d.realizePos_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hz)
    have hM : R.drawing d.edge t ∈ Graph.edgeArc R.drawing d.edge :=
      ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
    change Graph.pointSet (d.outer.map (d.realizePos R t)) (d.realizeDrawing R t) =
      Graph.pointSet (S.outerGraph.map R.pos) R.drawing
    rw [Graph.pointSet, Graph.pointSet, Graph.vertexSet_map, Graph.vertexSet_map,
      Graph.edgeSet_map, Graph.edgeSet_map, hvertex, hnew, hedge, Set.insert_union,
      Set.insert_eq_of_mem (Set.mem_union_right _ (Set.mem_union_left _ hM))]
  · change Graph.pointSet (d.outer.map (d.realizePos R t)) (d.realizeDrawing R t) =
      Graph.pointSet (S.outerGraph.map R.pos) R.drawing
    rw [d.outer_eq he]
    have hgraph : S.outerGraph.map (d.realizePos R t) = S.outerGraph.map R.pos :=
      Graph.map_eq_of_eqOn fun z hz => d.realizePos_of_mem_vertexSet
        (S.outerGraph_le.vertexSet_mono hz)
    rw [hgraph]
    apply Graph.pointSet_congr
    intro f hf
    rw [Graph.edgeSet_map] at hf
    have hfc := S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hf)
    exact d.edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc)
      (d.ne_newEdge₂_of_mem_cells hfc)

/-- An unchanged old edge is outer after subdivision only if it was outer before subdivision. -/
theorem old_notMem_outer {d : S.SubdivData} {f : γ}
    (hfe : f ≠ d.edge) (hnew : f ∉ E(d.outer)) :
    f ∉ E(S.outerGraph) := by
  intro hfO
  by_cases heO : d.edge ∈ E(S.outerGraph)
  · apply hnew
    rw [d.outer_edgeSet_of_mem heO]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hfO, hfe⟩)
  · rw [d.outer_eq heO] at hnew
    exact hnew hfO

/-- If the first half of the subdivided edge is not outer, neither was the original edge. -/
theorem edge_notMem_outer_of_newEdge₁ {d : S.SubdivData}
    (hnew : d.newEdge₁ ∉ E(d.outer)) : d.edge ∉ E(S.outerGraph) := by
  intro heO
  apply hnew
  rw [d.outer_edgeSet_of_mem heO]
  exact Set.mem_insert _ _

/-- If the second half of the subdivided edge is not outer, neither was the original edge. -/
theorem edge_notMem_outer_of_newEdge₂ {d : S.SubdivData}
    (hnew : d.newEdge₂ ∉ E(d.outer)) : d.edge ∉ E(S.outerGraph) := by
  intro heO
  apply hnew
  rw [d.outer_edgeSet_of_mem heO]
  exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

/-- Realizing an interior edge subdivision preserves weak admissibility. -/
theorem isWeaklyAdmissible_realize {d : S.SubdivData} {R : S.Realization}
    {outer dom : Set Plane} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R.IsWeaklyAdmissible outer dom) :
    (d.realize R t ht).IsWeaklyAdmissible outer dom where
  isTwoConnected := by
    have hS2 : S.skel.IsTwoConnected :=
      (Graph.isTwoConnected_map_iff R.injOn_pos).1 hR.isTwoConnected
    have hlr : d.left ≠ d.right := fun h =>
      R.isDrawing.ne_of_isLink (d.isLink.map R.pos) (congrArg R.pos h)
    exact (d.skeleton_isTwoConnected hS2 hlr).map (d.realize R t ht).injOn_pos
  outerSet_eq := (d.outerSet_realize ht).trans hR.outerSet_eq
  isPolygonal := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    change e ∉ E(d.outer) at houter
    rw [d.skeleton_edgeSet] at he
    rcases he with rfl | rfl | ⟨heS, hee⟩
    · exact (d.isArcBetween_newEdge₁ ht).isPolygonal_of_subset_arc
        (R.isDrawing.edge_isArcBetween (d.isLink.map R.pos))
        (hR.isPolygonal d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₁ houter))
        (d.edgeArc_newEdge₁_subset ht)
    · exact (d.isArcBetween_newEdge₂ ht).isPolygonal_of_subset_arc
        (R.isDrawing.edge_isArcBetween (d.isLink.map R.pos))
        (hR.isPolygonal d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₂ houter))
        (d.edgeArc_newEdge₂_subset ht)
    · have hfc := S.mem_cells_of_mem_edgeSet heS
      simp only [CellStructure.SubdivData.realize_drawing]
      rw [d.edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc)
        (d.ne_newEdge₂_of_mem_cells hfc)]
      exact hR.isPolygonal heS (d.old_notMem_outer (by simpa using hee) houter)
  cell_subset := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    change e ∉ E(d.outer) at houter
    rw [d.skeleton_edgeSet] at he
    rcases he with rfl | rfl | ⟨heS, hee⟩
    · exact (d.isRefinement_realize ht).cell_subset_edge (Or.inr (Or.inl rfl)) |>.trans
        (hR.cell_subset d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₁ houter))
    · exact (d.isRefinement_realize ht).cell_subset_edge (Or.inr (Or.inr rfl)) |>.trans
        (hR.cell_subset d.edge_mem_edgeSet (d.edge_notMem_outer_of_newEdge₂ houter))
    · rw [CellStructure.SubdivData.realize_cell,
        d.realizeCell_of_mem_cells (S.mem_cells_of_mem_edgeSet heS)]
      exact hR.cell_subset heS
        (d.old_notMem_outer (by simpa using hee) houter)
  skeletonSet_subset := by
    rw [d.skeletonSet_realize ht]
    exact hR.skeletonSet_subset

end SubdivData

end CellStructure

end Schoenflies

namespace Schoenflies

namespace GeneratedPair

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- Subdivide a generated matched pair at corresponding source and target parameters. -/
noncomputable def subdivide
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (d : P.str.SubdivData) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom where
  str := P.str.subdivideEdge d
  generated := .subdivideEdge P.generated d
  str_combInvariants := d.combInvariants P.str_combInvariants
  str_boundaryCycles := d.boundaryCycles P.str_boundaryCycles P.str_combInvariants
  src := d.realize P.src t ht
  tgt := d.realize P.tgt (d.targetParam P.homeo t) (d.targetParam_mem_Ioo P.homeo ht)
  homeo := d.realizeHomeo P.homeo ht
  src_isCellDecomposition :=
    (d.realize_isCellDecomposition_and_isFaceJordan ht P.str_combInvariants
      P.src_isCellDecomposition P.src_isFaceJordan).1
  tgt_isCellDecomposition :=
    (d.realize_isCellDecomposition_and_isFaceJordan (d.targetParam_mem_Ioo P.homeo ht)
      P.str_combInvariants P.tgt_isCellDecomposition P.tgt_isFaceJordan).1
  src_isFaceJordan :=
    (d.realize_isCellDecomposition_and_isFaceJordan ht P.str_combInvariants
      P.src_isCellDecomposition P.src_isFaceJordan).2.1
  tgt_isFaceJordan :=
    (d.realize_isCellDecomposition_and_isFaceJordan (d.targetParam_mem_Ioo P.homeo ht)
      P.str_combInvariants P.tgt_isCellDecomposition P.tgt_isFaceJordan).2.1
  tgtInterior_isOpen := P.tgtInterior_isOpen
  tgtInterior_frontier_subset := by
    rw [d.skeletonSet_realize (d.targetParam_mem_Ioo P.homeo ht)]
    exact P.tgtInterior_frontier_subset
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(d.skeleton) at he
    rw [d.skeleton_edgeSet] at he
    rcases he with rfl | rfl | ⟨heS, -⟩
    · exact (d.isArcBetween_newEdge₁ (d.targetParam_mem_Ioo P.homeo ht)).isPolygonal_of_subset_arc
        (P.tgt.isDrawing.edge_isArcBetween (d.isLink.map P.tgt.pos))
        (P.tgt_isPolygonal d.edge_mem_edgeSet)
        (d.edgeArc_newEdge₁_subset (d.targetParam_mem_Ioo P.homeo ht))
    · exact (d.isArcBetween_newEdge₂ (d.targetParam_mem_Ioo P.homeo ht)).isPolygonal_of_subset_arc
        (P.tgt.isDrawing.edge_isArcBetween (d.isLink.map P.tgt.pos))
        (P.tgt_isPolygonal d.edge_mem_edgeSet)
        (d.edgeArc_newEdge₂_subset (d.targetParam_mem_Ioo P.homeo ht))
    · have hfc := P.str.mem_cells_of_mem_edgeSet heS
      simp only [CellStructure.SubdivData.realize_drawing]
      rw [d.edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc)
        (d.ne_newEdge₂_of_mem_cells hfc)]
      exact P.tgt_isPolygonal heS
  src_isWeaklyAdmissible := d.isWeaklyAdmissible_realize ht P.src_isWeaklyAdmissible
  tgt_isWeaklyAdmissible := d.isWeaklyAdmissible_realize
    (d.targetParam_mem_Ioo P.homeo ht) P.tgt_isWeaklyAdmissible

/-- The source realization of a subdivided pair is the source subdivision. -/
@[simp] theorem subdivide_src
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (d : P.str.SubdivData) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (P.subdivide d ht).src = d.realize P.src t ht := rfl

/-- The target realization uses the parameter transported by the skeleton homeomorphism. -/
@[simp] theorem subdivide_tgt
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (d : P.str.SubdivData) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (P.subdivide d ht).tgt =
      d.realize P.tgt (d.targetParam P.homeo t) (d.targetParam_mem_Ioo P.homeo ht) := rfl

/-- The output of inserting one source skeleton point into a matched generated pair. -/
structure SubdivideAtData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (p : Plane) where
  /-- The pair after the possible subdivision. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- Subdivision does not change the occupied source skeleton. -/
  skeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- Subdivision does not change the occupied target skeleton. -/
  targetSkeletonSet_eq : pair.tgt.skeletonSet = P.tgt.skeletonSet
  /-- The transported skeleton map is the old map as a point map. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The requested point and every old vertex are vertices of the new source graph. -/
  vertexSet_eq : V(pair.src.graph) = insert p V(P.src.graph)
  /-- The corresponding target point and every old target vertex are vertices as well. -/
  targetVertexSet_eq :
    V(pair.tgt.graph) = insert (P.homeo.toFun p) V(P.tgt.graph)

/-- Every point of the source skeleton can be made a vertex by one matched subdivision. -/
theorem exists_subdivideAtData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {p : Plane}
    (hp : p ∈ P.src.skeletonSet) : Nonempty (SubdivideAtData P p) := by
  classical
  by_cases hpV : p ∈ V(P.src.graph)
  · exact ⟨{
      pair := P
      parent := id
      refines_src := CellStructure.Realization.Refines.refl P.src
      refines_tgt := CellStructure.Realization.Refines.refl P.tgt
      skeletonSet_eq := rfl
      targetSkeletonSet_eq := rfl
      homeo_eqOn := fun _ _ => rfl
      vertexSet_eq := (Set.insert_eq_of_mem hpV).symm
      targetVertexSet_eq := by
        rw [P.src.vertexSet_graph] at hpV
        obtain ⟨a, ha, rfl⟩ := hpV
        rw [P.homeo.pos_apply ha, P.tgt.vertexSet_graph]
        have hmem : P.tgt.pos a ∈ P.tgt.pos '' V(P.str.skel) := ⟨a, ha, rfl⟩
        exact (Set.insert_eq_of_mem hmem).symm
    }⟩
  · rcases hp with hpoldV | hpedge
    · exact absurd hpoldV hpV
    · obtain ⟨e, heR, t, ht, rfl⟩ := Set.mem_iUnion₂.1 hpedge
      have heS : e ∈ E(P.str.skel) := by rwa [P.src.edgeSet_graph] at heR
      obtain ⟨left, right, hlr⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heS
      have ht0 : t ≠ 0 := by
        intro h
        apply hpV
        rw [h]
        exact (P.src.isDrawing.edge_param heR).2.2.left_mem
      have ht1 : t ≠ 1 := by
        intro h
        apply hpV
        rw [h]
        exact (P.src.isDrawing.edge_param heR).2.2.right_mem
      have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      let _ : Finite (Fin 3) := inferInstance
      obtain ⟨fresh, hfresh, havoid⟩ :=
        exists_injective_avoiding P.str.cells P.str.finite_cells (Fin 3)
      have h01 : fresh 0 ≠ fresh 1 := fun h => by
        have := hfresh h
        omega
      have h02 : fresh 0 ≠ fresh 2 := fun h => by
        have := hfresh h
        omega
      have h12 : fresh 1 ≠ fresh 2 := fun h => by
        have := hfresh h
        omega
      obtain ⟨d, hdedge, -, -, -, -, -⟩ :=
        CellStructure.exists_subdivData P.str_boundaryCycles hlr
          (havoid 0) (havoid 1) (havoid 2) h01 h02 h12
      let T := P.subdivide d htIoo
      exact ⟨{
        pair := T
        parent := d.parent
        refines_src :=
          (d.realize_isCellDecomposition_and_isFaceJordan htIoo P.str_combInvariants
            P.src_isCellDecomposition P.src_isFaceJordan).2.2
        refines_tgt :=
          (d.realize_isCellDecomposition_and_isFaceJordan
            (d.targetParam_mem_Ioo P.homeo htIoo) P.str_combInvariants
            P.tgt_isCellDecomposition P.tgt_isFaceJordan).2.2
        skeletonSet_eq := d.skeletonSet_realize htIoo
        targetSkeletonSet_eq :=
          d.skeletonSet_realize (d.targetParam_mem_Ioo P.homeo htIoo)
        homeo_eqOn := fun _ _ => rfl
        vertexSet_eq := by
          change V(d.realizeGraph P.src t) = _
          rw [d.realizeGraph_vertexSet, hdedge]
        targetVertexSet_eq := by
          change V(d.realizeGraph P.tgt (d.targetParam P.homeo t)) = _
          rw [d.realizeGraph_vertexSet,
            d.drawing_targetParam P.homeo (Set.Ioo_subset_Icc_self htIoo), hdedge]
      }⟩

/-- The output of inserting one target skeleton point into a matched generated pair. -/
structure SubdivideTargetAtData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (p : Plane) where
  /-- The pair after the possible subdivision. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- The occupied source skeleton is unchanged. -/
  sourceSkeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- The occupied target skeleton is unchanged. -/
  skeletonSet_eq : pair.tgt.skeletonSet = P.tgt.skeletonSet
  /-- The transported skeleton map agrees with the old one. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The requested point and every old vertex are target vertices of the new pair. -/
  vertexSet_eq : V(pair.tgt.graph) = insert p V(P.tgt.graph)

/-- Every target skeleton point can be made a vertex by one matched subdivision. -/
theorem exists_subdivideTargetAtData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {p : Plane}
    (hp : p ∈ P.tgt.skeletonSet) : Nonempty (SubdivideTargetAtData P p) := by
  let q := P.homeo.invFun p
  have hq : q ∈ P.src.skeletonSet := by
    rw [← P.homeo.symm.image_skeletonSet]
    exact ⟨p, hp, rfl⟩
  obtain ⟨w⟩ := exists_subdivideAtData P hq
  exact ⟨{
    pair := w.pair
    parent := w.parent
    refines_src := w.refines_src
    refines_tgt := w.refines_tgt
    sourceSkeletonSet_eq := w.skeletonSet_eq
    skeletonSet_eq := w.targetSkeletonSet_eq
    homeo_eqOn := w.homeo_eqOn
    vertexSet_eq := by
      rw [w.targetVertexSet_eq, P.homeo.rightInvOn hp]
  }⟩

/-- The output of inserting a finite set of source skeleton points. -/
structure SubdivideSetData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (s : Set Plane) where
  /-- The pair after all subdivisions. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- Subdivision does not change the occupied source skeleton. -/
  skeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- The transported skeleton map agrees with the old one on that unchanged skeleton. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- Every requested point is a vertex of the final source graph. -/
  vertexSet_subset : s ⊆ V(pair.src.graph)

/-- Every finite set of source skeleton points can simultaneously be made vertices. -/
theorem exists_subdivideSetData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {s : Set Plane}
    (hs : s.Finite) (hsub : s ⊆ P.src.skeletonSet) :
    Nonempty (SubdivideSetData P s) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      exact ⟨{
        pair := P
        parent := id
        refines_src := CellStructure.Realization.Refines.refl P.src
        refines_tgt := CellStructure.Realization.Refines.refl P.tgt
        skeletonSet_eq := rfl
        homeo_eqOn := fun _ _ => rfl
        vertexSet_subset := Set.empty_subset _
      }⟩
  | @insert a s ha hs ih =>
      have hskeleton : s ⊆ P.src.skeletonSet := fun x hx =>
        hsub (Set.mem_insert_of_mem a hx)
      obtain ⟨w⟩ := ih hskeleton
      have haSkeleton : a ∈ w.pair.src.skeletonSet := by
        rw [w.skeletonSet_eq]
        exact hsub (Set.mem_insert a s)
      obtain ⟨q⟩ := exists_subdivideAtData w.pair haSkeleton
      exact ⟨{
        pair := q.pair
        parent := w.parent ∘ q.parent
        refines_src := q.refines_src.trans w.refines_src
        refines_tgt := q.refines_tgt.trans w.refines_tgt
        skeletonSet_eq := q.skeletonSet_eq.trans w.skeletonSet_eq
        homeo_eqOn := by
          intro x hx
          calc
            q.pair.homeo.toFun x = w.pair.homeo.toFun x :=
              q.homeo_eqOn (by rwa [w.skeletonSet_eq])
            _ = P.homeo.toFun x := w.homeo_eqOn hx
        vertexSet_subset := by
          intro x hx
          rw [q.vertexSet_eq]
          rcases hx with rfl | hx
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (w.vertexSet_subset hx)
      }⟩

/-- The output of inserting a finite set of target skeleton points. -/
structure SubdivideTargetSetData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (s : Set Plane) where
  /-- The pair after all subdivisions. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite new-to-old cell parent map. -/
  parent : γ → γ
  /-- Source refinement along `parent`. -/
  refines_src : pair.src.Refines P.src parent
  /-- Target refinement along the same `parent`. -/
  refines_tgt : pair.tgt.Refines P.tgt parent
  /-- The occupied source skeleton is unchanged. -/
  sourceSkeletonSet_eq : pair.src.skeletonSet = P.src.skeletonSet
  /-- The occupied target skeleton is unchanged. -/
  skeletonSet_eq : pair.tgt.skeletonSet = P.tgt.skeletonSet
  /-- The final skeleton map agrees with the original one on the original source skeleton. -/
  homeo_eqOn : Set.EqOn pair.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- Every requested point is a vertex of the final target graph. -/
  vertexSet_subset : s ⊆ V(pair.tgt.graph)

/-- Every finite set of target skeleton points can simultaneously be made vertices. -/
theorem exists_subdivideTargetSetData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {s : Set Plane}
    (hs : s.Finite) (hsub : s ⊆ P.tgt.skeletonSet) :
    Nonempty (SubdivideTargetSetData P s) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      exact ⟨{
        pair := P
        parent := id
        refines_src := CellStructure.Realization.Refines.refl P.src
        refines_tgt := CellStructure.Realization.Refines.refl P.tgt
        sourceSkeletonSet_eq := rfl
        skeletonSet_eq := rfl
        homeo_eqOn := fun _ _ => rfl
        vertexSet_subset := Set.empty_subset _
      }⟩
  | @insert a s ha hs ih =>
      have hskeleton : s ⊆ P.tgt.skeletonSet := fun x hx =>
        hsub (Set.mem_insert_of_mem a hx)
      obtain ⟨w⟩ := ih hskeleton
      have haSkeleton : a ∈ w.pair.tgt.skeletonSet := by
        rw [w.skeletonSet_eq]
        exact hsub (Set.mem_insert a s)
      obtain ⟨q⟩ := exists_subdivideTargetAtData w.pair haSkeleton
      exact ⟨{
        pair := q.pair
        parent := w.parent ∘ q.parent
        refines_src := q.refines_src.trans w.refines_src
        refines_tgt := q.refines_tgt.trans w.refines_tgt
        sourceSkeletonSet_eq := q.sourceSkeletonSet_eq.trans w.sourceSkeletonSet_eq
        skeletonSet_eq := q.skeletonSet_eq.trans w.skeletonSet_eq
        homeo_eqOn := by
          intro x hx
          calc
            q.pair.homeo.toFun x = w.pair.homeo.toFun x :=
              q.homeo_eqOn (by rwa [w.sourceSkeletonSet_eq])
            _ = P.homeo.toFun x := w.homeo_eqOn hx
        vertexSet_subset := by
          intro x hx
          rw [q.vertexSet_eq]
          rcases hx with rfl | hx
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (w.vertexSet_subset hx)
      }⟩

end GeneratedPair

end Schoenflies

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- Explicit output data for the common-subdivision construction. -/
structure CommonSubdivisionData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) where
  /-- The part of `H` supported on the old source skeleton. -/
  graph : Graph Plane γ
  /-- The matched pair after inserting every vertex of `graph`. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite parent map from the subdivided pair to `P`. -/
  parent : γ → γ
  /-- The traced graph remains 2-connected. -/
  graph_isTwoConnected : graph.IsTwoConnected
  /-- The traced graph is a subgraph of the given extension. -/
  graph_le : graph ≤ H
  /-- The refined pair realizes the traced graph and contains all of its vertices. -/
  isPartialTransferOf : IsPartialTransferOf pair P graph Hdraw parent

/-- Construct the traced graph, matched subdivided pair, and their composite parent map. -/
noncomputable def commonSubdivisionData [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    CommonSubdivisionData P H Hdraw := by
  classical
  let K := Graph.traceGraph H Hdraw P.src.skeletonSet
  have hKle : K ≤ H := Graph.traceGraph_le _
  let _ : H.Finite := hH.finite
  let _ : K.Finite := Graph.Finite.of_le hKle
  have hK2 : K.IsTwoConnected :=
    trace_isTwoConnected hH P.src_isWeaklyAdmissible.isTwoConnected
  have hvertices : V(K) ⊆ P.src.skeletonSet := by
    intro x hx
    rw [Graph.traceGraph_vertexSet] at hx
    exact hx.2
  let w := Classical.choice (GeneratedPair.exists_subdivideSetData P
    (Graph.finite_vertexSet K) hvertices)
  exact {
    graph := K
    pair := w.pair
    parent := w.parent
    graph_isTwoConnected := hK2
    graph_le := hKle
    isPartialTransferOf := {
      refines_src := w.refines_src
      refines_tgt := w.refines_tgt
      sourceSkeletonSet_subset := by rw [w.skeletonSet_eq]
      homeo_eqOn := w.homeo_eqOn
      skeletonSet_eq := w.skeletonSet_eq.trans (trace_pointSet hH).symm
      vertexSet_subset := w.vertexSet_subset
    }
  }

/-- **Step 1 of finite transfer:** construct the common matched subdivision. -/
theorem commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    CommonSubdivision P H Hdraw := by
  let w := commonSubdivisionData hH
  exact ⟨w.graph, w.pair, w.parent, w.graph_isTwoConnected, w.graph_le,
    w.isPartialTransferOf⟩

/-- Steps 1–3 of finite transfer, with the common subdivision and every ear constructed. -/
theorem transfer_of_ears [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P H Hdraw par :=
  transfer_of_ears_of_commonSubdivision hH (commonSubdivision hH)

/-- **`thm:finite-transfer`, direction (a).** -/
theorem finite_transfer_toward_square [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square_of_commonSubdivision hH (commonSubdivision hH)

end Schoenflies
