/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.InteriorHomeomorphism

/-!
# Boundary anchors retained by the quantitative recursion

Every reverse quantitative stage selects a finite metric net of accessible points on the model
curve.  This module takes their countable union, proves it dense, transports it through the
prescribed boundary homeomorphism, and records the finite-stage witness for every transported
source anchor.

## Blueprint

This discharges `lem:anchor-density` and constructs the `HasAnchorCrosscuts` and `HasSpokes`
inputs used in `prop:boundary-continuity`.
-/

public section

open Filter Metric Set
open scoped Graph

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-- An admissible realization of the closed Jordan domain is exactly a finite stage in the
form consumed by the skeleton-crosscut theorem. -/
theorem CellStructure.Realization.IsAdmissible.isStageOn
    {S : CellStructure γ} {R : S.Realization}
    (h : R.IsAdmissible C (C ∪ inside C)) :
    Graph.IsStageOn R.graph R.drawing C (inside C) where
  isDrawing := R.isDrawing
  polygonal := by
    intro e he hnonboundary
    have heSkel : e ∈ E(S.skel) := by rwa [R.edgeSet_graph] at he
    apply h.isPolygonal heSkel
    intro heOuter
    apply hnonboundary
    have heOuterMap : e ∈ E(S.outerGraph.map R.pos) := by
      rw [Graph.edgeSet_map]
      exact heOuter
    rw [← h.outerSet_eq]
    exact Graph.edgeArc_subset_pointSet heOuterMap
  disjoint := Set.disjoint_left.2 fun x hxC hxInside => inside_subset_compl hxInside hxC
  vertex_mem := by
    intro x hxV hxC
    have hxDom : x ∈ C ∪ inside C := h.skeletonSet_subset
      (Graph.vertexSet_subset_pointSet hxV)
    exact hxDom.resolve_left hxC
  edge_split := by
    intro e x y hlink
    have heSkel : e ∈ E(S.skel) := by
      rw [← R.edgeSet_graph]
      exact hlink.edge_mem
    by_cases heOuter : e ∈ E(S.outerGraph)
    · have heOuterMap : e ∈ E(S.outerGraph.map R.pos) := by
        rw [Graph.edgeSet_map]
        exact heOuter
      rw [← h.outerSet_eq]
      exact Or.inl (Graph.edgeArc_subset_pointSet heOuterMap)
    · right
      obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet heSkel
      have hcell := h.cell_subset heSkel heOuter
      rw [R.cell_edge hab, union_inside_sdiff] at hcell
      rcases hlink.eq_and_eq_or_eq_and_eq (hab.map R.pos) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcell
      · simpa only [Set.pair_comm] using hcell
  isConnected_diff := by
    rw [← h.outerSet_eq]
    exact h.isConnected_nonboundary

/-- A vertex approached by points of the graph off `C` is incident with an edge not contained
in `C`.  A sufficiently small vertex square excludes every other vertex and every nonincident
edge. -/
theorem Graph.IsDrawing.exists_nonboundary_incident_of_mem_closure
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane} [G.Finite]
    (h : G.IsDrawing drawing) {c : Plane} (hcV : c ∈ V(G)) (hcC : c ∈ C)
  (hclosure : c ∈ closure (Graph.pointSet G drawing \ C)) :
    ∃ e, G.Inc e c ∧ Graph.Nonboundary drawing C e := by
  obtain ⟨r, hr, hvert, hedge⟩ := h.exists_square_at hcV
  obtain ⟨z, hzOpen, hzGraph, hzC⟩ := mem_closure_iff.1 hclosure
    (Plane.openSquare c r) (Plane.isOpen_openSquare c r) (Plane.mem_openSquare_self hr)
  have hzClosed : z ∈ Plane.closedSquare c r :=
    Plane.openSquare_subset_closedSquare c r hzOpen
  rcases hzGraph with hzV | hzE
  · have hzc : z = c := by
      by_contra hne
      exact hvert z hzV hne hzClosed
    exact absurd hcC (hzc ▸ hzC)
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
    have hinc : G.Inc e c := by
      by_contra hninc
      exact Set.disjoint_left.1 (hedge e he hninc) hzClosed hze
    exact ⟨e, hinc, fun hsub => hzC (hsub hze)⟩

/-- The set-level interior part of a finite stage is the point set of the trace subgraph whose
support is the open region. -/
theorem Graph.pointSet_traceGraph_eq_interiorPart
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane}
    (h : G.IsDrawing drawing) (D : Set Plane) :
    Graph.pointSet (Graph.traceGraph G drawing D) drawing =
      Graph.interiorPart G drawing D := by
  apply Set.Subset.antisymm
  · rintro z (hzV | hzE)
    · exact Or.inl hzV
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
      obtain ⟨x, y, hxy⟩ :=
        (Graph.traceGraph G drawing D).exists_isLink_of_mem_edgeSet he
      have ht := (Graph.traceGraph_isLink D).1 hxy
      exact Or.inr (Set.mem_iUnion₂.2 ⟨e, ⟨ht.2.1.edge_mem, ht.1⟩, hze⟩)
  · rintro z (hzV | hzE)
    · exact Or.inl hzV
    · obtain ⟨e, ⟨he, heD⟩, hze⟩ := Set.mem_iUnion₂.1 hzE
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      have harc := h.edge_isArcBetween hxy
      apply Or.inr
      exact Set.mem_iUnion₂.2 ⟨e, by
        rw [Graph.edgeSet_eq_setOfPred_exists_isLink]
        exact ⟨x, y, (Graph.traceGraph_isLink D).2
          ⟨heD, hxy, heD harc.left_mem, heD harc.right_mem⟩⟩, hze⟩

/-- A nonempty walk is polygonal when the edge arcs actually used by that walk are polygonal;
no condition on unused (and possibly wild outer) edges is needed. -/
theorem Graph.IsDrawing.isPolygonal_edgesCover_of_mem
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane}
    (h : G.IsDrawing drawing) {a b : Plane} {W : List γ}
    (hW : G.IsWalk a W b) (hne : W ≠ [])
    (hpoly : ∀ e ∈ W, IsPolygonal (Graph.edgeArc drawing e)) :
    IsPolygonal (Graph.edgesCover drawing W) := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons a c b e W hlink hW ih =>
      rcases eq_or_ne W [] with rfl | hWne
      · simpa using hpoly e (List.mem_cons_self ..)
      · rw [Graph.edgesCover_cons]
        exact (hpoly e (List.mem_cons_self ..)).union
          (ih hWne fun f hf => hpoly f (List.mem_cons_of_mem e hf))
          ⟨c, (h.edge_isArcBetween hlink).right_mem,
            hW.left_mem_edgesCover h hWne⟩

/-- A walk in an injectively mapped graph lifts to a walk in the original graph, starting at
the prescribed preimage vertex. -/
theorem Graph.IsWalk.exists_lift_map
    {α α' β : Type*} {G : Graph α β} {f : α → α'}
    (hf : Set.InjOn f V(G)) {u : α} (hu : u ∈ V(G))
    {W : List β} {y : α'} (h : (G.map f).IsWalk (f u) W y) :
    ∃ v : α, G.IsWalk u W v ∧ f v = y := by
  induction W generalizing u y with
  | nil =>
      have hy : f u = y := h.eq_of_nil
      exact ⟨u, Graph.IsWalk.nil hu, hy⟩
  | cons e W ih =>
      cases h with
      | @cons _ w _ _ _ hlink htail =>
          obtain ⟨u₀, w₀, hlink₀, hu₀, hw₀⟩ := hlink
          have huu₀ : u₀ = u := hf hlink₀.left_mem hu hu₀
          subst u₀
          subst w
          obtain ⟨v, hv, hfv⟩ := ih hlink₀.right_mem htail
          exact ⟨v, Graph.IsWalk.cons hlink₀ hv, hfv⟩

/-- The corresponding lifting statement for a simple path. -/
theorem Graph.IsPath.exists_lift_map
    {α α' β : Type*} {G : Graph α β} {f : α → α'}
    (hf : Set.InjOn f V(G)) {u : α} (hu : u ∈ V(G))
    {W : List β} {y : α'} (h : (G.map f).IsPath (f u) W y) :
    ∃ v : α, G.IsPath u W v ∧ f v = y := by
  induction W generalizing u y with
  | nil =>
      have hy : f u = y := h.isWalk.eq_of_nil
      exact ⟨u, Graph.IsPath.nil hu, hy⟩
  | cons e W ih =>
      cases h with
      | @cons _ w _ _ _ hlink htail hfresh =>
          obtain ⟨u₀, w₀, hlink₀, hu₀, hw₀⟩ := hlink
          have huu₀ : u₀ = u := hf hlink₀.left_mem hu hu₀
          subst u₀
          subst w
          obtain ⟨v, hv, hfv⟩ := ih hlink₀.right_mem htail
          refine ⟨v, Graph.IsPath.cons hlink₀ hv ?_, hfv⟩
          intro huTail
          apply hfresh
          rw [Graph.walkVertices_map]
          exact ⟨u, huTail, rfl⟩

/-- A skeleton homeomorphism carries the union of any finite list of corresponding edges onto
the union of the same edge list in the target realization. -/
theorem CellStructure.SkeletonHomeo.image_edgesCover
    {S : CellStructure γ} {R₁ R₂ : S.Realization}
    (g : CellStructure.SkeletonHomeo R₁ R₂) {W : List γ}
    (hW : ∀ e ∈ W, e ∈ E(S.skel)) :
    g.toFun '' Graph.edgesCover R₁.drawing W = Graph.edgesCover R₂.drawing W := by
  induction W with
  | nil => simp
  | cons e W ih =>
      rw [Graph.edgesCover_cons, Graph.edgesCover_cons, Set.image_union,
        g.edgeArc_image (hW e (List.mem_cons_self ..)),
        ih (fun f hf => hW f (List.mem_cons_of_mem e hf))]

/-- Strengthened skeleton-crosscut extraction: the crosscut is the carrier of a simple graph
path all of whose edges are nonboundary.  This edge-list form can be transported to a matched
realization edge by edge. -/
theorem Graph.IsStageOn.exists_crosscut_path
    {G : Graph Plane γ} {drawing : γ → ℝ → Plane} [G.Finite]
    (h : G.IsStageOn drawing C (inside C)) (hC : IsJordanCurve C)
    {a b : Plane} (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : ∃ e, G.Inc e a ∧ Graph.Nonboundary drawing C e)
    (hb : ∃ e, G.Inc e b ∧ Graph.Nonboundary drawing C e) :
    ∃ W : List γ, G.IsPath a W b ∧
      (∀ e ∈ W, Graph.Nonboundary drawing C e) ∧
      IsCrosscut C (Graph.edgesCover drawing W) a b := by
  classical
  by_cases hbig : ∃ (e : γ) (x y : Plane),
      G.IsLink e x y ∧ Graph.Nonboundary drawing C e ∧ x ∈ C ∧ y ∈ C
  · obtain ⟨e, x, y, hlink, hnonboundary, hxC, hyC⟩ := hbig
    have hlab : G.IsLink e a b :=
      h.isLink_of_ends_mem hlink hnonboundary hxC hyC hab ha hb
    have hpath : G.IsPath a [e] b := Graph.IsPath.single hlab hab
    have hpoly : IsPolygonal (Graph.edgesCover drawing [e]) := by
      rw [Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty]
      exact h.polygonal hlab.edge_mem hnonboundary
    have hinter : Graph.edgesCover drawing [e] \ {a, b} ⊆ inside C := by
      rw [Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty]
      rcases h.edge_split hlab with houter | hinter
      · exact absurd houter hnonboundary
      · exact hinter
    exact ⟨[e], hpath, fun f hf => by
        have hfe : f = e := by simpa using hf
        subst f
        exact hnonboundary,
      ⟨hC, h.isDrawing.path_isArcBetween hpath (by simp), hpoly,
        haC, hbC, hinter⟩⟩
  · have hcase : ∀ ⦃e : γ⦄ ⦃x y : Plane⦄, G.IsLink e x y →
        Graph.Nonboundary drawing C e → x ∈ C → y ∉ C :=
      fun e x y hlink hnonboundary hxC hyC =>
        hbig ⟨e, x, y, hlink, hnonboundary, hxC, hyC⟩
    obtain ⟨ea, ⟨ya, hla⟩, hanb⟩ := ha
    obtain ⟨eb, ⟨yb, hlb⟩, hbnb⟩ := hb
    have hyaD : ya ∈ inside C :=
      h.vertex_mem hla.right_mem (hcase hla hanb haC)
    have hybD : yb ∈ inside C :=
      h.vertex_mem hlb.right_mem (hcase hlb hbnb hbC)
    let K := Graph.traceGraph G drawing (inside C)
    have hKle : K ≤ G := Graph.traceGraph_le _
    let _ : K.Finite := Graph.Finite.of_le hKle
    have hKpoint : Graph.pointSet K drawing =
        Graph.interiorPart G drawing (inside C) :=
      Graph.pointSet_traceGraph_eq_interiorPart h.isDrawing (inside C)
    have hyaK : ya ∈ V(K) := by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hla.right_mem, hyaD⟩
    have hybK : yb ∈ V(K) := by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hlb.right_mem, hybD⟩
    have hKconn : K.Connected := Graph.connected_of_isPreconnected_pointSet
      (h.isDrawing.mono hKle)
      (hKpoint.symm ▸ h.isPreconnected_interiorPart hcase) ⟨ya, hyaK⟩
    obtain ⟨W, hWK⟩ := hKconn.exists_isPath hyaK hybK
    have hWG : G.IsPath ya W yb := hWK.mono hKle
    have hybne : yb ≠ b := fun heq =>
      h.notMem_of_mem_curve hbC (heq ▸ hybD)
    have hlast : G.IsPath yb [eb] b := Graph.IsPath.single hlb.symm hybne
    have htail : G.IsPath ya (W ++ [eb]) b := by
      apply hWG.append hlast
      intro y hyW hyLast
      have hyK : y ∈ V(K) := by
        rw [Graph.walkVertices_congr_of_le hKle
          (fun e he => hWK.edge_mem he)] at hyW
        exact Graph.walkVertices_subset_vertexSet hWK.left_mem hyW
      have hyD : y ∈ inside C := by
        rw [Graph.traceGraph_vertexSet] at hyK
        exact hyK.2
      rcases Graph.mem_walkVertices_iff.1 hyLast with rfl | hyCovered
      · rfl
      · obtain ⟨e, he, hinc⟩ := hyCovered
        have heq : e = eb := by simpa using he
        subst e
        rcases hinc.eq_or_eq_of_isLink hlb with rfl | rfl
        · exact absurd hbC (h.notMem_curve hyD)
        · rfl
    have hafresh : a ∉ G.walkVertices ya (W ++ [eb]) := by
      intro haTail
      rcases Graph.mem_walkVertices_iff.1 haTail with haya | haCovered
      · exact h.notMem_of_mem_curve haC (haya ▸ hyaD)
      · rw [Graph.coveredVertices_append] at haCovered
        rcases haCovered with haW | haeb
        · have haK : a ∈ V(K) := by
            have hcoverEq : G.coveredVertices W = K.coveredVertices W :=
              Graph.coveredVertices_congr_of_le hKle (fun e he => hWK.edge_mem he)
            exact Graph.coveredVertices_subset_vertexSet (hcoverEq ▸ haW)
          rw [Graph.traceGraph_vertexSet] at haK
          exact h.notMem_of_mem_curve haC haK.2
        · obtain ⟨e, he, hinc⟩ := haeb
          have heq : e = eb := by simpa using he
          subst e
          rcases hinc.eq_or_eq_of_isLink hlb with heq | heq
          · exact hab heq
          · exact h.notMem_of_mem_curve haC (heq ▸ hybD)
    let Wfull := ea :: (W ++ [eb])
    have hfull : G.IsPath a Wfull b := Graph.IsPath.cons hla htail hafresh
    have hfullne : Wfull ≠ [] := List.cons_ne_nil _ _
    have hWnonboundary : ∀ e ∈ Wfull, Graph.Nonboundary drawing C e := by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hanb
      rcases List.mem_append.1 he with heW | heLast
      · have heK := hWK.edge_mem heW
        obtain ⟨x, y, hxyK⟩ := K.exists_isLink_of_mem_edgeSet heK
        have ht := (Graph.traceGraph_isLink (inside C)).1 hxyK
        intro houter
        have hxArc := (h.isDrawing.edge_isArcBetween ht.2.1).left_mem
        exact h.notMem_of_mem_curve (houter hxArc) (ht.1 hxArc)
      · have heq : e = eb := by simpa using heLast
        exact heq ▸ hbnb
    have hpoly : IsPolygonal (Graph.edgesCover drawing Wfull) :=
      Graph.IsDrawing.isPolygonal_edgesCover_of_mem h.isDrawing hfull.isWalk hfullne
        (fun e he => h.polygonal (hfull.edge_mem he) (hWnonboundary e he))
    have hinter : Graph.edgesCover drawing Wfull \ {a, b} ⊆ inside C := by
      rintro z ⟨hzCover, hzab⟩
      apply h.pointSet_diff_subset
      refine ⟨Graph.edgesCover_subset_pointSet
        (fun e he => hfull.edge_mem he) hzCover, fun hzC => ?_⟩
      obtain ⟨e, he, hze⟩ := Graph.mem_edgesCover_iff.1 hzCover
      rcases List.mem_cons.1 he with rfl | he
      · rcases h.edgeArc_inter_curve hla hanb ⟨hze, hzC⟩ with rfl | rfl
        · exact hzab (Or.inl rfl)
        · exact h.notMem_of_mem_curve hzC hyaD
      · rcases List.mem_append.1 he with heW | heLast
        · have heK := hWK.edge_mem heW
          obtain ⟨x, y, hxyK⟩ := K.exists_isLink_of_mem_edgeSet heK
          have ht := (Graph.traceGraph_isLink (inside C)).1 hxyK
          exact h.notMem_of_mem_curve hzC (ht.1 hze)
        · have heq : e = eb := by simpa using heLast
          subst e
          rcases h.edgeArc_inter_curve hlb hbnb ⟨hze, hzC⟩ with rfl | rfl
          · exact hzab (Or.inr rfl)
          · exact h.notMem_of_mem_curve hzC hybD
    exact ⟨Wfull, hfull, hWnonboundary,
      ⟨hC, h.isDrawing.path_isArcBetween hfull hfullne, hpoly,
        haC, hbC, hinter⟩⟩

/-- Every radial half-spoke has arbitrarily small connected tails accumulating at its missing
outer endpoint. -/
theorem exists_halfSpoke_tail {N : ℕ} (hN : 2 ≤ N) (z : Plane)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ A : Set Plane, A ⊆ halfSpoke N z ∧ IsPreconnected A ∧ A ⊆ ball z delta ∧
      z ∈ closure A := by
  let f : ℝ → Plane := fun t => t • z
  have hf : Continuous f := continuous_id.smul continuous_const
  obtain ⟨kappa, hkappa, hclose⟩ :=
    Metric.continuousAt_iff.1 hf.continuousAt delta hdelta
  let mu : ℝ := min ((1 - (N : ℝ)⁻¹) / 2) (kappa / 2)
  have hinv : (N : ℝ)⁻¹ < 1 := inv_cast_lt_one hN
  have hmu : 0 < mu := by
    apply lt_min
    · linarith
    · linarith
  have hmugap : mu ≤ (1 - (N : ℝ)⁻¹) / 2 := min_le_left _ _
  have hmukappa : mu ≤ kappa / 2 := min_le_right _ _
  let a : ℝ := 1 - mu
  have ha : a < 1 := by simp only [a]; linarith
  have hinva : (N : ℝ)⁻¹ ≤ a := by simp only [a]; linarith
  refine ⟨f '' Ico a 1, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨t, ht, rfl⟩
    exact smul_mem_halfSpoke (hinva.trans ht.1) ht.2 z
  · exact ((isConnected_Ico ha).image f hf.continuousOn).isPreconnected
  · rintro y ⟨t, ht, rfl⟩
    rw [mem_ball]
    have htmu : 1 - t ≤ mu := by
      have := ht.1
      simp only [a] at this
      linarith
    have htkappa : dist t 1 < kappa := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
      linarith
    simpa only [f, one_smul] using hclose htkappa
  · have h1cl : (1 : ℝ) ∈ closure (Ico a 1) := by
      rw [closure_Ico ha.ne]
      exact ⟨ha.le, le_rfl⟩
    have hclosure := mem_closure_image hf.continuousAt h1cl
    simpa only [f, one_smul] using hclosure

/-- All target-boundary points selected as fresh spoke endpoints by some reverse stage. -/
def quantitativeFreshTargetSet [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) : Set Plane :=
  {z | ∃ n, z ∈ (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.fresh}

theorem quantitativeFreshTargetSet_subset [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) :
    quantitativeFreshTargetSet P₀ hC hcycle q ⊆ modelCurve := by
  rintro z ⟨n, hn⟩
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.fresh_mem z hn

/-- The radial half-spoke attached to a fresh target anchor at successor `n` is retained by
the target skeleton of the complete two-sided successor. -/
theorem quantitativeFresh_halfSpoke_subset_targetSkeleton [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) {n : ℕ} {z : Plane}
    (hz : z ∈ (scheduledQuantitativeSuccessor hC hcycle q n
      (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.fresh) :
    halfSpoke (meshCount ((scheduledQuantitativeSuccessor hC hcycle q n
      (quantitativeStage P₀ hC hcycle q n)).reverse.overlay.delta)) z ⊆
      (quantitativeStage P₀ hC hcycle q (n + 1)).tgt.skeletonSet := by
  let w := scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)
  rw [quantitativeStage_succ]
  change halfSpoke (meshCount w.reverse.overlay.delta) z ⊆ w.pair.tgt.skeletonSet
  intro y hy
  apply w.forward.transition.targetSkeletonSet_subset
  have hyMesh : y ∈ Graph.pointSet
      (squareMesh w.reverse.overlay.delta w.reverse.overlay.fresh (q.anchors n))
      segmentDrawing := by
    rw [squareMesh_pointSet]
    exact spokePiece_seg_subset_cover (two_le_meshCount w.reverse.overlay.delta) hz
      (halfSpoke_subset (two_le_meshCount w.reverse.overlay.delta) z hy)
  have hyOverlay := w.reverse.cover.squareMesh_subset_meshOverlay
    w.reverse.overlay.delta w.reverse.overlay.fresh (q.anchors n) hyMesh
  rw [w.reverse.overlay.transfer.skeletonSet_eq, Graph.pointSet_relabelEdges]
  exact hyOverlay

/-- The selected target anchors are dense on the model curve. -/
theorem quantitativeFreshTargetSet_dense [Infinite γ]
    (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (q : QuantitativeSchedule C) :
    modelCurve ⊆ closure (quantitativeFreshTargetSet P₀ hC hcycle q) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 tendsto_dyadicTargetBound η hη
  let w := scheduledQuantitativeSuccessor hC hcycle q N
    (quantitativeStage P₀ hC hcycle q N)
  obtain ⟨z, hz, hxz⟩ := w.reverse.overlay.fresh_net x hx
  have hboundDist := hN N le_rfl
  have hbound : dyadicTargetBound N < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (dyadicTargetBound_pos N)] at hboundDist
    exact hboundDist
  exact ⟨z, ⟨N, hz⟩,
    lt_trans hxz (lt_trans w.reverse.delta_lt_half_bound (by linarith))⟩

variable {u v : Plane → Plane} (hC : IsJordanCurve C)
  (hu : IsHomeoOn u v C modelCurve)

/-- The target anchor set for the recursion started with the prescribed boundary map. -/
noncomputable def prescribedTargetAnchorSet : Set Plane :=
  let hsep := jordan_curve_theorem hC
  quantitativeFreshTargetSet
    (prescribedAnchoredInitialData hC u v hu).generatedPair hsep
      outerEdgesFormCycle_initialStructure (denseQuantitativeSchedule hsep)

/-- The corresponding source anchors, transported by the prescribed boundary inverse. -/
noncomputable def prescribedSourceAnchorSet : Set Plane :=
  v '' prescribedTargetAnchorSet hC hu

theorem prescribedTargetAnchorSet_subset :
    prescribedTargetAnchorSet hC hu ⊆ modelCurve := by
  exact quantitativeFreshTargetSet_subset
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC))

theorem prescribedTargetAnchorSet_dense :
    modelCurve ⊆ closure (prescribedTargetAnchorSet hC hu) := by
  exact quantitativeFreshTargetSet_dense
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC))

theorem prescribedSourceAnchorSet_subset :
    prescribedSourceAnchorSet hC hu ⊆ C := by
  rintro x ⟨z, hz, rfl⟩
  exact hu.mapsTo_inv (prescribedTargetAnchorSet_subset hC hu hz)

/-- Density pulls back through the inverse side of a relative homeomorphism. -/
theorem IsHomeoOn.subset_closure_image_inv
    {f g : Plane → Plane} {s t A : Set Plane}
    (h : IsHomeoOn f g s t) (hA : A ⊆ t) (hdense : t ⊆ closure A) :
    s ⊆ closure (g '' A) := by
  intro x hx
  have hfx : f x ∈ t := h.mapsTo hx
  have hcont : ContinuousWithinAt g A (f x) :=
    (h.continuousOn_inv (f x) hfx).mono hA
  have hcl : g (f x) ∈ closure (g '' A) :=
    hcont.mem_closure_image (hdense hfx)
  rwa [h.invOn.1 hx] at hcl

/- Density transports back through the prescribed boundary homeomorphism. -/
theorem prescribedSourceAnchorSet_dense :
    C ⊆ closure (prescribedSourceAnchorSet hC hu) := by
  exact IsHomeoOn.subset_closure_image_inv hu
    (prescribedTargetAnchorSet_subset hC hu)
    (prescribedTargetAnchorSet_dense hC hu)

/-- Every stage skeleton homeomorphism still agrees with the prescribed boundary map. -/
theorem prescribedJordanStage_homeo_eq_boundary (n : ℕ) :
    EqOn ((prescribedJordanStageSequence hC u v hu).stage n).homeo.toFun u C := by
  intro x hx
  let T := prescribedJordanStageSequence hC u v hu
  have hxouter : x ∈ (T.stage n).src.outerSet := by
    rw [(T.stage n).src_isWeaklyAdmissible.outerSet_eq]
    exact hx
  have hxskel : x ∈ (T.stage n).src.skeletonSet :=
    (T.stage n).src.outerSet_subset_skeletonSet hxouter
  exact (T.F_eq_skelHomeo hxskel (Or.inl hx)).symm.trans
    (prescribedJordanStageSequence_F_eq_boundary hC u v hu hx)

/-- On the model curve, the inverse of every finite-stage skeleton map is the prescribed
boundary inverse. -/
theorem prescribedJordanStage_invFun_eq_boundaryInv (n : ℕ) {z : Plane}
    (hz : z ∈ modelCurve) :
    ((prescribedJordanStageSequence hC u v hu).stage n).homeo.invFun z = v z := by
  let T := prescribedJordanStageSequence hC u v hu
  let x := (T.stage n).homeo.invFun z
  have hzouter : z ∈ (T.stage n).tgt.outerSet := by
    rw [(T.stage n).tgt_isWeaklyAdmissible.outerSet_eq]
    exact hz
  have hzskel : z ∈ (T.stage n).tgt.skeletonSet :=
    (T.stage n).tgt.outerSet_subset_skeletonSet hzouter
  have hxouter : x ∈ (T.stage n).src.outerSet := by
    rw [← (T.stage n).homeo.symm.image_outerSet]
    exact ⟨z, hzouter, rfl⟩
  have hxC : x ∈ C := by
    rw [(T.stage n).src_isWeaklyAdmissible.outerSet_eq] at hxouter
    exact hxouter
  apply hu.injOn hxC (hu.mapsTo_inv hz)
  calc
    u x = (T.stage n).homeo.toFun x :=
      (prescribedJordanStage_homeo_eq_boundary hC hu n hxC).symm
    _ = z := (T.stage n).homeo.rightInvOn hzskel
    _ = u (v z) := (hu.invOn.2 hz).symm

/-- Every noninitial prescribed stage is source-admissible; it is the output of the forward
half of the preceding quantitative successor. -/
theorem prescribedJordanStage_succ_src_isAdmissible (n : ℕ) :
    ((prescribedJordanStageSequence hC u v hu).stage (n + 1)).src.IsAdmissible
      C (C ∪ inside C) := by
  change (quantitativeStage
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) (n + 1)).src.IsAdmissible
      C (C ∪ inside C)
  rw [quantitativeStage_succ]
  exact (scheduledQuantitativeSuccessor
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) n
    (quantitativeStage
      (prescribedAnchoredInitialData hC u v hu).generatedPair
      (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC)) n)).forward.forward.src_isAdmissible

/-- Each transported source anchor comes with the reverse stage at which it was selected and
the exact finite-stage source endpoint realizing it. -/
theorem prescribedSourceAnchorSet_stageWitness {c : Plane}
    (hc : c ∈ prescribedSourceAnchorSet hC hu) :
    ∃ n z, z ∈ (scheduledQuantitativeSuccessor
        (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
        (denseQuantitativeSchedule (jordan_curve_theorem hC)) n
        ((prescribedJordanStageSequence hC u v hu).stage n)).reverse.overlay.fresh ∧
      c = v z ∧
      ((prescribedJordanStageSequence hC u v hu).stage n).homeo.invFun z = c := by
  obtain ⟨z, hz, rfl⟩ := hc
  obtain ⟨n, hn⟩ := hz
  refine ⟨n, z, hn, rfl, ?_⟩
  apply prescribedJordanStage_invFun_eq_boundaryInv hC hu n
  exact prescribedTargetAnchorSet_subset hC hu ⟨n, hn⟩

/-- Every selected source anchor is approached by the open nonboundary part of one finite-stage
skeleton.  This retains precisely the finite combinatorial germ needed to find an incident
nonboundary edge after making the anchor a vertex. -/
theorem prescribedSourceAnchorSet_stageClosure {c : Plane}
    (hc : c ∈ prescribedSourceAnchorSet hC hu) :
    ∃ n, c ∈ closure
      (((prescribedJordanStageSequence hC u v hu).stage (n + 1)).src.skeletonSet \ C) := by
  obtain ⟨n, z, hz, hcz, -⟩ := prescribedSourceAnchorSet_stageWitness hC hu hc
  let T := prescribedJordanStageSequence hC u v hu
  let w := scheduledQuantitativeSuccessor
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) n (T.stage n)
  change z ∈ w.reverse.overlay.fresh at hz
  have hzCurve : z ∈ modelCurve := w.reverse.overlay.fresh_mem z hz
  have hhalf : halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (T.stage (n + 1)).tgt.skeletonSet := by
    change halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (quantitativeStage
        (prescribedAnchoredInitialData hC u v hu).generatedPair
        (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
        (denseQuantitativeSchedule (jordan_curve_theorem hC)) (n + 1)).tgt.skeletonSet
    exact quantitativeFresh_halfSpoke_subset_targetSkeleton
      (prescribedAnchoredInitialData hC u v hu).generatedPair
      (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC)) hz
  have hzSkel : z ∈ (T.stage (n + 1)).tgt.skeletonSet := by
    have hzOuter : z ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [(T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hzCurve
    exact (T.stage (n + 1)).tgt.outerSet_subset_skeletonSet hzOuter
  obtain ⟨A, hAhalf, -, -, hzA⟩ := exists_halfSpoke_tail
    (two_le_meshCount w.reverse.overlay.delta) z one_pos
  have hzHalf : z ∈ closure (halfSpoke (meshCount w.reverse.overlay.delta) z) :=
    closure_mono hAhalf hzA
  have hInvImage : (T.stage (n + 1)).homeo.invFun ''
      halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
        (T.stage (n + 1)).src.skeletonSet \ C := by
    rintro x ⟨y, hyHalf, rfl⟩
    have hySkel : y ∈ (T.stage (n + 1)).tgt.skeletonSet := hhalf hyHalf
    have hxSkel : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.skeletonSet := by
      rw [← (T.stage (n + 1)).homeo.symm.image_skeletonSet]
      exact ⟨y, hySkel, rfl⟩
    refine ⟨hxSkel, fun hxC => ?_⟩
    have hxOuter : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.outerSet := by
      rw [(T.stage (n + 1)).src_isWeaklyAdmissible.outerSet_eq]
      exact hxC
    have hyOuter : y ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [← (T.stage (n + 1)).homeo.image_outerSet]
      exact ⟨(T.stage (n + 1)).homeo.invFun y, hxOuter,
        (T.stage (n + 1)).homeo.rightInvOn hySkel⟩
    have hyCurve : y ∈ modelCurve := by
      rw [← (T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hyOuter
    exact halfSpoke_disjoint_modelCurve
      (two_le_meshCount w.reverse.overlay.delta) hzCurve y hyHalf hyCurve
  have hInvClosure : (T.stage (n + 1)).homeo.invFun z ∈ closure
      ((T.stage (n + 1)).homeo.invFun ''
        halfSpoke (meshCount w.reverse.overlay.delta) z) := by
    have hcont :=
      ((T.stage (n + 1)).homeo.continuousOn_invFun z hzSkel).mono hhalf
    exact ContinuousWithinAt.mem_closure_image hcont hzHalf
  refine ⟨n, ?_⟩
  have hcInv : (T.stage (n + 1)).homeo.invFun z = c := by
    rw [prescribedJordanStage_invFun_eq_boundaryInv hC hu (n + 1) hzCurve, ← hcz]
  rw [← hcInv]
  exact closure_mono hInvImage hInvClosure

/-- The dense prescribed anchor set has the spoke germs required by boundary continuity.  A
fresh radial target segment is already present at the reverse half-stage; target-skeleton
monotonicity retains it through the following forward refinement, and the finite-stage inverse
transports an arbitrarily short tail into the Jordan domain. -/
theorem prescribedSourceAnchorSet_hasSpokes :
    HasSpokes C (prescribedSourceAnchorSet hC hu) u
      (prescribedJordanStageSequence hC u v hu).limitTower.F := by
  intro c hc epsilon hepsilon
  obtain ⟨n, z, hz, hcz, -⟩ := prescribedSourceAnchorSet_stageWitness hC hu hc
  let T := prescribedJordanStageSequence hC u v hu
  let w := scheduledQuantitativeSuccessor
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
    (denseQuantitativeSchedule (jordan_curve_theorem hC)) n (T.stage n)
  change z ∈ w.reverse.overlay.fresh at hz
  have hzCurve : z ∈ modelCurve := w.reverse.overlay.fresh_mem z hz
  have hhalf : halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (T.stage (n + 1)).tgt.skeletonSet := by
    change halfSpoke (meshCount w.reverse.overlay.delta) z ⊆
      (quantitativeStage
        (prescribedAnchoredInitialData hC u v hu).generatedPair
        (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
        (denseQuantitativeSchedule (jordan_curve_theorem hC)) (n + 1)).tgt.skeletonSet
    exact quantitativeFresh_halfSpoke_subset_targetSkeleton
      (prescribedAnchoredInitialData hC u v hu).generatedPair
      (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      (denseQuantitativeSchedule (jordan_curve_theorem hC)) hz
  have hzSkel : z ∈ (T.stage (n + 1)).tgt.skeletonSet := by
    have hzOuter : z ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [(T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hzCurve
    exact (T.stage (n + 1)).tgt.outerSet_subset_skeletonSet hzOuter
  obtain ⟨delta, hdelta, hclose⟩ := Metric.continuousWithinAt_iff.1
    ((T.stage (n + 1)).homeo.continuousOn_invFun z hzSkel) epsilon hepsilon
  obtain ⟨A, hAhalf, hAconn, hAball, hzcl⟩ :=
    exists_halfSpoke_tail (two_le_meshCount w.reverse.overlay.delta) z hdelta
  have hAskel : A ⊆ (T.stage (n + 1)).tgt.skeletonSet := hAhalf.trans hhalf
  let J : Set Plane := (T.stage (n + 1)).homeo.invFun '' A
  have hJinside : J ⊆ inside C := by
    rintro x ⟨y, hyA, rfl⟩
    have hySkel : y ∈ (T.stage (n + 1)).tgt.skeletonSet := hAskel hyA
    have hxSkel : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.skeletonSet := by
      rw [← (T.stage (n + 1)).homeo.symm.image_skeletonSet]
      exact ⟨y, hySkel, rfl⟩
    have hxDom : (T.stage (n + 1)).homeo.invFun y ∈ C ∪ inside C :=
      (T.stage (n + 1)).src_isCellDecomposition.skeletonSet_subset_domain hxSkel
    apply hxDom.resolve_left
    intro hxC
    have hxOuter : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.outerSet := by
      rw [(T.stage (n + 1)).src_isWeaklyAdmissible.outerSet_eq]
      exact hxC
    have hyOuter : y ∈ (T.stage (n + 1)).tgt.outerSet := by
      rw [← (T.stage (n + 1)).homeo.image_outerSet]
      exact ⟨(T.stage (n + 1)).homeo.invFun y, hxOuter,
        (T.stage (n + 1)).homeo.rightInvOn hySkel⟩
    have hyCurve : y ∈ modelCurve := by
      rw [← (T.stage (n + 1)).tgt_isWeaklyAdmissible.outerSet_eq]
      exact hyOuter
    exact halfSpoke_disjoint_modelCurve
      (two_le_meshCount w.reverse.overlay.delta) hzCurve y (hAhalf hyA) hyCurve
  have hJconn : IsPreconnected J := by
    exact hAconn.image (T.stage (n + 1)).homeo.invFun
      ((T.stage (n + 1)).homeo.continuousOn_invFun.mono hAskel)
  have hstageInv : (T.stage (n + 1)).homeo.invFun z = v z :=
    prescribedJordanStage_invFun_eq_boundaryInv hC hu (n + 1) hzCurve
  have hJball : J ⊆ ball c epsilon := by
    rintro x ⟨y, hyA, rfl⟩
    rw [mem_ball, hcz, ← hstageInv]
    exact hclose (hAskel hyA) (hAball hyA)
  have hccl : c ∈ closure J := by
    have hcont :=
      ((T.stage (n + 1)).homeo.continuousOn_invFun z hzSkel).mono hAskel
    have hcl := ContinuousWithinAt.mem_closure_image hcont hzcl
    rw [hstageInv, ← hcz] at hcl
    exact hcl
  have hAim : A ⊆ T.limitTower.F '' J := by
    intro y hyA
    have hySkel : y ∈ (T.stage (n + 1)).tgt.skeletonSet := hAskel hyA
    have hxSkel : (T.stage (n + 1)).homeo.invFun y ∈
        (T.stage (n + 1)).src.skeletonSet := by
      rw [← (T.stage (n + 1)).homeo.symm.image_skeletonSet]
      exact ⟨y, hySkel, rfl⟩
    have hxDom : (T.stage (n + 1)).homeo.invFun y ∈ C ∪ inside C :=
      (T.stage (n + 1)).src_isCellDecomposition.skeletonSet_subset_domain hxSkel
    refine ⟨(T.stage (n + 1)).homeo.invFun y, ⟨y, hyA, rfl⟩, ?_⟩
    rw [T.F_eq_skelHomeo hxSkel hxDom,
      (T.stage (n + 1)).homeo.rightInvOn hySkel]
  have huc : u c = z := by
    rw [hcz]
    exact hu.invOn.2 hzCurve
  refine ⟨J, hJinside, hJconn, hJball, hccl, ?_⟩
  rw [huc]
  exact closure_mono hAim hzcl

/-- Any two distinct prescribed anchors are joined by a finite-stage crosscut, and the same
abstract edge path in the matched target skeleton is its image.  The limit map agrees with
that finite skeleton map on the source crosscut. -/
theorem prescribedSourceAnchorSet_hasAnchorCrosscuts :
    HasAnchorCrosscuts C (prescribedSourceAnchorSet hC hu) u
      (prescribedJordanStageSequence hC u v hu).limitTower.F := by
  classical
  intro a b ha hb hab
  have haC : a ∈ C := prescribedSourceAnchorSet_subset hC hu ha
  have hbC : b ∈ C := prescribedSourceAnchorSet_subset hC hu hb
  obtain ⟨na, hacl⟩ := prescribedSourceAnchorSet_stageClosure hC hu ha
  obtain ⟨nb, hbcl⟩ := prescribedSourceAnchorSet_stageClosure hC hu hb
  let T := prescribedJordanStageSequence hC u v hu
  let N := max na nb
  let P := T.stage (N + 1)
  have hna : na + 1 ≤ N + 1 := Nat.add_le_add_right (Nat.le_max_left na nb) 1
  have hnb : nb + 1 ≤ N + 1 := Nat.add_le_add_right (Nat.le_max_right na nb) 1
  have haclP : a ∈ closure (P.src.skeletonSet \ C) := by
    apply closure_mono ?_ hacl
    rintro x ⟨hx, hxC⟩
    exact ⟨T.limitTower.skeletonSet_mono_le hna hx, hxC⟩
  have hbclP : b ∈ closure (P.src.skeletonSet \ C) := by
    apply closure_mono ?_ hbcl
    rintro x ⟨hx, hxC⟩
    exact ⟨T.limitTower.skeletonSet_mono_le hnb hx, hxC⟩
  have haSkel : a ∈ P.src.skeletonSet := by
    apply P.src.outerSet_subset_skeletonSet
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact haC
  have hbSkel : b ∈ P.src.skeletonSet := by
    apply P.src.outerSet_subset_skeletonSet
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact hbC
  obtain ⟨r⟩ := P.exists_subdivideSetData ((Set.finite_singleton b).insert a) (by
    rintro x (rfl | rfl)
    · exact haSkel
    · exact hbSkel)
  have haV : a ∈ V(r.pair.src.graph) := r.vertexSet_subset (Or.inl rfl)
  have hbV : b ∈ V(r.pair.src.graph) := r.vertexSet_subset (Or.inr rfl)
  have haclr : a ∈ closure (r.pair.src.skeletonSet \ C) := by
    rw [r.skeletonSet_eq]
    exact haclP
  have hbclr : b ∈ closure (r.pair.src.skeletonSet \ C) := by
    rw [r.skeletonSet_eq]
    exact hbclP
  have hPAdmissible : P.src.IsAdmissible C (C ∪ inside C) :=
    prescribedJordanStage_succ_src_isAdmissible hC hu N
  have hrAdmissible : r.pair.src.IsAdmissible C (C ∪ inside C) := by
    apply r.pair.src_isAdmissible
    rw [r.pair.src_nonboundary_eq, r.skeletonSet_eq, ← P.src_nonboundary_eq]
    exact hPAdmissible.isConnected_nonboundary
  have hrTargetAdmissible :
      r.pair.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) :=
    r.pair.tgt_isAdmissible hrAdmissible.isConnected_nonboundary
  let _ : r.pair.src.graph.Finite := CellStructure.Realization.finite_graph r.pair.src
  have hsourceStage := hrAdmissible.isStageOn
  have htargetStage : Graph.IsStageOn r.pair.tgt.graph r.pair.tgt.drawing
      modelCurve (inside modelCurve) := by
    apply CellStructure.Realization.IsAdmissible.isStageOn
    rw [modelCurve_union_inside]
    exact hrTargetAdmissible
  obtain ⟨ea, hea⟩ :=
    Graph.IsDrawing.exists_nonboundary_incident_of_mem_closure
      (G := r.pair.src.graph) (drawing := r.pair.src.drawing) (C := C)
      r.pair.src.isDrawing haV haC haclr
  obtain ⟨eb, heb⟩ :=
    Graph.IsDrawing.exists_nonboundary_incident_of_mem_closure
      (G := r.pair.src.graph) (drawing := r.pair.src.drawing) (C := C)
      r.pair.src.isDrawing hbV hbC hbclr
  obtain ⟨W, hWsrc, hWnonboundary, hPcross⟩ :=
    Graph.IsStageOn.exists_crosscut_path hsourceStage hC hab haC hbC
      ⟨ea, hea⟩ ⟨eb, heb⟩
  let Q : Set Plane := Graph.edgesCover r.pair.src.drawing W
  let Q' : Set Plane := r.pair.homeo.toFun '' Q
  have hQSkel : Q ⊆ r.pair.src.skeletonSet :=
    Graph.edgesCover_subset_pointSet (fun e he => hWsrc.edge_mem he)
  have hWedge : ∀ e ∈ W, e ∈ E(r.pair.str.skel) := by
    intro e he
    rw [← r.pair.src.edgeSet_graph]
    exact hWsrc.edge_mem he
  have hWnotOuter : ∀ e ∈ W, e ∉ E(r.pair.str.outerGraph) := by
    intro e he heOuter
    apply hWnonboundary e he
    intro x hx
    have hxOuter : x ∈ r.pair.src.outerSet :=
      Graph.edgeArc_subset_pointSet (by
        rw [Graph.edgeSet_map]
        exact heOuter) hx
    rwa [r.pair.src_isWeaklyAdmissible.outerSet_eq] at hxOuter
  rw [CellStructure.Realization.vertexSet_graph] at haV hbV
  obtain ⟨alpha, halpha, halphaPos⟩ := haV
  obtain ⟨beta, hbeta, hbetaPos⟩ := hbV
  have hsrcPathMapped : (r.pair.str.skel.map r.pair.src.pos).IsPath
      (r.pair.src.pos alpha) W (r.pair.src.pos beta) := by
    rw [halphaPos, hbetaPos]
    exact hWsrc
  obtain ⟨beta', hAbstractPath, hbeta'Pos⟩ :=
    Graph.IsPath.exists_lift_map r.pair.src.injOn_pos halpha hsrcPathMapped
  have hbeta'eq : beta' = beta :=
    r.pair.src.injOn_pos hAbstractPath.right_mem hbeta hbeta'Pos
  subst beta'
  have htargetPath : r.pair.tgt.graph.IsPath
      (r.pair.tgt.pos alpha) W (r.pair.tgt.pos beta) := by
    exact Graph.IsPath.map r.pair.tgt.injOn_pos hAbstractPath
  have htargetPoly : IsPolygonal (Graph.edgesCover r.pair.tgt.drawing W) :=
    Graph.IsDrawing.isPolygonal_edgesCover_of_mem r.pair.tgt.isDrawing
      htargetPath.isWalk (hWsrc.ne_nil hab) (fun e he =>
        hrTargetAdmissible.isPolygonal (hWedge e he) (hWnotOuter e he))
  have hQ'image : Q' = Graph.edgesCover r.pair.tgt.drawing W := by
    exact CellStructure.SkeletonHomeo.image_edgesCover r.pair.homeo hWedge
  have hga : r.pair.homeo.toFun a = u a := by
    calc
      r.pair.homeo.toFun a = P.homeo.toFun a := r.homeo_eqOn haSkel
      _ = u a := prescribedJordanStage_homeo_eq_boundary hC hu (N + 1) haC
  have hgb : r.pair.homeo.toFun b = u b := by
    calc
      r.pair.homeo.toFun b = P.homeo.toFun b := r.homeo_eqOn hbSkel
      _ = u b := prescribedJordanStage_homeo_eq_boundary hC hu (N + 1) hbC
  have hQ'target : IsCrosscut modelCurve Q'
      (r.pair.homeo.toFun a) (r.pair.homeo.toFun b) := by
    apply hPcross.image_of_injOn hQSkel r.pair.homeo.continuousOn_toFun
      r.pair.homeo.injOn isJordanCurve_modelCurve
    · change IsPolygonal Q'
      rw [hQ'image]
      exact htargetPoly
    · rw [hga]
      exact hu.mapsTo haC
    · rw [hgb]
      exact hu.mapsTo hbC
    · rintro y ⟨x, ⟨hxQ, hyEnds⟩, rfl⟩
      have hxSkel : x ∈ r.pair.src.skeletonSet := hQSkel hxQ
      have hySkel : r.pair.homeo.toFun x ∈ r.pair.tgt.skeletonSet := by
        rw [← r.pair.homeo.image_skeletonSet]
        exact Set.mem_image_of_mem _ hxSkel
      apply htargetStage.pointSet_diff_subset
      refine ⟨hySkel, fun hyCurve => ?_⟩
      have hyOuter : r.pair.homeo.toFun x ∈ r.pair.tgt.outerSet := by
        rw [r.pair.tgt_isWeaklyAdmissible.outerSet_eq]
        exact hyCurve
      have hxOuter : x ∈ r.pair.src.outerSet := by
        rw [← r.pair.homeo.symm.image_outerSet]
        exact ⟨r.pair.homeo.toFun x, hyOuter,
          r.pair.homeo.leftInvOn hxSkel⟩
      have hxC : x ∈ C := by
        rw [← r.pair.src_isWeaklyAdmissible.outerSet_eq]
        exact hxOuter
      have hxEnds : x ∈ ({a, b} : Set Plane) := by
        have hxInter : x ∈ Q ∩ C := ⟨hxQ, hxC⟩
        rw [hPcross.inter_eq] at hxInter
        exact hxInter
      rcases hxEnds with rfl | rfl
      · exact hyEnds (Or.inl rfl)
      · exact hyEnds (Or.inr rfl)
  have hFQ : Set.EqOn T.limitTower.F r.pair.homeo.toFun (Q \ {a, b}) := by
    intro x hx
    have hxP : x ∈ P.src.skeletonSet := by
      rw [← r.skeletonSet_eq]
      exact hQSkel hx.1
    have hxDom : x ∈ C ∪ inside C :=
      P.src_isCellDecomposition.skeletonSet_subset_domain hxP
    calc
      T.limitTower.F x = P.homeo.toFun x := T.F_eq_skelHomeo hxP hxDom
      _ = r.pair.homeo.toFun x := (r.homeo_eqOn hxP).symm
  have hagree : T.limitTower.F '' (Q \ {a, b}) =
      Q' \ {r.pair.homeo.toFun a, r.pair.homeo.toFun b} := by
    exact image_sdiff_eq_of_eqOn hQSkel r.pair.homeo.injOn
      hPcross.arc.left_mem hPcross.arc.right_mem hFQ
  refine ⟨Q, Q', hPcross, ?_, ?_⟩
  · simpa only [hga, hgb] using hQ'target
  · simpa only [hga, hgb] using hagree

end Schoenflies
