/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.OverlayExtension
public import LeanPool.Schoenflies.StageTransition

/-!
# Polygonal joining ears for boundary-touching source crosscuts

When both ends of the auxiliary face crosscut lie on the wild outer curve, deleting that curve
separates the crosscut/grid carrier from the old nonboundary source carrier.  The last step of
`prop:local-grid-attachment` joins those two carriers by a simple polygonal arc in the open
source domain.

This module begins with the finite inner construction: re-overlay the already-subdivided source
core, crosscut, and grid together with the joining segments, retaining every old inner vertex.
`OverlayExtension` then supplies the plane-subdivision certificate automatically.
-/

public section

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

namespace Graph

variable {β : Type*} {G A B : _root_.Graph Plane β} {drawing : β → ℝ → Plane}

/-- Two edge-disjoint subgraphs of one plane drawing can meet only at vertices common to both.
This is the converse interface used when an already-plane union is re-subdivided on one side. -/
theorem IsDrawing.common_vertices_of_disjoint_subgraphs (h : G.IsDrawing drawing)
    (hA : A ≤ G) (hB : B ≤ G) (hdisj : Disjoint E(A) E(B))
    {x : Plane} (hxA : x ∈ _root_.Graph.pointSet A drawing)
    (hxB : x ∈ _root_.Graph.pointSet B drawing) :
    x ∈ V(A) ∩ V(B) := by
  rcases hxA with hxAV | hxAE
  · refine ⟨hxAV, ?_⟩
    rcases hxB with hxBV | hxBE
    · exact hxBV
    · obtain ⟨e, heB, hxe⟩ := Set.mem_iUnion₂.1 hxBE
      obtain ⟨u, v, huv⟩ := B.exists_isLink_of_mem_edgeSet heB
      rcases h.vertex_mem_edgeArc (hB.isLink_mono huv) (hA.vertexSet_mono hxAV) hxe with
        rfl | rfl
      · exact huv.left_mem
      · exact huv.right_mem
  · rcases hxB with hxBV | hxBE
    · refine ⟨?_, hxBV⟩
      obtain ⟨e, heA, hxe⟩ := Set.mem_iUnion₂.1 hxAE
      obtain ⟨u, v, huv⟩ := A.exists_isLink_of_mem_edgeSet heA
      rcases h.vertex_mem_edgeArc (hA.isLink_mono huv) (hB.vertexSet_mono hxBV) hxe with
        rfl | rfl
      · exact huv.left_mem
      · exact huv.right_mem
    · obtain ⟨e, heA, hxe⟩ := Set.mem_iUnion₂.1 hxAE
      obtain ⟨f, hfB, hxf⟩ := Set.mem_iUnion₂.1 hxBE
      have hef : e ≠ f := fun hef => Set.disjoint_left.1 hdisj heA (hef ▸ hfB)
      have hinter := h.edge_inter
        (hA.edgeSet_mono heA) (hB.edgeSet_mono hfB) hef hxe hxf
      obtain ⟨a, b, hab⟩ := A.exists_isLink_of_mem_edgeSet heA
      obtain ⟨c, d, hcd⟩ := B.exists_isLink_of_mem_edgeSet hfB
      have hxAV : x ∈ V(A) := by
        rcases h.vertex_mem_edgeArc (hA.isLink_mono hab) hinter.1 hxe with rfl | rfl
        · exact hab.left_mem
        · exact hab.right_mem
      have hxBV : x ∈ V(B) := by
        rcases h.vertex_mem_edgeArc (hB.isLink_mono hcd) hinter.1 hxf with rfl | rfl
        · exact hcd.left_mem
        · exact hcd.right_mem
      exact ⟨hxAV, hxBV⟩

end Graph

/-- The distinct head and last vertices of a polygonal chain are endpoints of segments retained
by `segsOf`, even when the input list contains repeated consecutive vertices. -/
theorem head_getLast_mem_endSet_segsOf {vs : List Plane} (hvs : vs ≠ [])
    (hne : vs.head hvs ≠ vs.getLast hvs) :
    vs.head hvs ∈ endSet (segsOf vs) ∧ vs.getLast hvs ∈ endSet (segsOf vs) := by
  classical
  induction vs with
  | nil => exact (hvs rfl).elim
  | cons u tl ih =>
      match tl with
      | [] => exact (hne rfl).elim
      | v :: rest =>
          rw [segsOf_cons_cons]
          by_cases huv : u = v
          · rw [ite_eq_left huv]
            subst u
            exact ih (List.cons_ne_nil v rest) hne
          · rw [ite_eq_right huv]
            constructor
            · exact ⟨(u, v), List.mem_cons_self, Or.inl rfl⟩
            · by_cases hvlast : v = (v :: rest).getLast (List.cons_ne_nil v rest)
              · exact ⟨(u, v), List.mem_cons_self, Or.inr (by
                  rw [List.getLast_cons (a := u) (List.cons_ne_nil v rest)]
                  exact hvlast.symm)⟩
              · obtain ⟨-, hlast⟩ := ih (List.cons_ne_nil v rest) hvlast
                obtain ⟨A, hA, hxA⟩ := hlast
                exact ⟨A, List.mem_cons_of_mem _ hA, by
                  rw [List.getLast_cons (a := u) (List.cons_ne_nil v rest)]
                  exact hxA⟩

namespace SourceNonboundarySegmentCover

variable {Q : SourceNonboundarySegmentCover P} {J : Piece} {p : Plane}
  {s epsilon : ℝ} {extra : List Plane}

/-- Re-overlay the complete auxiliary-crosscut inner graph together with a list of polygonal
joining segments. -/
noncomputable def joinedCrosscutOverlay
    (Q : SourceNonboundarySegmentCover P) (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) (joins : List Piece) : Graph Plane Piece :=
  extendOverlay (Q.crosscutPieces J p s epsilon)
    (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins

instance joinedCrosscutOverlay_finite
    (Q : SourceNonboundarySegmentCover P) (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) (joins : List Piece) :
    (Q.joinedCrosscutOverlay J p s epsilon extra joins).Finite :=
  extendOverlay_finite _ _ _

/-- The joined inner overlay occupies exactly the old core/crosscut/grid carrier together with
the polygonal joining carrier. -/
theorem joinedCrosscutOverlay_pointSet (Q : SourceNonboundarySegmentCover P)
    (J : Piece) (p : Plane) (s epsilon : ℝ) (extra : List Plane) (joins : List Piece) :
    Graph.pointSet (Q.joinedCrosscutOverlay J p s epsilon extra joins) segmentDrawing =
      Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing ∪ cover joins := by
  exact extendOverlay_pointSet _ _ _

/-- The joined inner overlay is a finite straight-line plane graph. -/
theorem joinedCrosscutOverlay_isDrawing
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    Graph.IsDrawing (Q.joinedCrosscutOverlay J p s epsilon extra joins) segmentDrawing :=
  extendOverlay_isDrawing (Q.crosscutPieces_nondeg hs hJ) hjoins

/-- Every vertex of the core/crosscut/grid overlay survives the joining re-overlay. -/
theorem crosscutOverlayVertices_subset_joinedCrosscutOverlay
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    V(Q.crosscutOverlay J p s epsilon extra) ⊆
      V(Q.joinedCrosscutOverlay J p s epsilon extra joins) :=
  attachGraphVertices_subset_extendOverlay (Q.crosscutPieces_nondeg hs hJ) hjoins

/-- The joined inner overlay is a plane subdivision extension of the complete old inner
crosscut overlay. -/
theorem crosscutOverlay_isPlaneSubdivisionExtension_joined
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    IsPlaneSubdivisionExtension
      (Q.crosscutOverlay J p s epsilon extra) segmentDrawing
      (Q.joinedCrosscutOverlay J p s epsilon extra joins) segmentDrawing :=
  attachGraph_isPlaneSubdivisionExtension_extendOverlay
    (Q.crosscutPieces_nondeg hs hJ) hjoins

/-- Every old inner edge is absorbed by its subdivision in the joined overlay. -/
theorem joinedCrosscutOverlay_old_edge_subset
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    ∀ {A : Piece}, A ∈ E(Q.crosscutOverlay J p s epsilon extra) → ∀ {R : Piece},
      R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins) →
      (Graph.edgeArc segmentDrawing R ∩
        (Graph.edgeArc segmentDrawing A \
          V(Q.joinedCrosscutOverlay J p s epsilon extra joins))).Nonempty →
      Graph.edgeArc segmentDrawing R ⊆ Graph.edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  exact extendOverlay_edge_subset (Q.crosscutPieces_nondeg hs hJ) hjoins hA hR hmeet

/-- A joined-overlay edge meeting the joining carrier away from overlay vertices is absorbed by
that carrier. -/
theorem joinedCrosscutOverlay_join_subset
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    ∀ {R : Piece}, R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins) →
      (Graph.edgeArc segmentDrawing R ∩
        (cover joins \ V(Q.joinedCrosscutOverlay J p s epsilon extra joins))).Nonempty →
      Graph.edgeArc segmentDrawing R ⊆ cover joins := by
  intro R hR hmeet
  obtain ⟨z, hzR, hzJoin, hznot⟩ := hmeet
  obtain ⟨A, hA, hzA⟩ := mem_cover_iff.1 hzJoin
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints
        (extendedOverlayPieces (Q.crosscutPieces J p s epsilon)
          (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins)
        (Q.crosscutOverlay J p s epsilon extra).vertexFinset.toList)
      (P₀ := A)
      (List.mem_append_right
        (currentOverlayPieces (Q.crosscutPieces J p s epsilon)
          (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)) hA)
      hzA
  have hzR'Arc : z ∈ Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.joinedCrosscutOverlay_isDrawing hs hJ hjoins).unique_edge_at
      hR hR' hznot hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact fun x hx => mem_cover_iff.2 ⟨A, hA, hR'A hx⟩

/-- Every endpoint of a joining segment is a vertex of the joined inner overlay. -/
theorem joinEnds_subset_joinedCrosscutOverlay
    (hs : 0 < s) (hJ : J.Nondeg) {joins : List Piece}
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    endSet joins ⊆ V(Q.joinedCrosscutOverlay J p s epsilon extra joins) := by
  intro x hx
  obtain ⟨A, hA, hxA⟩ := hx
  change x ∈ V(overlayGraph
    (extendedOverlayPieces (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins)
    (attachPoints
      (extendedOverlayPieces (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList) joins)
      (Q.crosscutOverlay J p s epsilon extra).vertexFinset.toList))
  apply overlayGraph_mem_vertexSet_of_mem_cover
  · intro R hR
    rcases List.mem_append.1 hR with hR | hR
    · exact currentOverlayPieces_nondeg (Q.crosscutPieces_nondeg hs hJ) R hR
    · exact hjoins R hR
  · exact attachPoints_endsAreCut _ _ A
      (List.mem_append_right _ hA) x hxA
  · exact mem_cover_iff.2 ⟨A, List.mem_append_right _ hA, by
      rcases hxA with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _⟩

/-! ### Fresh relabelling and the wild outer graph -/

/-- Fresh abstract edge names for the joined inner overlay. -/
structure JoinedCrosscutOverlayRelabeling
    (w : Q.CrosscutOverlayRelabeling J p s epsilon extra) (joins : List Piece) where
  /-- Fresh names for the overlay after adding the joining segments. -/
  name : Piece → γ
  name_inj : InjOn name E(Q.joinedCrosscutOverlay J p s epsilon extra joins)
  name_fresh : ∀ R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins),
    name R ∉ P.str.cells

/-- An infinite cell-name type supplies fresh names for the joined overlay. -/
theorem CrosscutOverlayRelabeling.exists_joinedRelabeling [Infinite γ]
    (w : Q.CrosscutOverlayRelabeling J p s epsilon extra) (joins : List Piece) :
    Nonempty (JoinedCrosscutOverlayRelabeling w joins) := by
  obtain ⟨name, hname, hfresh⟩ := exists_finiteGraph_edgeRelabeling_avoiding γ
    (Q.joinedCrosscutOverlay J p s epsilon extra joins) P.str.cells P.str.finite_cells
  exact ⟨⟨name, hname, hfresh⟩⟩

namespace JoinedCrosscutOverlayRelabeling

variable {joins : List Piece}
  {w : Q.CrosscutOverlayRelabeling J p s epsilon extra}
  (u : JoinedCrosscutOverlayRelabeling w joins)

/-- The unchanged mapped wild outer graph. -/
abbrev outerGraph (_u : JoinedCrosscutOverlayRelabeling w joins) :
    _root_.Graph Plane γ := P.str.outerGraph.map P.src.pos

/-- The freshly relabelled joined inner overlay. -/
noncomputable abbrev innerGraph : _root_.Graph Plane γ :=
  (Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelEdges u.name u.name_inj

/-- The mixed graph after adjoining the polygonal join. -/
noncomputable def graph : _root_.Graph Plane γ := u.outerGraph.union u.innerGraph

/-- The joined drawing keeps the wild outer parametrizations and draws every inner edge as a
straight segment. -/
noncomputable def drawing : γ → ℝ → Plane := by
  classical
  exact fun e =>
    if e ∈ E(P.str.outerGraph) then P.src.drawing e
    else (Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
      u.name segmentDrawing e

theorem compatible : u.outerGraph.Compatible u.innerGraph := by
  apply _root_.Graph.Compatible.of_disjoint_edgeSet
  rw [Set.disjoint_left, _root_.Graph.edgeSet_map, _root_.Graph.edgeSet_relabelEdges]
  intro e heOuter heInner
  obtain ⟨R, hR, hname⟩ := heInner
  rw [← hname] at heOuter
  exact u.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

theorem disjoint_edgeSet : Disjoint E(u.outerGraph) E(u.innerGraph) := by
  rw [Set.disjoint_left, _root_.Graph.edgeSet_map, _root_.Graph.edgeSet_relabelEdges]
  intro e heOuter heInner
  obtain ⟨R, hR, hname⟩ := heInner
  rw [← hname] at heOuter
  exact u.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

theorem drawing_of_outer {e : γ} (he : e ∈ E(P.str.outerGraph)) :
    u.drawing e = P.src.drawing e := by simp [drawing, he]

theorem drawing_of_inner {e : γ} (he : e ∈ E(u.innerGraph)) :
    u.drawing e =
      (Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
        u.name segmentDrawing e := by
  rw [drawing, ite_eq_right]
  obtain ⟨R, hR, rfl⟩ := he
  exact fun heOuter => u.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

theorem outer_isDrawing : u.outerGraph.IsDrawing u.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    (P.src.isDrawing.mono (P.str.outerGraph_le.map P.src.pos))
  intro e he
  apply u.drawing_of_outer
  rwa [_root_.Graph.edgeSet_map] at he

theorem inner_isDrawing (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    u.innerGraph.IsDrawing u.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    ((Q.joinedCrosscutOverlay_isDrawing hs hJ hjoins).relabelEdges u.name_inj)
  intro e he
  exact u.drawing_of_inner he

theorem outer_pointSet :
    _root_.Graph.pointSet u.outerGraph u.drawing = srcOuter := by
  calc
    _root_.Graph.pointSet u.outerGraph u.drawing =
        _root_.Graph.pointSet u.outerGraph P.src.drawing := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval)
        (u.drawing_of_outer (by rwa [_root_.Graph.edgeSet_map] at he))
    _ = P.src.outerSet := rfl
    _ = srcOuter := P.src_isWeaklyAdmissible.outerSet_eq

theorem inner_pointSet :
    _root_.Graph.pointSet u.innerGraph u.drawing =
      _root_.Graph.pointSet (Q.joinedCrosscutOverlay J p s epsilon extra joins)
        segmentDrawing := by
  calc
    _root_.Graph.pointSet u.innerGraph u.drawing =
        _root_.Graph.pointSet u.innerGraph
          ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
            u.name segmentDrawing) := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval) (u.drawing_of_inner he)
    _ = _root_.Graph.pointSet (Q.joinedCrosscutOverlay J p s epsilon extra joins)
        segmentDrawing := _root_.Graph.pointSet_relabelEdges u.name_inj

/-- The joined inner overlay remains plane when every joining segment lies in the open source
domain. -/
theorem graph_isDrawing (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    u.graph.IsDrawing u.drawing := by
  apply Schoenflies.Graph.isDrawing_union_of_common_vertices
    u.outer_isDrawing (u.inner_isDrawing hs hJ hjoins) u.compatible
  intro x hxOuter hxInner
  rw [u.outer_pointSet] at hxOuter
  rw [u.inner_pointSet, Q.joinedCrosscutOverlay_pointSet] at hxInner
  rcases hxInner with hxOldInner | hxJoin
  · have hxOldOuter : x ∈ _root_.Graph.pointSet w.outerGraph w.drawing := by
      rwa [w.outer_pointSet]
    have hxOldInner' : x ∈ _root_.Graph.pointSet w.innerGraph w.drawing := by
      rwa [w.inner_pointSet]
    have hOldDisjoint : Disjoint E(w.outerGraph) E(w.innerGraph) := by
      rw [Set.disjoint_left, _root_.Graph.edgeSet_map,
        _root_.Graph.edgeSet_relabelEdges]
      intro e heOuter heInner
      obtain ⟨R, hR, hname⟩ := heInner
      rw [← hname] at heOuter
      exact w.name_fresh R hR
        (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))
    have hxOldVertices :=
      Schoenflies.Graph.IsDrawing.common_vertices_of_disjoint_subgraphs
        (w.graph_isDrawing hs hJ hJgeom hwindow)
        (_root_.Graph.left_le_union _ _) w.compatible.right_le_union hOldDisjoint
        hxOldOuter hxOldInner'
    refine ⟨hxOldVertices.1, ?_⟩
    rw [_root_.Graph.vertexSet_relabelEdges] at hxOldVertices ⊢
    exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
      hs hJ hjoins hxOldVertices.2
  · exact ((hjoinsOpen hxJoin).2 hxOuter).elim

/-- The joined mixed graph is finite. -/
theorem graph_finite : u.graph.Finite where
  finite_vertexSet := by
    rw [graph, _root_.Graph.vertexSet_union, outerGraph, _root_.Graph.vertexSet_map,
      _root_.Graph.vertexSet_relabelEdges]
    exact ((P.str.finite_vertexSet.subset P.str.outerGraph_le.vertexSet_mono).image
      P.src.pos).union
      (_root_.Graph.finite_vertexSet
        (Q.joinedCrosscutOverlay J p s epsilon extra joins))
  finite_edgeSet := by
    rw [graph, _root_.Graph.edgeSet_union, outerGraph, _root_.Graph.edgeSet_map,
      _root_.Graph.edgeSet_relabelEdges]
    exact (P.str.finite_edgeSet.subset P.str.outerGraph_le.edgeSet_mono).union
      ((_root_.Graph.finite_edgeSet
        (Q.joinedCrosscutOverlay J p s epsilon extra joins)).image u.name)

/-- Exact carrier of the joined mixed graph. -/
theorem graph_pointSet :
    _root_.Graph.pointSet u.graph u.drawing =
      _root_.Graph.pointSet w.graph w.drawing ∪ cover joins := by
  rw [graph, _root_.Graph.pointSet_union, u.outer_pointSet, u.inner_pointSet,
    Q.joinedCrosscutOverlay_pointSet]
  calc
    srcOuter ∪
        (_root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra)
          segmentDrawing ∪ cover joins) =
        (srcOuter ∪
          _root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing) ∪
            cover joins := by ac_rfl
    _ = _root_.Graph.pointSet w.graph w.drawing ∪ cover joins := by
      rw [CrosscutOverlayRelabeling.graph, _root_.Graph.pointSet_union,
        w.outer_pointSet, w.inner_pointSet]

/-- Every vertex of the old mixed crosscut graph survives the joining re-overlay. -/
theorem oldVertices_subset_graph (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    V(w.graph) ⊆ V(u.graph) := by
  intro x hx
  rw [CrosscutOverlayRelabeling.graph, _root_.Graph.vertexSet_union] at hx
  rw [graph, _root_.Graph.vertexSet_union]
  rcases hx with hxOuter | hxInner
  · exact Or.inl hxOuter
  · exact Or.inr (by
      rw [_root_.Graph.vertexSet_relabelEdges] at hxInner ⊢
      exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
        hs hJ hjoins hxInner)

/-- A new mixed edge meeting an old mixed edge away from new vertices is one of that old edge's
subdivision pieces. -/
theorem old_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(w.graph) → ∀ {f : γ}, f ∈ E(u.graph) →
      (_root_.Graph.edgeArc u.drawing f ∩
        (_root_.Graph.edgeArc w.drawing e \ V(u.graph))).Nonempty →
      _root_.Graph.edgeArc u.drawing f ⊆ _root_.Graph.edgeArc w.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hze, hznot⟩ := hmeet
  rcases he with heOuter | heInner
  · have heAbstract : e ∈ E(P.str.outerGraph) := by
      rwa [_root_.Graph.edgeSet_map] at heOuter
    have heNew : e ∈ E(u.graph) := Or.inl heOuter
    have hzeNew : z ∈ _root_.Graph.edgeArc u.drawing e := by
      have hu := u.drawing_of_outer heAbstract
      have hw := w.drawing_of_outer heAbstract
      rw [_root_.Graph.edgeArc, hu]
      rw [_root_.Graph.edgeArc, hw] at hze
      exact hze
    have hef : e = f :=
      (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen).unique_edge_at
        heNew hf hznot hzeNew hzf
    subst f
    have hu := u.drawing_of_outer heAbstract
    have hw := w.drawing_of_outer heAbstract
    intro y hy
    rw [_root_.Graph.edgeArc, hu] at hy
    rw [_root_.Graph.edgeArc, hw]
    exact hy
  · obtain ⟨A, hA, rfl⟩ := heInner
    have hAOld : w.name A ∈ E(w.innerGraph) := ⟨A, hA, rfl⟩
    have hOldArc : _root_.Graph.edgeArc w.drawing (w.name A) =
        _root_.Graph.edgeArc segmentDrawing A := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name A) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name A) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) (w.drawing_of_inner hAOld)
        _ = _root_.Graph.edgeArc segmentDrawing A :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hA
    rcases hf with hfOuter | hfInner
    · exfalso
      have hzOldOuter : z ∈ _root_.Graph.pointSet w.outerGraph w.drawing := by
        rw [w.outer_pointSet, ← u.outer_pointSet]
        exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
      have hzOldInner : z ∈ _root_.Graph.pointSet w.innerGraph w.drawing :=
        _root_.Graph.edgeArc_subset_pointSet hAOld (hOldArc ▸ hze)
      have hOldDisjoint : Disjoint E(w.outerGraph) E(w.innerGraph) := by
        rw [Set.disjoint_left, _root_.Graph.edgeSet_map,
          _root_.Graph.edgeSet_relabelEdges]
        intro g hgOuter hgInner
        obtain ⟨R, hR, hname⟩ := hgInner
        rw [← hname] at hgOuter
        exact w.name_fresh R hR
          (P.str.mem_cells_of_mem_edgeSet
            (P.str.outerGraph_le.edgeSet_mono hgOuter))
      have hzOldVertex :=
        Schoenflies.Graph.IsDrawing.common_vertices_of_disjoint_subgraphs
          (w.graph_isDrawing hs hJ hJgeom hwindow)
          (_root_.Graph.left_le_union _ _) w.compatible.right_le_union hOldDisjoint
          hzOldOuter hzOldInner |>.2
      apply hznot
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by
        rw [_root_.Graph.vertexSet_relabelEdges] at hzOldVertex ⊢
        exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
          hs hJ hjoins hzOldVertex)
    · obtain ⟨R, hR, rfl⟩ := hfInner
      have hRNew : u.name R ∈ E(u.innerGraph) := ⟨R, hR, rfl⟩
      have hNewArc : _root_.Graph.edgeArc u.drawing (u.name R) =
          _root_.Graph.edgeArc segmentDrawing R := by
        calc
          _root_.Graph.edgeArc u.drawing (u.name R) =
              _root_.Graph.edgeArc
                ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
                  u.name segmentDrawing) (u.name R) := by
            simpa only [_root_.Graph.edgeArc] using congrArg
              (fun g : ℝ → Plane => g '' unitInterval) (u.drawing_of_inner hRNew)
          _ = _root_.Graph.edgeArc segmentDrawing R :=
            _root_.Graph.edgeArc_relabelDrawing u.name_inj hR
      rw [hNewArc, hOldArc]
      apply Q.joinedCrosscutOverlay_old_edge_subset hs hJ hjoins hA hR
      refine ⟨z, hNewArc ▸ hzf, hOldArc ▸ hze, ?_⟩
      intro hzLocal
      apply hznot
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The joined mixed graph is a plane subdivision extension of the complete old mixed graph. -/
theorem oldGraph_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension w.graph w.drawing u.graph u.drawing where
  finite := u.graph_finite
  oldIsDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  isDrawing := u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen
  vertexSet_subset := u.oldVertices_subset_graph hs hJ hjoins
  pointSet_subset := by
    rw [u.graph_pointSet]
    exact subset_union_left
  edge_subset := by
    intro e he f hf hmeet
    exact u.old_edge_subset hs hJ hJgeom hwindow hjoins hjoinsOpen he hf hmeet

/-- The exact trace of the old mixed carrier remains 2-connected in the joined graph. -/
theorem oldTrace_isTwoConnected (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    (htwo : w.graph.IsTwoConnected) :
    (_root_.Graph.traceGraph u.graph u.drawing
      (_root_.Graph.pointSet w.graph w.drawing)).IsTwoConnected :=
  (u.oldGraph_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)
    |>.trace_isTwoConnected htwo

/-- Every endpoint of a joining segment is a vertex of the joined mixed graph. -/
theorem joinEnds_subset_graph (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg) :
    endSet joins ⊆ V(u.graph) := by
  intro x hx
  rw [graph, _root_.Graph.vertexSet_union]
  exact Or.inr (by
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.joinEnds_subset_joinedCrosscutOverlay hs hJ hjoins hx)

/-- The complete polygonal joining carrier lies in the joined mixed graph. -/
theorem joins_subset_graph :
    cover joins ⊆ _root_.Graph.pointSet u.graph u.drawing := by
  rw [u.graph_pointSet]
  exact subset_union_right

/-- A joined mixed edge meeting the polygonal joining carrier away from mixed vertices is
absorbed by that carrier. -/
theorem graph_join_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {f : γ}, f ∈ E(u.graph) →
      (_root_.Graph.edgeArc u.drawing f ∩ (cover joins \ V(u.graph))).Nonempty →
      _root_.Graph.edgeArc u.drawing f ⊆ cover joins := by
  intro f hf hmeet
  obtain ⟨z, hzf, hzJoin, hznot⟩ := hmeet
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← u.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
    exact (hjoinsOpen hzJoin).2 hzOuter
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hRInner : u.name R ∈ E(u.innerGraph) := ⟨R, hR, rfl⟩
    have hArc : _root_.Graph.edgeArc u.drawing (u.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc u.drawing (u.name R) =
            _root_.Graph.edgeArc
              ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
                u.name segmentDrawing) (u.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) (u.drawing_of_inner hRInner)
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing u.name_inj hR
    rw [hArc]
    apply Q.joinedCrosscutOverlay_join_subset hs hJ hjoins hR
    refine ⟨z, hArc ▸ hzf, hzJoin, ?_⟩
    intro hzLocal
    apply hznot
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The trace supported on the polygonal joining carrier occupies that carrier exactly. -/
theorem joinTrace_pointSet (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    _root_.Graph.pointSet
      (_root_.Graph.traceGraph u.graph u.drawing (cover joins)) u.drawing = cover joins :=
  _root_.Graph.pointSet_traceGraph_eq
    (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen)
    _ u.joins_subset_graph (by
      intro f hf hmeet
      exact u.graph_join_subset hs hJ hjoins hjoinsOpen hf hmeet)

/-- An arc presented by the joining pieces is the exact carrier of a path in the joined mixed
graph. -/
theorem exists_join_trace (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    {x y : Plane} (hxy : x ≠ y) (hxEnd : x ∈ endSet joins)
    (hyEnd : y ∈ endSet joins) (hArc : IsArcBetween (cover joins) x y) :
    ∃ D : List γ, u.graph.IsPath x D y ∧
      _root_.Graph.edgesCover u.drawing D = cover joins := by
  let T := _root_.Graph.traceGraph u.graph u.drawing (cover joins)
  have hTle : T ≤ u.graph := _root_.Graph.traceGraph_le _
  let _ : u.graph.Finite := u.graph_finite
  let _ : T.Finite := _root_.Graph.Finite.of_le hTle
  have hpoint : _root_.Graph.pointSet T u.drawing = cover joins :=
    u.joinTrace_pointSet hs hJ hJgeom hwindow hjoins hjoinsOpen
  have hxGraph : x ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hxEnd
  have hyGraph : y ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hyEnd
  have hxT : x ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hxGraph, hArc.left_mem⟩
  have hyT : y ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hyGraph, hArc.right_mem⟩
  have hTconn : T.Connected := _root_.Graph.connected_of_isPreconnected_pointSet
    ((u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen).mono hTle)
    (hpoint.symm ▸ hArc.isArc.isConnected.isPreconnected) ⟨x, hxT⟩
  obtain ⟨D, hD⟩ := (hTconn.reaches hxT hyT).exists_isPath
  have hDGraph : u.graph.IsPath x D y := hD.mono hTle
  have hPathArc : IsArcBetween (_root_.Graph.edgesCover u.drawing D) x y :=
    (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen).path_isArcBetween
      hDGraph (hDGraph.ne_nil hxy)
  have hcoverSub : _root_.Graph.edgesCover u.drawing D ⊆ cover joins := by
    rw [← hpoint]
    exact _root_.Graph.edgesCover_subset_pointSet fun g hg => hD.edge_mem hg
  exact ⟨D, hDGraph,
    hPathArc.eq_of_subset_arc hArc hArc hcoverSub Set.Subset.rfl⟩

/-- Attaching a polygonal joining arc between two old-carrier points makes the entire joined
mixed graph 2-connected. -/
theorem graph_isTwoConnected_of_join (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    (hOldTwo : w.graph.IsTwoConnected)
    {x y : Plane} (hxy : x ≠ y) (hxEnd : x ∈ endSet joins)
    (hyEnd : y ∈ endSet joins) (hxOld : x ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hyOld : y ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hArc : IsArcBetween (cover joins) x y) :
    u.graph.IsTwoConnected := by
  obtain ⟨D, hD, hcover⟩ :=
    u.exists_join_trace hs hJ hJgeom hwindow hjoins hjoinsOpen
      hxy hxEnd hyEnd hArc
  let T := _root_.Graph.traceGraph u.graph u.drawing
    (_root_.Graph.pointSet w.graph w.drawing)
  let C := u.graph.pathGraphOf x D
  have hT2 : T.IsTwoConnected :=
    u.oldTrace_isTwoConnected hs hJ hJgeom hwindow hjoins hjoinsOpen hOldTwo
  have hxGraph : x ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hxEnd
  have hyGraph : y ∈ V(u.graph) := u.joinEnds_subset_graph hs hJ hjoins hyEnd
  have hxT : x ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hxGraph, hxOld⟩
  have hyT : y ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hyGraph, hyOld⟩
  have hTC : T.Compatible C :=
    _root_.Graph.Compatible.of_le_le (_root_.Graph.traceGraph_le _)
      (_root_.Graph.pathGraphOf_le hD.isWalk)
  have hUnion2 : (T.union C).IsTwoConnected :=
    hT2.ear hTC hD.isPathGraph_pathGraphOf hxy hxT hyT
  apply hUnion2.of_le_of_vertexSet_subset
    (_root_.Graph.union_le (_root_.Graph.traceGraph_le _)
      (_root_.Graph.pathGraphOf_le hD.isWalk))
  intro z hz
  rw [_root_.Graph.vertexSet_union]
  have hzPoint : z ∈ _root_.Graph.pointSet u.graph u.drawing :=
    _root_.Graph.vertexSet_subset_pointSet hz
  rw [u.graph_pointSet] at hzPoint
  rcases hzPoint with hzOld | hzJoin
  · exact Or.inl (by
      rw [_root_.Graph.traceGraph_vertexSet]
      exact ⟨hz, hzOld⟩)
  · exact Or.inr (by
      rw [_root_.Graph.pathGraphOf_vertexSet]
      apply (u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen)
        |>.mem_walkVertices_of_mem_edgesCover_walk hD.isWalk hz
      rw [hcover]
      exact hzJoin)

/-- The joined graph remains a plane subdivision extension of the complete old source drawing. -/
theorem source_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension P.src.graph P.src.drawing u.graph u.drawing :=
  (w.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).trans
    (u.oldGraph_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)

/-- The joined graph stays in the closed source domain. -/
theorem graph_pointSet_subset (hs : 0 < s)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    _root_.Graph.pointSet u.graph u.drawing ⊆ srcDom := by
  rw [u.graph_pointSet]
  exact Set.union_subset (w.graph_pointSet_subset hs hJgeom hwindow)
    (hjoinsOpen.trans sdiff_subset)

/-- Every joined inner edge is cut either from an old core/crosscut/grid edge or from one of
the polygonal joining segments. -/
theorem joinedInner_edge_source {R : Piece}
    (hR : R ∈ E(Q.joinedCrosscutOverlay J p s epsilon extra joins)) :
    (∃ A ∈ E(Q.crosscutOverlay J p s epsilon extra), R.seg ⊆ A.seg) ∨
      ∃ A ∈ joins, R.seg ⊆ A.seg := by
  exact extendOverlay_edge_source hR

/-- Every joined mixed edge either lies on the wild outer curve or is polygonal with all
nonvertex points in the open source domain. -/
theorem graph_edge_dichotomy (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(u.graph) → _root_.Graph.edgeArc u.drawing e ⊆ srcOuter ∨
      (IsPolygonal (_root_.Graph.edgeArc u.drawing e) ∧
        _root_.Graph.edgeArc u.drawing e \ V(u.graph) ⊆ srcDom \ srcOuter) := by
  intro e he
  rcases he with heOuter | heInner
  · exact Or.inl (by
      intro x hx
      rw [← u.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet heOuter hx)
  · obtain ⟨R, hR, rfl⟩ := heInner
    have hRInner : u.name R ∈ E(u.innerGraph) := ⟨R, hR, rfl⟩
    have hArc : _root_.Graph.edgeArc u.drawing (u.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc u.drawing (u.name R) =
            _root_.Graph.edgeArc
              ((Q.joinedCrosscutOverlay J p s epsilon extra joins).relabelDrawing
                u.name segmentDrawing) (u.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) (u.drawing_of_inner hRInner)
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing u.name_inj hR
    rw [hArc]
    refine Or.inr ⟨by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _, ?_⟩
    intro x hx
    have hxSeg : x ∈ R.seg := by
      rw [← edgeArc_segmentDrawing]
      exact hx.1
    rcases joinedInner_edge_source (Q := Q) hR with hOld | hJoin
    · obtain ⟨A, hA, hRA⟩ := hOld
      obtain ⟨-, hAopen⟩ :=
        Q.crosscutOverlay_edge_dichotomy hs hJ hJgeom hwindow extra hA
      apply hAopen
      refine ⟨by
        rw [edgeArc_segmentDrawing]
        exact hRA hxSeg, ?_⟩
      intro hxOldVertex
      apply hx.2
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by
        rw [_root_.Graph.vertexSet_relabelEdges]
        exact Q.crosscutOverlayVertices_subset_joinedCrosscutOverlay
          hs hJ hjoins hxOldVertex)
    · obtain ⟨A, hA, hRA⟩ := hJoin
      exact hjoinsOpen (mem_cover_iff.2 ⟨A, hA, hRA hxSeg⟩)

/-- A joined edge meeting an old source cell away from joined vertices is absorbed by that old
source edge. -/
theorem graph_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → ∀ {f : γ}, f ∈ E(u.graph) →
      (_root_.Graph.edgeArc u.drawing f ∩ (P.src.cell e \ V(u.graph))).Nonempty →
      _root_.Graph.edgeArc u.drawing f ⊆ _root_.Graph.edgeArc P.src.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hzCell, hznot⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have heSrc : e ∈ E(P.src.graph) := by rwa [P.src.edgeSet_graph]
  apply (u.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen).edge_subset
    heSrc hf
  refine ⟨z, hzf, ?_, hznot⟩
  rw [P.src.cell_edge hab] at hzCell
  exact hzCell.1

/-- A join running from the open crosscut to the old nonboundary source carrier makes the
joined carrier connected after deletion of the wild outer curve. -/
theorem graph_isConnected_diff_of_join (hs : 0 < s)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg)
    {x y : Plane} (hxJ : x ∈ J.interior)
    (hySource : y ∈ P.src.skeletonSet \ srcOuter)
    (hArc : IsArcBetween (cover joins) x y) :
    IsConnected (_root_.Graph.pointSet u.graph u.drawing \ srcOuter) := by
  let Sset := P.src.skeletonSet \ srcOuter
  let Jset := J.seg \ srcOuter
  let Kset := _root_.Graph.pointSet
    (localGrid p s (localGridCount s epsilon)) segmentDrawing
  have hJinteriorConn : IsConnected J.interior :=
    (convex_openSegment J.1 J.2).isConnected
      ⟨midpoint ℝ J.1 J.2, midpoint_mem_openSegment J.1 J.2⟩
  have hJconn : IsConnected Jset := by
    apply hJinteriorConn.subset_closure
    · intro z hz
      exact ⟨openSegment_subset_segment ℝ _ _ hz, (hJgeom.interior_subset hz).2⟩
    · change J.seg \ srcOuter ⊆ closure (openSegment ℝ J.1 J.2)
      rw [closure_openSegment]
      exact sdiff_subset
  have hKconn : IsConnected Kset :=
    Schoenflies.Graph.IsDrawing.isConnected_pointSet
      (localGrid_isDrawing hs (one_le_localGridCount s epsilon))
      (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon)).connected
  have hKmiss : Kset ⊆ srcOuterᶜ := by
    intro z hzK hzOuter
    have hzCover : z ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hzK
    have hzWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hzCover
    exact (hwindow hzWindow).2 hzOuter
  have hcarrier : _root_.Graph.pointSet u.graph u.drawing \ srcOuter =
      ((Sset ∪ Jset) ∪ Kset) ∪ cover joins := by
    ext z
    rw [Set.mem_sdiff, Set.mem_union, Set.mem_union, Set.mem_union,
      Set.mem_sdiff, Set.mem_sdiff]
    constructor
    · rintro ⟨hzGraph, hzNotOuter⟩
      rw [u.graph_pointSet, w.graph_pointSet] at hzGraph
      rcases hzGraph with hzOld | hzJoin
      · rcases hzOld with hzOuter | hzRest
        · exact (hzNotOuter hzOuter).elim
        · rcases hzRest with hzCoreJ | hzGrid
          · rcases hzCoreJ with hzCore | hzJ
            · exact Or.inl (Or.inl (Or.inl ⟨by
                rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
                exact Or.inl hzCore, hzNotOuter⟩))
            · exact Or.inl (Or.inl (Or.inr ⟨hzJ, hzNotOuter⟩))
          · exact Or.inl (Or.inr (by
              simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hzGrid))
      · exact Or.inr hzJoin
    · rintro (⟨⟨⟨hzSource, hzNotOuter⟩ | ⟨hzJ, hzNotOuter⟩⟩ | hzK⟩ | hzJoin)
      · refine ⟨?_, hzNotOuter⟩
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hzSource
        rw [u.graph_pointSet, w.graph_pointSet]
        rcases hzSource with hzCore | hzOuter
        · exact Or.inl (Or.inr (Or.inl (Or.inl hzCore)))
        · exact Or.inl (Or.inl hzOuter)
      · exact ⟨by
          rw [u.graph_pointSet, w.graph_pointSet]
          exact Or.inl (Or.inr (Or.inl (Or.inr hzJ))), hzNotOuter⟩
      · exact ⟨by
          rw [u.graph_pointSet, w.graph_pointSet]
          exact Or.inl (Or.inr (Or.inr (by
            simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hzK))), hKmiss hzK⟩
      · exact ⟨by rw [u.graph_pointSet]; exact Or.inr hzJoin,
          (hjoinsOpen hzJoin).2⟩
  have hA1K : A.1 ∈ Kset := by
    apply _root_.Graph.edgeArc_subset_pointSet hA
    rw [edgeArc_segmentDrawing]
    exact left_mem_segment ℝ _ _
  have hA1J : A.1 ∈ Jset :=
    ⟨hAJ (left_mem_segment ℝ _ _), hKmiss hA1K⟩
  have hJK : IsConnected (Jset ∪ Kset) :=
    IsConnected.union ⟨A.1, hA1J, hA1K⟩ hJconn hKconn
  have hJoinConn : IsConnected (cover joins) := hArc.isArc.isConnected
  have hSourceJoin : IsConnected (Sset ∪ cover joins) :=
    IsConnected.union ⟨y, hySource, hArc.right_mem⟩ hsource hJoinConn
  have hxJset : x ∈ Jset :=
    ⟨openSegment_subset_segment ℝ _ _ hxJ, (hJgeom.interior_subset hxJ).2⟩
  have hAll : IsConnected ((Sset ∪ cover joins) ∪ (Jset ∪ Kset)) :=
    IsConnected.union ⟨x, Or.inr hArc.left_mem, Or.inl hxJset⟩ hSourceJoin hJK
  rw [hcarrier]
  convert hAll using 1
  ac_rfl

/-- The joined construction is a complete source extension. -/
theorem isSourceExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hjoins : ∀ R ∈ joins, R.Nondeg)
    (hjoinsOpen : cover joins ⊆ srcDom \ srcOuter)
    (hOldTwo : w.graph.IsTwoConnected)
    {x y : Plane} (hxy : x ≠ y) (hxEnd : x ∈ endSet joins)
    (hyEnd : y ∈ endSet joins) (hxOld : x ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hyOld : y ∈ _root_.Graph.pointSet w.graph w.drawing)
    (hArc : IsArcBetween (cover joins) x y)
    (hconnected : IsConnected
      (_root_.Graph.pointSet u.graph u.drawing \ srcOuter)) :
    IsSourceExtension P.src srcOuter srcDom u.graph u.drawing where
  finite := u.graph_finite
  isDrawing := u.graph_isDrawing hs hJ hJgeom hwindow hjoins hjoinsOpen
  isTwoConnected := u.graph_isTwoConnected_of_join hs hJ hJgeom hwindow
    hjoins hjoinsOpen hOldTwo hxy hxEnd hyEnd hxOld hyOld hArc
  vertexSet_subset :=
    (u.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)
      |>.vertexSet_subset
  skeletonSet_subset :=
    (u.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow hjoins hjoinsOpen)
      |>.pointSet_subset
  edge_subset := by
    intro e he f hf hmeet
    exact u.graph_edge_subset hs hJ hJgeom hwindow hjoins hjoinsOpen he hf hmeet
  pointSet_subset := u.graph_pointSet_subset hs hJgeom hwindow hjoinsOpen
  edge_dichotomy := by
    intro e he
    exact u.graph_edge_dichotomy hs hJ hJgeom hwindow hjoins hjoinsOpen he
  isConnected := hconnected

end JoinedCrosscutOverlayRelabeling

end SourceNonboundarySegmentCover

/-- The complete output of the boundary-crosscut joining construction. -/
structure JoinedLocalGridSourceExtensionData
    {F : γ} {A : Piece} (r : RefinedSourceFaceCrosscutData P F A)
    (p : Plane) (s epsilon : ℝ) where
  /-- Crosscut overlay before joining its components. -/
  oldOverlay : RefinedCrosscutOverlayData r p s epsilon
  /-- Polygonal segments joining the nonboundary components. -/
  joins : List Piece
  /-- Cell names for the overlay including the joining segments. -/
  joinedRelabeling :
    SourceNonboundarySegmentCover.JoinedCrosscutOverlayRelabeling
      oldOverlay.relabeling joins
  isSourceExtension :
    IsSourceExtension r.subdivision.pair.src srcOuter srcDom
      joinedRelabeling.graph joinedRelabeling.drawing
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet joinedRelabeling.graph joinedRelabeling.drawing

/-- Construct the manuscript's final polygonal component-joining ear.  A midpoint of the open
crosscut and a point of the connected old nonboundary carrier lie in the same open connected
source domain, so polygonal connectedness supplies a simple joining arc.  Re-overlaying its
segments and attaching its exact trace gives a complete local-grid source extension even when
both crosscut endpoints lie on the wild outer curve. -/
theorem RefinedCrosscutOverlayData.exists_joinedLocalGridSourceExtensionData
    [Infinite γ] {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    {r : RefinedSourceFaceCrosscutData P F A}
    (o : RefinedCrosscutOverlayData r p s epsilon)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hopen : IsOpen (srcDom \ srcOuter))
    (hconn : IsPreconnected (srcDom \ srcOuter))
    (hsource : IsConnected r.subdivision.pair.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (JoinedLocalGridSourceExtensionData r p s epsilon) := by
  let d := r.crosscutData
  let x : Plane := midpoint ℝ d.crosscut.1 d.crosscut.2
  have hxJ : x ∈ d.crosscut.interior := midpoint_mem_openSegment _ _
  have hxOpen : x ∈ srcDom \ srcOuter := r.geometry.interior_subset hxJ
  obtain ⟨y, hyNonboundary⟩ := hsource.nonempty
  have hySource : y ∈ r.subdivision.pair.src.skeletonSet \ srcOuter := by
    rwa [r.subdivision.pair.src_nonboundary_eq] at hyNonboundary
  have hyOpen : y ∈ srcDom \ srcOuter :=
    ⟨r.subdivision.pair.src_isWeaklyAdmissible.skeletonSet_subset hySource.1,
      hySource.2⟩
  have hxy : x ≠ y := by
    intro hxy
    have hxFace : x ∈ P.src.cell F := r.crosscutData.interior_subset_face hxJ
    have hyOldSource : y ∈ P.src.skeletonSet := by
      rw [← r.subdivision.skeletonSet_eq]
      exact hySource.1
    exact Set.disjoint_left.1
      (P.src.disjoint_cell_skeletonSet P.src_isCellDecomposition
        r.crosscutData.face_mem) hxFace (hxy ▸ hyOldSource)
  obtain ⟨vs, hvs, hhead, hlast, hpolyOpen, hpolyArc⟩ :=
    exists_simple_poly_of_isPreconnected hopen hconn hxOpen hyOpen hxy
  let joins := segsOf vs
  have hxPoly : x ∈ poly vs := hpolyArc.left_mem
  have hyPoly : y ∈ poly vs := hpolyArc.right_mem
  have hcover : Schoenflies.cover joins = poly vs :=
    cover_segsOf_eq hxPoly hyPoly hxy
  have hjoins : ∀ R ∈ joins, R.Nondeg := segsOf_nondeg vs
  have hjoinsOpen : Schoenflies.cover joins ⊆ srcDom \ srcOuter := by
    rw [hcover]
    exact hpolyOpen
  have hjoinArc : IsArcBetween (Schoenflies.cover joins) x y := by
    rw [hcover]
    exact hpolyArc
  have hHeadLastNe : vs.head hvs ≠ vs.getLast hvs := by
    rw [hhead, hlast]
    exact hxy
  obtain ⟨hheadEnd, hlastEnd⟩ :=
    head_getLast_mem_endSet_segsOf hvs hHeadLastNe
  have hxEnd : x ∈ endSet joins := by
    rw [← hhead]
    exact hheadEnd
  have hyEnd : y ∈ endSet joins := by
    rw [← hlast]
    exact hlastEnd
  obtain ⟨u⟩ := o.relabeling.exists_joinedRelabeling joins
  have hxOld : x ∈ _root_.Graph.pointSet o.relabeling.graph o.relabeling.drawing := by
    rw [o.relabeling.graph_pointSet]
    exact Or.inr (Or.inl (Or.inr
      (openSegment_subset_segment ℝ _ _ hxJ)))
  have hyOld : y ∈ _root_.Graph.pointSet o.relabeling.graph o.relabeling.drawing :=
    o.relabeling.sourceSkeleton_subset_graph hySource.1
  have hsource' : IsConnected
      (r.subdivision.pair.src.skeletonSet \ srcOuter) := by
    rwa [r.subdivision.pair.src_nonboundary_eq] at hsource
  have hconnected : IsConnected
      (_root_.Graph.pointSet u.graph u.drawing \ srcOuter) :=
    u.graph_isConnected_diff_of_join hs r.geometry hwindow hsource'
      hjoinsOpen hA r.crosscutData.grid_subset hxJ hySource hjoinArc
  exact ⟨{
    oldOverlay := o
    joins := joins
    joinedRelabeling := u
    isSourceExtension :=
      u.isSourceExtension hs r.crosscutData.nondeg r.geometry hwindow
        hjoins hjoinsOpen o.isTwoConnected hxy hxEnd hyEnd hxOld hyOld
        hjoinArc hconnected
    localGrid_subset := o.localGrid_subset.trans (by
      rw [u.graph_pointSet]
      exact subset_union_left)
  }⟩

/-- Complete the boundary-touching local-grid attachment starting only from a bounded source
face and a grid edge whose relative interior lies on a line through that face.  The preliminary
matched subdivision preserves the old source carrier, so connectedness of the original
nonboundary source graph is exactly the connectedness needed by the polygonal joining step. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData
    [Infinite γ] {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hopen : IsOpen (srcDom \ srcOuter))
    (hconn : IsPreconnected (srcDom \ srcOuter))
    (hsource : IsConnected P.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (Σ r : RefinedSourceFaceCrosscutData P F A,
      JoinedLocalGridSourceExtensionData r p s epsilon) := by
  obtain ⟨⟨r, o⟩⟩ := P.exists_refinedCrosscutOverlayData
    hF hFbdd hab hAline hy hs hwindow hA
  have hrsource : IsConnected r.subdivision.pair.src.nonboundary := by
    rw [r.subdivision.pair.src_nonboundary_eq, r.subdivision.skeletonSet_eq,
      ← P.src_nonboundary_eq]
    exact hsource
  obtain ⟨j⟩ := o.exists_joinedLocalGridSourceExtensionData
    hs hwindow hopen hconn hrsource hA
  exact ⟨⟨r, j⟩⟩

/-- In the actual Schönflies source domain, the hypotheses needed to draw the final joining
arc are automatic consequences of Jordan separation: the closed domain minus its boundary is
the connected open inside region. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData_inside
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (Σ r : RefinedSourceFaceCrosscutData P F A,
      JoinedLocalGridSourceExtensionData r p s epsilon) := by
  apply P.exists_joinedLocalGridSourceExtensionData hF hFbdd hab hAline hy
    hs hwindow
  · rw [union_inside_sdiff]
    exact hC.isOpen_inside
  · rw [union_inside_sdiff]
    exact hC.isConnected_inside.isPreconnected
  · exact hsource
  · exact hA

/-- Every point in the relative interior of a horizontal grid edge has the row's fixed second
coordinate. -/
theorem gridHEdge_interior_snd {xc yc : ℕ → ℝ} {i j : ℕ} {z : Plane}
    (hz : z ∈ (gridHEdge xc yc i j).interior) : z 1 = yc j := by
  change z ∈ openSegment ℝ (gridPt xc yc i j) (gridPt xc yc (i + 1) j) at hz
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, -, rfl⟩ := hz
  simp [AffineMap.lineMap_apply, gridPt]

/-- The relative interiors of a local grid's bottom and top leftmost edges are disjoint. -/
theorem localGrid_horizontal_extremes_interior_disjoint
    {p : Plane} {s : ℝ} {k : ℕ} (hs : 0 < s) (hk : 1 ≤ k) :
    Disjoint
      (gridHEdge (localGridX p s k) (localGridY p s k) 0 0).interior
      (gridHEdge (localGridX p s k) (localGridY p s k) 0 k).interior := by
  rw [Set.disjoint_left]
  intro z hzBottom hzTop
  have hzBottomCoord := gridHEdge_interior_snd hzBottom
  have hzTopCoord := gridHEdge_interior_snd hzTop
  have hrows : localGridY p s k 0 ≠ localGridY p s k k :=
    ne_of_lt ((localGridY_strictMono hs hk) (by omega))
  exact hrows (hzBottomCoord.symm.trans hzTopCoord)

/-- If the complete source/grid intersection has at most one point, at least one of two
opposite horizontal grid edges has relative interior disjoint from the source skeleton. -/
theorem GeneratedPair.exists_localGridEdge_interior_disjoint_of_common_subsingleton
    {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (hcommon :
      (P.src.skeletonSet ∩
        _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
          segmentDrawing).Subsingleton) :
    ∃ A ∈ E(localGrid p s (localGridCount s epsilon)),
      Disjoint A.interior P.src.skeletonSet := by
  classical
  let k := localGridCount s epsilon
  let A₀ := gridHEdge (localGridX p s k) (localGridY p s k) 0 0
  let A₁ := gridHEdge (localGridX p s k) (localGridY p s k) 0 k
  have hk : 1 ≤ k := one_le_localGridCount s epsilon
  have hA₀List : A₀ ∈ localGridEdges p s k := by
    change A₀ ∈ gridEdges (localGridX p s k) (localGridY p s k) k k
    exact gridHEdge_mem_gridEdges (by omega) (Nat.zero_le k) hk
  have hA₁List : A₁ ∈ localGridEdges p s k := by
    change A₁ ∈ gridEdges (localGridX p s k) (localGridY p s k) k k
    exact gridHEdge_mem_gridEdges (by omega) (le_refl k) hk
  have hA₀ : A₀ ∈ E(localGrid p s k) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA₀List
  have hA₁ : A₁ ∈ E(localGrid p s k) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA₁List
  by_cases hdisj₀ : Disjoint A₀.interior P.src.skeletonSet
  · exact ⟨A₀, hA₀, hdisj₀⟩
  · have hdisj₁ : Disjoint A₁.interior P.src.skeletonSet := by
      by_contra hnot
      rw [Set.disjoint_left] at hdisj₀ hnot
      push Not at hdisj₀ hnot
      obtain ⟨z₀, hz₀Int, hz₀Source⟩ := hdisj₀
      obtain ⟨z₁, hz₁Int, hz₁Source⟩ := hnot
      have hz₀Grid : z₀ ∈ _root_.Graph.pointSet (localGrid p s k) segmentDrawing := by
        rw [localGrid_eq, pieceListGraph_pointSet]
        exact mem_cover_iff.2 ⟨A₀, hA₀List,
          openSegment_subset_segment ℝ _ _ hz₀Int⟩
      have hz₁Grid : z₁ ∈ _root_.Graph.pointSet (localGrid p s k) segmentDrawing := by
        rw [localGrid_eq, pieceListGraph_pointSet]
        exact mem_cover_iff.2 ⟨A₁, hA₁List,
          openSegment_subset_segment ℝ _ _ hz₁Int⟩
      have hzEq : z₀ = z₁ :=
        hcommon ⟨hz₀Source, hz₀Grid⟩ ⟨hz₁Source, hz₁Grid⟩
      exact Set.disjoint_left.1
        (localGrid_horizontal_extremes_interior_disjoint hs hk)
        hz₀Int (hzEq ▸ hz₁Int)
    exact ⟨A₁, hA₁, hdisj₁⟩

/-- In the two-common-point branch, retaining those points explicitly in the raw source/grid
overlay gives the complete local-grid source extension directly. -/
theorem GeneratedPair.exists_localGridSourceExtensionData_of_common_not_subsingleton
    [Infinite γ] {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected P.src.nonboundary)
    (hcommon : ¬(P.src.skeletonSet ∩
      _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
        segmentDrawing).Subsingleton) :
    Nonempty (LocalGridSourceExtensionData P p s epsilon) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hcommon
  obtain ⟨Q⟩ := P.exists_sourceNonboundarySegmentCover
  obtain ⟨w⟩ := Q.exists_localOverlayRelabeling p s epsilon [a, b]
  have commonVertex : ∀ {x : Plane}, x ∈ [a, b] →
      x ∈ P.src.skeletonSet →
      x ∈ _root_.Graph.pointSet
        (localGrid p s (localGridCount s epsilon)) segmentDrawing →
      x ∈ V(w.graph) := by
    intro x hxList hxSource hxGrid
    have hxCover : x ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [localGrid_eq, pieceListGraph_pointSet] using hxGrid
    have hxWindow : x ∈ Plane.closedSquare p s :=
      SourceNonboundarySegmentCover.cover_localGridEdges_subset_closedSquare hs
        (one_le_localGridCount s epsilon) hxCover
    have hxNotOuter : x ∉ srcOuter := (hwindow hxWindow).2
    have hxCore : x ∈
        _root_.Graph.pointSet P.sourceNonboundaryGraph P.src.drawing := by
      rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSource
      exact hxSource.resolve_right hxNotOuter
    change x ∈ V(w.outerGraph.union w.innerGraph)
    rw [_root_.Graph.vertexSet_union]
    refine Or.inr ?_
    rw [_root_.Graph.vertexSet_relabelEdges]
    change x ∈ V(overlayGraph (Q.localPieces p s epsilon)
      (attachPoints (Q.localPieces p s epsilon)
        ([a, b] ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
    apply overlayGraph_mem_vertexSet_of_mem_cover (Q.localPieces_nondeg hs)
    · exact mem_attachPoints_of_mem (List.mem_append_left _ hxList)
    · change x ∈ cover (Q.pieces ++
        localGridEdges p s (localGridCount s epsilon))
      rw [cover_append, Q.cover_eq]
      exact Or.inl hxCore
  have haV : a ∈ V(w.graph) := commonVertex (by simp) ha.1 ha.2
  have hbV : b ∈ V(w.graph) := commonVertex (by simp) hb.1 hb.2
  exact ⟨{
    graph := w.graph
    drawing := w.drawing
    isSourceExtension :=
      w.isSourceExtension_of_source_connected_two_common hs hwindow hsource
        hab haV hbV ha.1 hb.1 ha.2 hb.2
    localGrid_subset := w.localGrid_subset_graph
  }⟩

/-- A raw grid edge whose open segment misses the current source skeleton lies in one bounded
source face.  Thus it supplies all of the face-selection data required by the auxiliary
crosscut and joining construction. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData_of_disjoint_edge
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hdisj : Disjoint A.interior P.src.skeletonSet) :
    Nonempty (Σ F : γ, Σ r : RefinedSourceFaceCrosscutData P F A,
      JoinedLocalGridSourceExtensionData r p s epsilon) := by
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hAne : A.Nondeg :=
    localGridEdges_nondeg hs (one_le_localGridCount s epsilon) A hAList
  have hADom : A.interior ⊆ C ∪ inside C := by
    intro z hz
    exact (hwindow (SourceNonboundarySegmentCover.cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hAList, openSegment_subset_segment ℝ _ _ hz⟩))).1
  obtain ⟨F, hF, hAF, -⟩ :=
    P.src_isCellDecomposition.exists_unique_face_subset_cell
      (P.src_isCellDecomposition.cellsAbsorb P.src_isFaceJordan)
      (convex_openSegment A.1 A.2).isPreconnected
      ⟨midpoint ℝ A.1 A.2, midpoint_mem_openSegment A.1 A.2⟩
      hADom hdisj
  have hAline : A.interior ⊆ Plane.line A.1 A.2 ∩ P.src.cell F := by
    intro z hz
    refine ⟨?_, hAF hz⟩
    change z ∈ openSegment ℝ A.1 A.2 at hz
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t, -, rfl⟩ := hz
    exact Plane.lineMap_mem_line A.1 A.2 t
  obtain ⟨⟨r, j⟩⟩ := P.exists_joinedLocalGridSourceExtensionData_inside
    hC hF (P.src_isFaceJordan.isBounded hF) hAne hAline
      (midpoint_mem_openSegment A.1 A.2) hs hwindow hsource hA
  exact ⟨⟨F, r, j⟩⟩

/-- The at-most-one-common-point branch automatically supplies a skeleton-disjoint grid edge,
so the completed face-crosscut and joining construction applies without further choices. -/
theorem GeneratedPair.exists_joinedLocalGridSourceExtensionData_of_common_subsingleton
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary)
    (hcommon :
      (P.src.skeletonSet ∩
        _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
          segmentDrawing).Subsingleton) :
    Nonempty (Σ F : γ, Σ A : Piece,
      Σ r : RefinedSourceFaceCrosscutData P F A,
        JoinedLocalGridSourceExtensionData r p s epsilon) := by
  obtain ⟨A, hA, hdisj⟩ :=
    P.exists_localGridEdge_interior_disjoint_of_common_subsingleton hs hcommon
  obtain ⟨⟨F, r, j⟩⟩ :=
    P.exists_joinedLocalGridSourceExtensionData_of_disjoint_edge
      hC hs hwindow hsource hA hdisj
  exact ⟨⟨F, A, r, j⟩⟩

/-- Exhaustive local-grid attachment.  With two distinct source/grid intersection points the
raw overlay extends the current pair directly.  Otherwise a raw grid edge misses the skeleton
in its relative interior, and a matched endpoint subdivision followed by the crosscut and
polygonal joining ears produces the extension. -/
theorem GeneratedPair.exists_localGridSourceExtensionData_cases
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary) :
    Nonempty (LocalGridSourceExtensionData P p s epsilon) ∨
      Nonempty (Σ F : γ, Σ A : Piece,
        Σ r : RefinedSourceFaceCrosscutData P F A,
          JoinedLocalGridSourceExtensionData r p s epsilon) := by
  classical
  by_cases hcommon :
      (P.src.skeletonSet ∩
        _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
          segmentDrawing).Subsingleton
  · exact Or.inr
      (P.exists_joinedLocalGridSourceExtensionData_of_common_subsingleton
        hC hs hwindow hsource hcommon)
  · exact Or.inl
      (P.exists_localGridSourceExtensionData_of_common_not_subsingleton
        hs hwindow hsource hcommon)

namespace GeneratedPair.SubdivideSetData

/-- A matched finite source-skeleton subdivision is already a stage transition. -/
theorem stageTransition {s : Set Plane} (r : GeneratedPair.SubdivideSetData P s) :
    StageTransition r.pair P r.parent where
  refines_src := r.refines_src
  refines_tgt := r.refines_tgt
  sourceSkeletonSet_subset := by
    rw [r.skeletonSet_eq]
  homeo_eqOn := r.homeo_eqOn

end GeneratedPair.SubdivideSetData

/-- The uniform stage-level output of local-grid attachment, after running forward finite
transfer.  Both geometric branches now return one generated refinement of the original pair,
with admissibility restored and the complete raw local grid in its source skeleton. -/
structure LocalGridForwardStageData {C : Set Plane}
    (P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom)
    (p : Plane) (s epsilon : ℝ) where
  /-- Generated matched pair after the local-grid transfer. -/
  pair : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom
  /-- Parent cell of each cell in the refinement. -/
  parent : γ → γ
  transition : StageTransition pair P parent
  src_isAdmissible : pair.src.IsAdmissible C (C ∪ inside C)
  tgt_isAdmissible : pair.tgt.IsAdmissible tgtOuter tgtDom
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      pair.src.skeletonSet

/-- **Local-grid forward successor.** The source/grid intersection dichotomy,
the auxiliary face crosscut, endpoint subdivisions, polygonal joining ear, and forward finite
transfer are all internal. -/
theorem GeneratedPair.exists_localGridForwardStageData
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) tgtOuter tgtDom}
    {p : Plane} {s epsilon : ℝ}
    (hC : IsSeparating C)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    (hsource : IsConnected P.src.nonboundary) :
    Nonempty (LocalGridForwardStageData P p s epsilon) := by
  rcases P.exists_localGridSourceExtensionData_cases hC hs hwindow hsource with
    hdirect | hrefined
  · obtain ⟨d⟩ := hdirect
    obtain ⟨T, par, hT⟩ :=
      finite_transfer_toward_square d.isSourceExtension
    exact ⟨{
      pair := T
      parent := par
      transition := hT.stageTransition
      src_isAdmissible := hT.src_isAdmissible
      tgt_isAdmissible := hT.tgt_isAdmissible
      localGrid_subset := by
        rw [hT.skeletonSet_eq]
        exact d.localGrid_subset
    }⟩
  · obtain ⟨⟨F, A, r, j⟩⟩ := hrefined
    obtain ⟨T, par, hT⟩ :=
      finite_transfer_toward_square j.isSourceExtension
    exact ⟨{
      pair := T
      parent := r.subdivision.parent ∘ par
      transition := hT.stageTransition.trans r.subdivision.stageTransition
      src_isAdmissible := hT.src_isAdmissible
      tgt_isAdmissible := hT.tgt_isAdmissible
      localGrid_subset := by
        rw [hT.skeletonSet_eq]
        exact j.localGrid_subset
    }⟩

end Schoenflies
