/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SourceOverlay

/-!
# Auxiliary-crosscut source overlays

A local window can miss the current skeleton, so the raw source/grid overlay need not have the
two common vertices required for 2-connectivity.  The degenerate cases of
`prop:local-grid-attachment` add one polygonal crosscut of the containing face.  This module
builds the corresponding finite straight-line inner overlay while keeping the original wild
outer curve separate.

## Blueprint

* `Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay` — the old compact nonboundary
  carrier, one auxiliary crosscut, and the local grid in a single exact segment overlay.
* `crosscutOverlay_pointSet` — its exact carrier.
* `crosscutOverlay_isDrawing`, `crosscutOverlay_pointSet_subset`, and
  `crosscutOverlay_edge_dichotomy` — the local plane and domain geometry needed by finite
  transfer.
-/

public section

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

/-- Every source face of a generated pair lies in the prescribed open source domain. -/
theorem GeneratedPair.src_face_subset_interior {F : γ} (hF : F ∈ P.str.faces) :
    P.src.cell F ⊆ srcDom \ srcOuter := by
  intro x hx
  refine ⟨P.src_isCellDecomposition.cell_subset_domain
    (P.str.mem_cells_of_mem_faces hF) hx, ?_⟩
  intro hxOuter
  have hxSkel : x ∈ P.src.skeletonSet := by
    rw [← P.src_isWeaklyAdmissible.outerSet_eq] at hxOuter
    exact P.src.outerSet_subset_skeletonSet hxOuter
  exact Set.disjoint_left.1
    (P.src.disjoint_cell_skeletonSet P.src_isCellDecomposition hF) hx hxSkel

/-- The geometric output of cutting a bounded source face along the line carrying a selected
grid edge.  The closed crosscut swallows that edge; its open part lies in the face and both ends
lie on the old source skeleton. -/
structure SourceFaceCrosscutData (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (F : γ) (A : Piece) where
  face_mem : F ∈ P.str.faces
  /-- Closed segment spanning the selected source face. -/
  crosscut : Piece
  nondeg : crosscut.Nondeg
  left_mem_frontier : crosscut.1 ∈ frontier (P.src.cell F)
  right_mem_frontier : crosscut.2 ∈ frontier (P.src.cell F)
  left_mem_skeleton : crosscut.1 ∈ P.src.skeletonSet
  right_mem_skeleton : crosscut.2 ∈ P.src.skeletonSet
  interior_subset_face : crosscut.interior ⊆ P.src.cell F
  grid_subset : A.seg ⊆ crosscut.seg

namespace SourceFaceCrosscutData

variable {F : γ} {A : Piece}

/-- If the selected face has no wild-boundary points on its frontier, the entire closed
crosscut lies in the open source domain. -/
theorem seg_subset_interior (d : SourceFaceCrosscutData P F A)
    (hfrontier : frontier (P.src.cell F) ⊆ srcDom \ srcOuter) :
    d.crosscut.seg ⊆ srcDom \ srcOuter := by
  intro x hx
  by_cases hxLeft : x = d.crosscut.1
  · exact hfrontier (hxLeft ▸ d.left_mem_frontier)
  by_cases hxRight : x = d.crosscut.2
  · exact hfrontier (hxRight ▸ d.right_mem_frontier)
  exact P.src_face_subset_interior d.face_mem (d.interior_subset_face
      (mem_openSegment_of_ne_left_right (Ne.symm hxLeft) (Ne.symm hxRight) hx))

end SourceFaceCrosscutData

/-- A line through the relative interior of a selected grid edge in a bounded source face
produces the exact auxiliary-crosscut data used by the mixed source overlay. -/
theorem GeneratedPair.exists_sourceFaceCrosscutData {F : γ} {A : Piece}
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior) :
    Nonempty (SourceFaceCrosscutData P F A) := by
  obtain ⟨q₀, q₁, hne, hq₀, hq₁, hinterior, -, hswallow⟩ :=
    exists_crosscut hab (P.src_isFaceJordan.isOpen hF) hFbdd (hAline hy)
  have hfrontier :=
    P.src_isCellDecomposition.frontier_cell_subset_skeletonSet P.src_isFaceJordan hF
  exact ⟨{
    face_mem := hF
    crosscut := (q₀, q₁)
    nondeg := hne
    left_mem_frontier := hq₀
    right_mem_frontier := hq₁
    left_mem_skeleton := hfrontier hq₀
    right_mem_skeleton := hfrontier hq₁
    interior_subset_face := hinterior
    grid_subset := seg_subset_crosscut hswallow hAline hy
  }⟩

/-- The exact geometry needed to adjoin a straight crosscut to a source drawing.  Its interior
is disjoint from the wild boundary; an endpoint is allowed on that boundary precisely when it
is already a source vertex (as happens after subdividing the endpoint into the old skeleton). -/
structure SourceCrosscutGeometry
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (J : Piece) : Prop where
  seg_subset_domain : J.seg ⊆ srcDom
  interior_subset : J.interior ⊆ srcDom \ srcOuter
  left_vertex_of_mem_outer : J.1 ∈ srcOuter → J.1 ∈ V(P.src.graph)
  right_vertex_of_mem_outer : J.2 ∈ srcOuter → J.2 ∈ V(P.src.graph)

namespace SourceCrosscutGeometry

/-- A crosscut whose complete closed segment lies in the open domain automatically satisfies
the boundary-endpoint condition. -/
theorem of_seg_subset_interior {J : Piece} (hJopen : J.seg ⊆ srcDom \ srcOuter) :
    SourceCrosscutGeometry P J where
  seg_subset_domain := hJopen.trans sdiff_subset
  interior_subset := (openSegment_subset_segment ℝ _ _).trans hJopen
  left_vertex_of_mem_outer h :=
    ((hJopen (left_mem_segment ℝ _ _)).2 h).elim
  right_vertex_of_mem_outer h :=
    ((hJopen (right_mem_segment ℝ _ _)).2 h).elim

end SourceCrosscutGeometry

/-- A source vertex lying on the realized outer set is already a vertex of the mapped outer
graph. -/
theorem GeneratedPair.sourceVertex_mem_outerGraph {x : Plane}
    (hxV : x ∈ V(P.src.graph)) (hxOuter : x ∈ srcOuter) :
    x ∈ V(P.str.outerGraph.map P.src.pos) := by
  rw [← P.src_isWeaklyAdmissible.outerSet_eq] at hxOuter
  rcases hxOuter with hxOuterV | hxOuterE
  · exact hxOuterV
  · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxOuterE
    obtain ⟨a, b, hab⟩ :=
      (P.str.outerGraph.map P.src.pos).exists_isLink_of_mem_edgeSet he
    have habSrc := (P.str.outerGraph_le.map P.src.pos).isLink_mono hab
    rcases P.src.isDrawing.vertex_mem_edgeArc habSrc hxV hxe with rfl | rfl
    · exact hab.left_mem
    · exact hab.right_mem

/-- A face crosscut together with the preliminary matched subdivision that makes both of its
endpoints old source vertices.  This is the representation needed when either endpoint lands
in the interior of a wild outer edge. -/
structure RefinedSourceFaceCrosscutData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (F : γ) (A : Piece) where
  /-- Crosscut geometry before refining its endpoints. -/
  crosscutData : SourceFaceCrosscutData P F A
  /-- Matched subdivision making both crosscut endpoints vertices. -/
  subdivision : GeneratedPair.SubdivideSetData P
    ({crosscutData.crosscut.1, crosscutData.crosscut.2} : Set Plane)
  geometry : SourceCrosscutGeometry subdivision.pair crosscutData.crosscut

/-- Every source-face crosscut admits a matched preliminary subdivision at its two endpoints.
The construction is harmless when an endpoint was already a vertex and essential when it lies
inside a wild outer edge. -/
theorem SourceFaceCrosscutData.exists_refinement [Infinite γ]
    {F : γ} {A : Piece} (d : SourceFaceCrosscutData P F A) :
    Nonempty (RefinedSourceFaceCrosscutData P F A) := by
  have hendsFinite : ({d.crosscut.1, d.crosscut.2} : Set Plane).Finite :=
    Set.toFinite _
  have hendsSource : ({d.crosscut.1, d.crosscut.2} : Set Plane) ⊆
      P.src.skeletonSet := by
    intro x hx
    rcases hx with rfl | hx
    · exact d.left_mem_skeleton
    · simpa only [Set.mem_singleton_iff] using hx ▸ d.right_mem_skeleton
  obtain ⟨r⟩ := P.exists_subdivideSetData hendsFinite hendsSource
  have hgeom : SourceCrosscutGeometry r.pair d.crosscut := by
    refine {
      seg_subset_domain := ?_
      interior_subset := ?_
      left_vertex_of_mem_outer := fun _ => r.vertexSet_subset
        (Set.mem_insert d.crosscut.1 {d.crosscut.2})
      right_vertex_of_mem_outer := fun _ => r.vertexSet_subset
        (Set.mem_insert_of_mem d.crosscut.1 (Set.mem_singleton d.crosscut.2))
    }
    · intro x hx
      by_cases hxLeft : x = d.crosscut.1
      · exact P.src_isWeaklyAdmissible.skeletonSet_subset
          (hxLeft ▸ d.left_mem_skeleton)
      by_cases hxRight : x = d.crosscut.2
      · exact P.src_isWeaklyAdmissible.skeletonSet_subset
          (hxRight ▸ d.right_mem_skeleton)
      exact (P.src_face_subset_interior d.face_mem
        (d.interior_subset_face
          (mem_openSegment_of_ne_left_right (Ne.symm hxLeft) (Ne.symm hxRight) hx))).1
    · exact d.interior_subset_face |>.trans (P.src_face_subset_interior d.face_mem)
  exact ⟨{
    crosscutData := d
    subdivision := r
    geometry := hgeom
  }⟩

namespace SourceNonboundarySegmentCover

variable (Q : SourceNonboundarySegmentCover P)

/-- The source pieces after adjoining one auxiliary crosscut and one local grid. -/
noncomputable def crosscutPieces (J : Piece) (p : Plane) (s epsilon : ℝ) : List Piece :=
  (Q.pieces ++ [J]) ++ localGridEdges p s (localGridCount s epsilon)

/-- The finite straight-line overlay of the old compact source core, an auxiliary crosscut,
and the local grid.  Old nonboundary vertices and prescribed points are retained. -/
noncomputable def crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : Graph Plane Piece :=
  attachGraph (Q.crosscutPieces J p s epsilon)
    (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)

instance crosscutOverlay_finite (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : (Q.crosscutOverlay J p s epsilon extra).Finite :=
  attachGraph_finite _ _

/-- Every source piece in the crosscut overlay is nondegenerate. -/
theorem crosscutPieces_nondeg {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) :
    ∀ R ∈ Q.crosscutPieces J p s epsilon, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · rcases List.mem_append.1 hR with hR | hR
    · exact Q.nondeg R hR
    · rw [List.mem_singleton] at hR
      subst R
      exact hJ
  · exact localGridEdges_nondeg hs (one_le_localGridCount s epsilon) R hR

/-- The auxiliary-crosscut overlay is a finite straight-line plane graph. -/
theorem crosscutOverlay_isDrawing {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    Graph.IsDrawing (Q.crosscutOverlay J p s epsilon extra) segmentDrawing :=
  attachGraph_isDrawing (Q.crosscutPieces_nondeg hs hJ) _

/-- The crosscut overlay occupies exactly the old compact source carrier, the auxiliary
segment, and the local grid. -/
theorem crosscutOverlay_pointSet (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing =
      (Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪ J.seg) ∪
        cover (localGridEdges p s (localGridCount s epsilon)) := by
  rw [crosscutOverlay, attachGraph_pointSet, crosscutPieces, cover_append,
    cover_append, Q.cover_eq]
  simp only [cover_cons, cover_nil, Set.union_empty]

/-- The old compact source core survives in the auxiliary-crosscut overlay. -/
theorem sourceCore_subset_crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ⊆
      Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing := by
  rw [Q.crosscutOverlay_pointSet]
  exact subset_union_left.trans subset_union_left

/-- The entire auxiliary segment survives in the overlay. -/
theorem crosscut_subset_crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    J.seg ⊆ Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing := by
  rw [Q.crosscutOverlay_pointSet]
  exact subset_union_right.trans subset_union_left

/-- The entire local grid survives in the auxiliary-crosscut overlay. -/
theorem localGrid_subset_crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    cover (localGridEdges p s (localGridCount s epsilon)) ⊆
      Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing := by
  rw [Q.crosscutOverlay_pointSet]
  exact subset_union_right

/-- Every old compact-core vertex is retained by the auxiliary-crosscut overlay. -/
theorem sourceCoreVertices_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    V(P.sourceNonboundaryGraph) ⊆ V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right extra (by
      rw [Finset.mem_toList, Graph.mem_vertexFinset]
      exact hx)
  · rw [crosscutPieces, cover_append, cover_append, Q.cover_eq]
    exact Or.inl (Or.inl (Graph.vertexSet_subset_pointSet hx))

/-- Both endpoints of the auxiliary crosscut are overlay vertices. -/
theorem crosscutEnds_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ({J.1, J.2} : Set Plane) ⊆ V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · exact attachPoints_endsAreCut _ _ J
      (List.mem_append_left _ (List.mem_append_right Q.pieces (List.mem_singleton_self J)))
      x hx
  · exact mem_cover_iff.2 ⟨J,
      List.mem_append_left _ (List.mem_append_right Q.pieces (List.mem_singleton_self J)), by
        rcases hx with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩

/-- Every raw local-grid vertex is retained by the auxiliary-crosscut overlay. -/
theorem localGridVertices_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    V(localGrid p s (localGridCount s epsilon)) ⊆
      V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  rw [localGrid_eq, pieceListGraph_vertexSet] at hx
  simp only [endSet, Set.mem_ofPred_eq] at hx
  obtain ⟨R, hR, hxR⟩ := hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right (Q.pieces ++ [J]) hR) x hxR
  · exact mem_cover_iff.2 ⟨R, List.mem_append_right (Q.pieces ++ [J]) hR, by
      rcases hxR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _⟩

/-- Every overlay edge is cut from the old compact cover, the auxiliary crosscut, or the local
grid. -/
theorem crosscutOverlay_edge_source {J : Piece} {p : Plane} {s epsilon : ℝ}
    {extra : List Plane} {R : Piece} (hR : R ∈ E(Q.crosscutOverlay J p s epsilon extra)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      R.seg ⊆ J.seg ∨
        ∃ A ∈ localGridEdges p s (localGridCount s epsilon), R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hGrid
  · rcases List.mem_append.1 hA with hOld | hCrosscut
    · exact Or.inl ⟨A, hOld, hsub⟩
    · rw [List.mem_singleton] at hCrosscut
      exact Or.inr (Or.inl (hCrosscut ▸ hsub))
  · exact Or.inr (Or.inr ⟨A, hGrid, hsub⟩)

/-- If both the crosscut and the window lie in the open source domain, the entire auxiliary
overlay lies in the closed source domain. -/
theorem crosscutOverlay_pointSet_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJdom : J.seg ⊆ srcDom)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing ⊆ srcDom := by
  rw [Q.crosscutOverlay_pointSet]
  apply Set.union_subset
  · apply Set.union_subset
    · exact (Graph.pointSet_mono P.sourceNonboundaryGraph_le).trans
        P.src_isWeaklyAdmissible.skeletonSet_subset
    · exact hJdom
  · exact (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)).trans (hwindow.trans sdiff_subset)

/-- Every auxiliary-overlay edge is polygonal and has all nonvertex points in the open source
domain. -/
theorem crosscutOverlay_edge_dichotomy {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    ∀ {R : Piece}, R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      IsPolygonal (_root_.Graph.edgeArc segmentDrawing R) ∧
        _root_.Graph.edgeArc segmentDrawing R \ V(Q.crosscutOverlay J p s epsilon extra) ⊆
          srcDom \ srcOuter := by
  intro R hR
  refine ⟨by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _, ?_⟩
  intro x hx
  have hxSeg : x ∈ R.seg := by
    rw [← edgeArc_segmentDrawing]
    exact hx.1
  rcases Q.crosscutOverlay_edge_source hR with hOld | hCrosscut | hGrid
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, heNotOuter, hAe⟩ := Q.source A hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hxe : x ∈ _root_.Graph.edgeArc P.src.drawing e := hAe (hRA hxSeg)
    have hxCell : x ∈ P.src.cell e := by
      rw [P.src.cell_edge hab]
      refine ⟨hxe, ?_⟩
      intro hxEnds
      have habSrc := hab.map P.src.pos
      rcases hxEnds with hxa | hxb
      · apply hx.2
        rw [hxa]
        apply Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_left⟩
      · apply hx.2
        rw [hxb]
        apply Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_right⟩
    exact P.src_isWeaklyAdmissible.cell_subset he heNotOuter hxCell
  · have hxLeft : x ≠ J.1 := by
      intro h
      apply hx.2
      rw [h]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert J.1 {J.2})
    have hxRight : x ≠ J.2 := by
      intro h
      apply hx.2
      rw [h]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
    exact hJgeom.interior_subset
      (mem_openSegment_of_ne_left_right (Ne.symm hxLeft) (Ne.symm hxRight)
        (hCrosscut hxSeg))
  · obtain ⟨A, hA, hRA⟩ := hGrid
    exact hwindow (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hA, hRA hxSeg⟩))

/-- Away from overlay vertices, an auxiliary-overlay edge meeting an old open nonboundary edge
is one of that edge's subdivision pieces. -/
theorem crosscutOverlay_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → e ∉ E(P.str.outerGraph) → ∀ {R : Piece},
      R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (P.src.cell e \ V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc P.src.drawing e := by
  intro e he heOuter R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ _root_.Graph.edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  have hzCore : z ∈ Graph.pointSet P.sourceNonboundaryGraph P.src.drawing :=
    Graph.edgeArc_subset_pointSet
      (sourceNonboundaryGraph_edge_mem (P := P) he heOuter) hzOldArc
  have hzCover : z ∈ cover Q.pieces := by rwa [Q.cover_eq]
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, -, hAg⟩ := Q.source A hA
  have hzg : z ∈ _root_.Graph.edgeArc P.src.drawing g := hAg hzA
  have hznotOldVertex : z ∉ V(P.src.graph) := by
    intro hzV
    rcases P.src.isDrawing.vertex_mem_edgeArc (hab.map P.src.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have heg : e = g := P.src.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ _root_.Graph.edgeArc P.src.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A)
      (List.mem_append_left _ (List.mem_append_left [J] hA)) hzA
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-- Away from overlay vertices, an auxiliary-overlay edge meeting a raw local-grid edge is one
of that edge's subdivision pieces. -/
theorem crosscutOverlay_grid_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {R : Piece},
      R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (_root_.Graph.edgeArc segmentDrawing A \
          V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  obtain ⟨z, hzR, hzA, hznotOverlay⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_right (Q.pieces ++ [J]) hAList)
      (by rwa [edgeArc_segmentDrawing] at hzA)
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'A

/-- Away from overlay vertices, an edge meeting the auxiliary crosscut is one of the
crosscut's subdivision pieces. -/
theorem crosscutOverlay_crosscut_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {R : Piece}, R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (_root_.Graph.edgeArc segmentDrawing J \
          V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc segmentDrawing J := by
  intro R hR hmeet
  obtain ⟨z, hzR, hzJ, hznotOverlay⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'J⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := J)
      (List.mem_append_left _
        (List.mem_append_right Q.pieces (List.mem_singleton_self J)))
      (by rwa [edgeArc_segmentDrawing] at hzJ)
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'J

/-- The auxiliary straight-line overlay contains a plane subdivision of the raw local grid. -/
theorem crosscutOverlay_localGrid_isPlaneSubdivisionExtension
    {J : Piece} {p : Plane} {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg)
    (extra : List Plane) :
    IsPlaneSubdivisionExtension
      (localGrid p s (localGridCount s epsilon)) segmentDrawing
      (Q.crosscutOverlay J p s epsilon extra) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := localGrid_isDrawing hs (one_le_localGridCount s epsilon)
  isDrawing := Q.crosscutOverlay_isDrawing hs hJ extra
  vertexSet_subset := Q.localGridVertices_subset_crosscutOverlay hs hJ extra
  pointSet_subset := by
    rw [localGrid_eq, pieceListGraph_pointSet]
    exact Q.localGrid_subset_crosscutOverlay J p s epsilon extra
  edge_subset := by
    intro A hA R hR hmeet
    exact Q.crosscutOverlay_grid_edge_subset hs hJ extra hA hR hmeet

/-- A single nondegenerate straight segment, with its two ends as vertices, is a plane
drawing. -/
theorem pieceListGraph_single_isDrawing {J : Piece} (hJ : J.Nondeg) :
    _root_.Graph.IsDrawing (pieceListGraph [J]) segmentDrawing where
  edge_param := by
    intro R hR
    rw [pieceListGraph_mem_edgeSet, List.mem_singleton] at hR
    subst R
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hJ, ?_⟩
    simp [segmentDrawing]
  vertex_mem_edgeArc := by
    intro R x y v hR hv _
    rw [pieceListGraph_isLink] at hR
    obtain ⟨hRJ, hxy⟩ := hR
    rw [List.mem_singleton] at hRJ
    subst R
    rw [pieceListGraph_vertexSet] at hv
    obtain ⟨A, hAJ, hvA⟩ := hv
    rw [List.mem_singleton] at hAJ
    subst A
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hvA
    · exact hvA.symm
  edge_inter := by
    intro R A hR hA hne
    rw [pieceListGraph_mem_edgeSet, List.mem_singleton] at hR hA
    exact (hne (hR.trans hA.symm)).elim

/-! ### Fresh relabelling and the wild outer graph -/

/-- Fresh abstract edge names for an auxiliary-crosscut inner overlay. -/
structure CrosscutOverlayRelabeling (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) where
  /-- Assignment of overlay vertices, edges and faces to fresh cell names. -/
  name : Piece → γ
  name_inj : InjOn name E(Q.crosscutOverlay J p s epsilon extra)
  name_fresh : ∀ R ∈ E(Q.crosscutOverlay J p s epsilon extra), name R ∉ P.str.cells

/-- An infinite cell-name type supplies fresh names for the auxiliary-crosscut overlay. -/
theorem exists_crosscutOverlayRelabeling [Infinite γ]
    (J : Piece) (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    Nonempty (Q.CrosscutOverlayRelabeling J p s epsilon extra) := by
  obtain ⟨name, hname, hfresh⟩ := exists_finiteGraph_edgeRelabeling_avoiding γ
    (Q.crosscutOverlay J p s epsilon extra) P.str.cells P.str.finite_cells
  exact ⟨⟨name, hname, hfresh⟩⟩

namespace CrosscutOverlayRelabeling

variable {Q : SourceNonboundarySegmentCover P} {J : Piece} {p : Plane}
  {s epsilon : ℝ} {extra : List Plane}
  (w : Q.CrosscutOverlayRelabeling J p s epsilon extra)

/-- The old outer graph, still drawn on the wild source curve. -/
abbrev outerGraph (_w : Q.CrosscutOverlayRelabeling J p s epsilon extra) :
    _root_.Graph Plane γ := P.str.outerGraph.map P.src.pos

/-- The freshly relabelled auxiliary-crosscut inner overlay. -/
noncomputable abbrev innerGraph : _root_.Graph Plane γ :=
  (Q.crosscutOverlay J p s epsilon extra).relabelEdges w.name w.name_inj

/-- The mixed crosscut source graph. -/
noncomputable def graph : _root_.Graph Plane γ := w.outerGraph.union w.innerGraph

/-- The mixed drawing keeps the wild outer parametrizations and uses straight segments on all
fresh inner edges. -/
noncomputable def drawing : γ → ℝ → Plane := by
  classical
  exact fun e =>
    if e ∈ E(P.str.outerGraph) then P.src.drawing e
    else (Q.crosscutOverlay J p s epsilon extra).relabelDrawing
      w.name segmentDrawing e

/-- Old outer names and freshly allocated inner names are disjoint. -/
theorem compatible : w.outerGraph.Compatible w.innerGraph := by
  apply _root_.Graph.Compatible.of_disjoint_edgeSet
  rw [Set.disjoint_left, _root_.Graph.edgeSet_map, _root_.Graph.edgeSet_relabelEdges]
  intro e heOuter heInner
  obtain ⟨R, hR, hname⟩ := heInner
  rw [← hname] at heOuter
  exact w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- On an old outer edge the mixed drawing is the old source drawing. -/
theorem drawing_of_outer {e : γ} (he : e ∈ E(P.str.outerGraph)) :
    w.drawing e = P.src.drawing e := by simp [drawing, he]

/-- On a fresh inner edge the mixed drawing is its relabelled segment drawing. -/
theorem drawing_of_inner {e : γ} (he : e ∈ E(w.innerGraph)) :
    w.drawing e =
      (Q.crosscutOverlay J p s epsilon extra).relabelDrawing
        w.name segmentDrawing e := by
  rw [drawing, ite_eq_right]
  obtain ⟨R, hR, rfl⟩ := he
  exact fun heOuter => w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- The mixed drawing restricts to a drawing of the old wild outer graph. -/
theorem outer_isDrawing : w.outerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    (P.src.isDrawing.mono (P.str.outerGraph_le.map P.src.pos))
  intro e he
  apply w.drawing_of_outer
  rwa [_root_.Graph.edgeSet_map] at he

/-- The mixed drawing restricts to the relabelled auxiliary-crosscut inner overlay. -/
theorem inner_isDrawing (hs : 0 < s) (hJ : J.Nondeg) :
    w.innerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    ((Q.crosscutOverlay_isDrawing hs hJ extra).relabelEdges w.name_inj)
  intro e he
  exact w.drawing_of_inner he

/-- The outer part occupies exactly the wild source curve. -/
theorem outer_pointSet :
    _root_.Graph.pointSet w.outerGraph w.drawing = srcOuter := by
  calc
    _root_.Graph.pointSet w.outerGraph w.drawing =
        _root_.Graph.pointSet w.outerGraph P.src.drawing := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval)
        (w.drawing_of_outer (by rwa [_root_.Graph.edgeSet_map] at he))
    _ = P.src.outerSet := rfl
    _ = srcOuter := P.src_isWeaklyAdmissible.outerSet_eq

/-- The inner part occupies exactly the straight-line auxiliary-crosscut overlay. -/
theorem inner_pointSet :
    _root_.Graph.pointSet w.innerGraph w.drawing =
      _root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra)
        segmentDrawing := by
  calc
    _root_.Graph.pointSet w.innerGraph w.drawing =
        _root_.Graph.pointSet w.innerGraph
          ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
            w.name segmentDrawing) := by
      apply _root_.Graph.pointSet_congr
      intro e he
      simpa only [_root_.Graph.edgeArc] using congrArg
        (fun f : ℝ → Plane => f '' unitInterval) (w.drawing_of_inner he)
    _ = _root_.Graph.pointSet (Q.crosscutOverlay J p s epsilon extra)
        segmentDrawing :=
      _root_.Graph.pointSet_relabelEdges w.name_inj

/-- The wild outer graph and the auxiliary-crosscut inner overlay form a plane drawing. -/
theorem graph_isDrawing (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    w.graph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_union_of_common_vertices
    w.outer_isDrawing (w.inner_isDrawing hs hJ) w.compatible
  intro x hxOuter hxInner
  rw [w.outer_pointSet] at hxOuter
  rw [w.inner_pointSet, Q.crosscutOverlay_pointSet] at hxInner
  rcases hxInner with (hxCore | hxCrosscut) | hxGrid
  · obtain ⟨hxCoreV, hxOuterV⟩ :=
      sourceCore_inter_outer_vertices (P := P) hxCore hxOuter
    refine ⟨hxOuterV, ?_⟩
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra hxCoreV
  · by_cases hxLeft : x = J.1
    · subst x
      refine ⟨P.sourceVertex_mem_outerGraph
          (hJgeom.left_vertex_of_mem_outer hxOuter) hxOuter, ?_⟩
      rw [_root_.Graph.vertexSet_relabelEdges]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert J.1 {J.2})
    by_cases hxRight : x = J.2
    · subst x
      refine ⟨P.sourceVertex_mem_outerGraph
          (hJgeom.right_vertex_of_mem_outer hxOuter) hxOuter, ?_⟩
      rw [_root_.Graph.vertexSet_relabelEdges]
      exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra
        (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
    exact ((hJgeom.interior_subset
      (mem_openSegment_of_ne_left_right (Ne.symm hxLeft) (Ne.symm hxRight) hxCrosscut)).2
        hxOuter).elim
  · have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxGrid
    exact ((hwindow hxWindow).2 hxOuter).elim

/-- The mixed crosscut source graph is finite. -/
theorem graph_finite : w.graph.Finite where
  finite_vertexSet := by
    rw [graph, _root_.Graph.vertexSet_union, outerGraph, _root_.Graph.vertexSet_map,
      _root_.Graph.vertexSet_relabelEdges]
    exact ((P.str.finite_vertexSet.subset P.str.outerGraph_le.vertexSet_mono).image
      P.src.pos).union
      (_root_.Graph.finite_vertexSet (Q.crosscutOverlay J p s epsilon extra))
  finite_edgeSet := by
    rw [graph, _root_.Graph.edgeSet_union, outerGraph, _root_.Graph.edgeSet_map,
      _root_.Graph.edgeSet_relabelEdges]
    exact (P.str.finite_edgeSet.subset P.str.outerGraph_le.edgeSet_mono).union
      ((_root_.Graph.finite_edgeSet
        (Q.crosscutOverlay J p s epsilon extra)).image w.name)

/-- The mixed graph occupies the wild outer curve, old compact core, auxiliary crosscut, and
local grid. -/
theorem graph_pointSet :
    _root_.Graph.pointSet w.graph w.drawing =
      srcOuter ∪ ((
        _root_.Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪ J.seg) ∪
          cover (localGridEdges p s (localGridCount s epsilon))) := by
  rw [graph, _root_.Graph.pointSet_union, w.outer_pointSet, w.inner_pointSet,
    Q.crosscutOverlay_pointSet]

/-- The complete old source skeleton is retained by the mixed crosscut graph. -/
theorem sourceSkeleton_subset_graph :
    P.src.skeletonSet ⊆ _root_.Graph.pointSet w.graph w.drawing := by
  rw [P.skeletonSet_eq_sourceNonboundaryGraph_union, w.graph_pointSet]
  intro x hx
  rcases hx with hxCore | hxOuter
  · exact Or.inr (Or.inl (Or.inl hxCore))
  · exact Or.inl hxOuter

/-- Every old source vertex is retained by the mixed crosscut graph. -/
theorem sourceVertices_subset_graph (hs : 0 < s) (hJ : J.Nondeg) :
    V(P.src.graph) ⊆ V(w.graph) := by
  intro x hx
  obtain ⟨z, hz, hzx, -⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne x x
  obtain ⟨D, hD⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.connected.exists_isPath hx hz
  obtain ⟨e, heD, hinc⟩ :=
    hD.isWalk.exists_inc_source (hD.ne_nil (Ne.symm hzx))
  have heSrc : e ∈ E(P.src.graph) := hD.edge_mem heD
  by_cases heOuter : e ∈ E(P.str.outerGraph)
  · rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inl
      (((P.str.outerGraph_le.map P.src.pos).inc_congr
        (by rwa [_root_.Graph.edgeSet_map])).2 hinc).vertex_mem
  · have hxCore : x ∈ V(P.sourceNonboundaryGraph) := by
      change x ∈ P.sourceNonboundaryVertices
      exact ⟨e, heSrc, heOuter, hinc⟩
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by
      rw [_root_.Graph.vertexSet_relabelEdges]
      exact Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra hxCore)

/-- Both ends of the auxiliary crosscut are vertices of the mixed graph. -/
theorem crosscutEnds_subset_graph (hs : 0 < s) (hJ : J.Nondeg) :
    ({J.1, J.2} : Set Plane) ⊆ V(w.graph) := by
  intro x hx
  rw [graph, _root_.Graph.vertexSet_union]
  exact Or.inr (by
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.crosscutEnds_subset_crosscutOverlay hs hJ extra hx)

/-- The mixed crosscut graph stays in the closed source domain. -/
theorem graph_pointSet_subset (hs : 0 < s)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    _root_.Graph.pointSet w.graph w.drawing ⊆ srcDom := by
  rw [graph, _root_.Graph.pointSet_union]
  apply Set.union_subset
  · rw [w.outer_pointSet, ← P.src_isWeaklyAdmissible.outerSet_eq]
    exact (_root_.Graph.pointSet_mono (P.str.outerGraph_le.map P.src.pos)).trans
      P.src_isWeaklyAdmissible.skeletonSet_subset
  · rw [w.inner_pointSet]
    exact Q.crosscutOverlay_pointSet_subset hs hJgeom.seg_subset_domain hwindow extra

/-- Every mixed edge is either on the wild outer curve or is a polygonal inner edge whose
nonvertex points lie in the open source domain. -/
theorem graph_edge_dichotomy (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(w.graph) → _root_.Graph.edgeArc w.drawing e ⊆ srcOuter ∨
      (IsPolygonal (_root_.Graph.edgeArc w.drawing e) ∧
        _root_.Graph.edgeArc w.drawing e \ V(w.graph) ⊆ srcDom \ srcOuter) := by
  intro e he
  rcases he with heOuter | heInner
  · exact Or.inl (by
      intro x hx
      rw [← w.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet heOuter hx)
  · obtain ⟨R, hR, rfl⟩ := heInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : _root_.Graph.edgeArc w.drawing (w.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name R) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun f : ℝ → Plane => f '' unitInterval) hdrawing
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    obtain ⟨hpoly, hinterior⟩ :=
      Q.crosscutOverlay_edge_dichotomy hs hJ hJgeom hwindow extra hR
    refine Or.inr ⟨hpoly, ?_⟩
    intro x hx
    apply hinterior
    refine ⟨hx.1, ?_⟩
    intro hxVertex
    apply hx.2
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- An edge of the mixed crosscut graph meeting an old open source edge away from mixed
vertices is one of that edge's subdivision pieces. -/
theorem graph_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → ∀ {f : γ}, f ∈ E(w.graph) →
      (_root_.Graph.edgeArc w.drawing f ∩ (P.src.cell e \ V(w.graph))).Nonempty →
      _root_.Graph.edgeArc w.drawing f ⊆ _root_.Graph.edgeArc P.src.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hzCell, hznotGraph⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hze : z ∈ _root_.Graph.edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  rcases hf with hfOuter | hfInner
  · have hfAbstract : f ∈ E(P.str.outerGraph) := by
      rwa [_root_.Graph.edgeSet_map] at hfOuter
    have hzfSrc : z ∈ _root_.Graph.edgeArc P.src.drawing f := by
      have hdraw := w.drawing_of_outer hfAbstract
      simpa only [_root_.Graph.edgeArc] using
        (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hzf)
    have hznotOld : z ∉ V(P.src.graph) := fun hzOld =>
      hznotGraph (w.sourceVertices_subset_graph hs hJ hzOld)
    have hef : e = f := P.src.isDrawing.unique_edge_at
      (by rw [_root_.Graph.edgeSet_map]; exact he)
      (by
        rw [_root_.Graph.edgeSet_map]
        exact P.str.outerGraph_le.edgeSet_mono hfAbstract)
      hznotOld hze hzfSrc
    subst f
    have hdraw := w.drawing_of_outer hfAbstract
    rw [_root_.Graph.edgeArc, hdraw]
    intro y hy
    exact hy
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : _root_.Graph.edgeArc w.drawing (w.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name R) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hR
    by_cases heOuter : e ∈ E(P.str.outerGraph)
    · exfalso
      have heMixed : e ∈ E(w.graph) := Or.inl (by
        rw [_root_.Graph.edgeSet_map]
        exact heOuter)
      have hne : e ≠ w.name R := fun heq =>
        w.name_fresh R hR (heq ▸ P.str.mem_cells_of_mem_edgeSet he)
      have hzeMixed : z ∈ _root_.Graph.edgeArc w.drawing e := by
        have hdraw := w.drawing_of_outer heOuter
        simpa only [_root_.Graph.edgeArc] using
          (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hze)
      have hzVertex :=
        (w.graph_isDrawing hs hJ hJgeom hwindow).edge_inter
          heMixed (Or.inr hname) hne hzeMixed hzf |>.1
      exact hznotGraph hzVertex
    · rw [harc]
      apply Q.crosscutOverlay_edge_subset hs hJ extra he heOuter hR
      refine ⟨z, harc ▸ hzf, hzCell, ?_⟩
      intro hzLocal
      apply hznotGraph
      rw [graph, _root_.Graph.vertexSet_union]
      exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The mixed crosscut graph contains a plane subdivision of the complete old source drawing. -/
theorem source_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension P.src.graph P.src.drawing w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := P.src.isDrawing
  isDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  vertexSet_subset := w.sourceVertices_subset_graph hs hJ
  pointSet_subset := w.sourceSkeleton_subset_graph
  edge_subset := by
    intro e he f hf hmeet
    have heAbstract : e ∈ E(P.str.skel) := by
      simpa only [P.src.edgeSet_graph] using he
    obtain ⟨z, hzf, hze, hznot⟩ := hmeet
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heAbstract
    apply w.graph_edge_subset hs hJ hJgeom hwindow heAbstract hf
    refine ⟨z, hzf, ?_, hznot⟩
    rw [P.src.cell_edge hab]
    refine ⟨hze, ?_⟩
    rintro (rfl | rfl)
    · exact hznot (w.sourceVertices_subset_graph hs hJ (hab.map P.src.pos).left_mem)
    · exact hznot (w.sourceVertices_subset_graph hs hJ (hab.map P.src.pos).right_mem)

/-- The old-source trace inside the mixed crosscut graph remains 2-connected. -/
theorem sourceTrace_isTwoConnected (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (_root_.Graph.traceGraph w.graph w.drawing P.src.skeletonSet).IsTwoConnected :=
  (w.source_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).trace_isTwoConnected
    P.src_isWeaklyAdmissible.isTwoConnected

/-- Every raw local-grid vertex is retained by the mixed crosscut graph. -/
theorem localGridVertices_subset_graph (hs : 0 < s) (hJ : J.Nondeg) :
    V(localGrid p s (localGridCount s epsilon)) ⊆ V(w.graph) := by
  intro x hx
  rw [graph, _root_.Graph.vertexSet_union]
  exact Or.inr (by
    rw [_root_.Graph.vertexSet_relabelEdges]
    exact Q.localGridVertices_subset_crosscutOverlay hs hJ extra hx)

/-- The complete raw local-grid carrier is retained by the mixed crosscut graph. -/
theorem localGrid_subset_graph :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet w.graph w.drawing := by
  rw [localGrid_eq, pieceListGraph_pointSet, w.graph_pointSet]
  intro x hx
  exact Or.inr (Or.inr hx)

/-- A mixed edge meeting a raw grid edge away from mixed vertices is a subdivision piece of
that grid edge. -/
theorem graph_grid_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {f : γ},
      f ∈ E(w.graph) →
      (_root_.Graph.edgeArc w.drawing f ∩
        (_root_.Graph.edgeArc segmentDrawing A \ V(w.graph))).Nonempty →
      _root_.Graph.edgeArc w.drawing f ⊆
        _root_.Graph.edgeArc segmentDrawing A := by
  intro A hA f hf hmeet
  obtain ⟨z, hzf, hzA, hznotGraph⟩ := hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hzWindow : z ∈ Plane.closedSquare p s :=
    cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hAList, by rwa [edgeArc_segmentDrawing] at hzA⟩)
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← w.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
    exact (hwindow hzWindow).2 hzOuter
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : _root_.Graph.edgeArc w.drawing (w.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name R) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    apply Q.crosscutOverlay_grid_edge_subset hs hJ extra hA hR
    refine ⟨z, harc ▸ hzf, hzA, ?_⟩
    intro hzLocal
    apply hznotGraph
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- A mixed edge meeting the auxiliary crosscut away from mixed vertices is one of the
crosscut's subdivision pieces. -/
theorem graph_crosscut_edge_subset (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J) :
    ∀ {f : γ}, f ∈ E(w.graph) →
      (_root_.Graph.edgeArc w.drawing f ∩
        (_root_.Graph.edgeArc segmentDrawing J \ V(w.graph))).Nonempty →
      _root_.Graph.edgeArc w.drawing f ⊆
        _root_.Graph.edgeArc segmentDrawing J := by
  intro f hf hmeet
  obtain ⟨z, hzf, hzJ, hznotGraph⟩ := hmeet
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← w.outer_pointSet]
      exact _root_.Graph.edgeArc_subset_pointSet hfOuter hzf
    have hzSeg : z ∈ J.seg := by rwa [edgeArc_segmentDrawing] at hzJ
    have hzLeft : z ≠ J.1 := by
      intro h
      apply hznotGraph
      rw [h]
      exact w.crosscutEnds_subset_graph hs hJ (Set.mem_insert J.1 {J.2})
    have hzRight : z ≠ J.2 := by
      intro h
      apply hznotGraph
      rw [h]
      exact w.crosscutEnds_subset_graph hs hJ
        (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
    exact ((hJgeom.interior_subset
      (mem_openSegment_of_ne_left_right (Ne.symm hzLeft) (Ne.symm hzRight) hzSeg)).2
        hzOuter).elim
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : _root_.Graph.edgeArc w.drawing (w.name R) =
        _root_.Graph.edgeArc segmentDrawing R := by
      calc
        _root_.Graph.edgeArc w.drawing (w.name R) =
            _root_.Graph.edgeArc
              ((Q.crosscutOverlay J p s epsilon extra).relabelDrawing
                w.name segmentDrawing) (w.name R) := by
          simpa only [_root_.Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = _root_.Graph.edgeArc segmentDrawing R :=
          _root_.Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    apply Q.crosscutOverlay_crosscut_edge_subset hs hJ extra hR
    refine ⟨z, harc ▸ hzf, hzJ, ?_⟩
    intro hzLocal
    apply hznotGraph
    rw [graph, _root_.Graph.vertexSet_union]
    exact Or.inr (by rwa [_root_.Graph.vertexSet_relabelEdges])

/-- The mixed graph contains a plane subdivision of the one-edge auxiliary crosscut. -/
theorem crosscut_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension (pieceListGraph [J]) segmentDrawing
      w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := pieceListGraph_single_isDrawing hJ
  isDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  vertexSet_subset := by
    intro x hx
    rw [pieceListGraph_vertexSet] at hx
    simp only [endSet, Set.mem_ofPred_eq] at hx
    obtain ⟨R, hR, hxR⟩ := hx
    simp only [List.mem_singleton] at hR
    subst R
    exact w.crosscutEnds_subset_graph hs hJ hxR
  pointSet_subset := by
    rw [pieceListGraph_pointSet]
    intro x hx
    rw [w.graph_pointSet]
    exact Or.inr (Or.inl (Or.inr (by simpa using hx)))
  edge_subset := by
    intro R hR f hf hmeet
    simp only [pieceListGraph_mem_edgeSet, List.mem_singleton] at hR
    subst R
    exact w.graph_crosscut_edge_subset hs hJ hJgeom hf hmeet

/-- The mixed crosscut graph contains a plane subdivision of the raw local grid. -/
theorem localGrid_isPlaneSubdivisionExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension
      (localGrid p s (localGridCount s epsilon)) segmentDrawing
      w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := localGrid_isDrawing hs (one_le_localGridCount s epsilon)
  isDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  vertexSet_subset := w.localGridVertices_subset_graph hs hJ
  pointSet_subset := w.localGrid_subset_graph
  edge_subset := by
    intro A hA f hf hmeet
    exact w.graph_grid_edge_subset hs hJ hwindow hA hf hmeet

/-- The local-grid trace inside the mixed crosscut graph remains 2-connected. -/
theorem localGridTrace_isTwoConnected (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (_root_.Graph.traceGraph w.graph w.drawing
      (_root_.Graph.pointSet (localGrid p s (localGridCount s epsilon))
        segmentDrawing)).IsTwoConnected :=
  (w.localGrid_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).trace_isTwoConnected
    (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon))

/-- The subdivided auxiliary segment is the exact carrier of a path in the mixed graph. -/
theorem exists_crosscut_trace (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∃ D : List γ, w.graph.IsPath J.1 D J.2 ∧
      _root_.Graph.edgesCover w.drawing D = J.seg := by
  obtain ⟨D, hD, hcover⟩ :=
    (w.crosscut_isPlaneSubdivisionExtension hs hJ hJgeom hwindow).exists_edge_trace
      (pieceListGraph_isLink_self (List.mem_singleton_self J))
  exact ⟨D, hD, by simpa only [edgeArc_segmentDrawing] using hcover⟩

/-- If a nondegenerate raw grid edge lies on the auxiliary segment and both crosscut ends lie
on the old source skeleton, the old trace, crosscut ear, and grid trace span a 2-connected
subgraph.  Consequently the complete mixed graph is 2-connected. -/
theorem graph_isTwoConnected_of_crosscut_grid_edge (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hJsource : J.1 ∈ P.src.skeletonSet ∧ J.2 ∈ P.src.skeletonSet)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg) :
    w.graph.IsTwoConnected := by
  obtain ⟨D, hD, hcover⟩ := w.exists_crosscut_trace hs hJ hJgeom hwindow
  let T := _root_.Graph.traceGraph w.graph w.drawing P.src.skeletonSet
  let C := w.graph.pathGraphOf J.1 D
  let K := _root_.Graph.traceGraph w.graph w.drawing
    (_root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
  have hT2 : T.IsTwoConnected :=
    w.sourceTrace_isTwoConnected hs hJ hJgeom hwindow
  have hJ1Graph : J.1 ∈ V(w.graph) :=
    w.crosscutEnds_subset_graph hs hJ (Set.mem_insert J.1 {J.2})
  have hJ2Graph : J.2 ∈ V(w.graph) :=
    w.crosscutEnds_subset_graph hs hJ (Set.mem_insert_of_mem J.1 (Set.mem_singleton J.2))
  have hJ1T : J.1 ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hJ1Graph, hJsource.1⟩
  have hJ2T : J.2 ∈ V(T) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hJ2Graph, hJsource.2⟩
  have hTC : T.Compatible C :=
    _root_.Graph.Compatible.of_le_le (_root_.Graph.traceGraph_le _)
      (_root_.Graph.pathGraphOf_le hD.isWalk)
  have hU2 : (T.union C).IsTwoConnected :=
    hT2.ear hTC hD.isPathGraph_pathGraphOf hJ hJ1T hJ2T
  have hK2 : K.IsTwoConnected :=
    w.localGridTrace_isTwoConnected hs hJ hJgeom hwindow
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hAlink :
      (localGrid p s (localGridCount s epsilon)).IsLink A A.1 A.2 := by
    rw [localGrid_eq]
    exact pieceListGraph_isLink_self hAList
  have hA1Graph : A.1 ∈ V(w.graph) :=
    w.localGridVertices_subset_graph hs hJ hAlink.left_mem
  have hA2Graph : A.2 ∈ V(w.graph) :=
    w.localGridVertices_subset_graph hs hJ hAlink.right_mem
  have hA1J : A.1 ∈ J.seg := hAJ (left_mem_segment ℝ _ _)
  have hA2J : A.2 ∈ J.seg := hAJ (right_mem_segment ℝ _ _)
  have hA1C : A.1 ∈ V(C) := by
    rw [_root_.Graph.pathGraphOf_vertexSet]
    apply (w.graph_isDrawing hs hJ hJgeom hwindow).mem_walkVertices_of_mem_edgesCover_walk
      hD.isWalk hA1Graph
    rw [hcover]
    exact hA1J
  have hA2C : A.2 ∈ V(C) := by
    rw [_root_.Graph.pathGraphOf_vertexSet]
    apply (w.graph_isDrawing hs hJ hJgeom hwindow).mem_walkVertices_of_mem_edgesCover_walk
      hD.isWalk hA2Graph
    rw [hcover]
    exact hA2J
  have hA1U : A.1 ∈ V(T.union C) := by
    rw [_root_.Graph.vertexSet_union]
    exact Or.inr hA1C
  have hA2U : A.2 ∈ V(T.union C) := by
    rw [_root_.Graph.vertexSet_union]
    exact Or.inr hA2C
  have hA1K : A.1 ∈ V(K) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hA1Graph,
      (_root_.Graph.edgeArc_subset_pointSet hA) (by
        rw [edgeArc_segmentDrawing]
        exact left_mem_segment ℝ _ _)⟩
  have hA2K : A.2 ∈ V(K) := by
    rw [_root_.Graph.traceGraph_vertexSet]
    exact ⟨hA2Graph,
      (_root_.Graph.edgeArc_subset_pointSet hA) (by
        rw [edgeArc_segmentDrawing]
        exact right_mem_segment ℝ _ _)⟩
  have hUKcompat : (T.union C).Compatible K :=
    _root_.Graph.Compatible.of_le_le
      (_root_.Graph.union_le (_root_.Graph.traceGraph_le _)
        (_root_.Graph.pathGraphOf_le hD.isWalk))
      (_root_.Graph.traceGraph_le _)
  have hAne : A.1 ≠ A.2 :=
    localGridEdges_nondeg hs (one_le_localGridCount s epsilon) A hAList
  have hAll2 : ((T.union C).union K).IsTwoConnected :=
    hU2.union hUKcompat hK2 hAne hA1U hA1K hA2U hA2K
  apply hAll2.of_le_of_vertexSet_subset
    (_root_.Graph.union_le
      (_root_.Graph.union_le (_root_.Graph.traceGraph_le _)
        (_root_.Graph.pathGraphOf_le hD.isWalk))
      (_root_.Graph.traceGraph_le _))
  intro x hx
  rw [_root_.Graph.vertexSet_union]
  have hxPoint : x ∈ _root_.Graph.pointSet w.graph w.drawing :=
    _root_.Graph.vertexSet_subset_pointSet hx
  rw [w.graph_pointSet] at hxPoint
  rcases hxPoint with hxOuter | hxRest
  · exact Or.inl (Or.inl (by
      rw [_root_.Graph.traceGraph_vertexSet]
      exact ⟨hx, by
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
        exact Or.inr hxOuter⟩))
  · rcases hxRest with hxCoreJ | hxGrid
    · rcases hxCoreJ with hxCore | hxJ
      · exact Or.inl (Or.inl (by
          rw [_root_.Graph.traceGraph_vertexSet]
          exact ⟨hx, by
            rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
            exact Or.inl hxCore⟩))
      · exact Or.inl (Or.inr (by
          rw [_root_.Graph.pathGraphOf_vertexSet]
          apply
            (w.graph_isDrawing hs hJ hJgeom hwindow).mem_walkVertices_of_mem_edgesCover_walk
              hD.isWalk hx
          rw [hcover]
          exact hxJ))
    · exact Or.inr (by
        rw [_root_.Graph.traceGraph_vertexSet]
        exact ⟨hx, by rwa [localGrid_eq, pieceListGraph_pointSet]⟩)

/-- If the old nonouter source carrier is connected, adjoining a crosscut whose first endpoint
lies on it and a grid edge carried by that crosscut preserves connectedness after removing the
wild outer curve. -/
theorem graph_isConnected_diff_of_crosscut_grid_edge (hs : 0 < s)
    (hJopen : J.seg ⊆ srcDom \ srcOuter)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hJsource : J.1 ∈ P.src.skeletonSet)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg) :
    IsConnected (_root_.Graph.pointSet w.graph w.drawing \ srcOuter) := by
  let Kset := _root_.Graph.pointSet
    (localGrid p s (localGridCount s epsilon)) segmentDrawing
  have hJconn : IsConnected J.seg :=
    (convex_segment J.1 J.2).isConnected ⟨J.1, left_mem_segment ℝ _ _⟩
  have hKconn : IsConnected Kset :=
    Schoenflies.Graph.IsDrawing.isConnected_pointSet
      (localGrid_isDrawing hs (one_le_localGridCount s epsilon))
      (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon)).connected
  have hJmiss : J.seg ⊆ srcOuterᶜ := fun x hxJ hxOuter => (hJopen hxJ).2 hxOuter
  have hKmiss : Kset ⊆ srcOuterᶜ := by
    intro x hxK hxOuter
    have hxCover : x ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK
    have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxCover
    exact (hwindow hxWindow).2 hxOuter
  have hcarrier : _root_.Graph.pointSet w.graph w.drawing \ srcOuter =
      ((P.src.skeletonSet \ srcOuter) ∪ J.seg) ∪ Kset := by
    ext x
    rw [Set.mem_sdiff, Set.mem_union, Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro ⟨hxGraph, hxNotOuter⟩
      rw [w.graph_pointSet] at hxGraph
      rcases hxGraph with hxOuter | hxRest
      · exact (hxNotOuter hxOuter).elim
      · rcases hxRest with hxCoreJ | hxGrid
        · rcases hxCoreJ with hxCore | hxJ
          · exact Or.inl (Or.inl ⟨by
              rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
              exact Or.inl hxCore, hxNotOuter⟩)
          · exact Or.inl (Or.inr hxJ)
        · exact Or.inr (by
            simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxGrid)
    · rintro (⟨⟨hxSource, hxNotOuter⟩ | hxJ⟩ | hxK)
      · refine ⟨?_, hxNotOuter⟩
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSource
        rw [w.graph_pointSet]
        rcases hxSource with hxCore | hxOuter
        · exact Or.inr (Or.inl (Or.inl hxCore))
        · exact Or.inl hxOuter
      · exact ⟨by
          rw [w.graph_pointSet]
          exact Or.inr (Or.inl (Or.inr hxJ)), hJmiss hxJ⟩
      · exact ⟨by
          rw [w.graph_pointSet]
          exact Or.inr (Or.inr (by
            simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK)), hKmiss hxK⟩
  have hsourceJmeet : ((P.src.skeletonSet \ srcOuter) ∩ J.seg).Nonempty :=
    ⟨J.1, ⟨hJsource, (hJopen (left_mem_segment ℝ _ _)).2⟩,
      left_mem_segment ℝ _ _⟩
  have hsourceJconn : IsConnected ((P.src.skeletonSet \ srcOuter) ∪ J.seg) :=
    IsConnected.union hsourceJmeet hsource hJconn
  have hA1J : A.1 ∈ J.seg := hAJ (left_mem_segment ℝ _ _)
  have hA1K : A.1 ∈ Kset := by
    apply _root_.Graph.edgeArc_subset_pointSet hA
    rw [edgeArc_segmentDrawing]
    exact left_mem_segment ℝ _ _
  rw [hcarrier]
  exact IsConnected.union ⟨A.1, Or.inr hA1J, hA1K⟩ hsourceJconn hKconn

/-- The boundary-tolerant connectedness argument.  The crosscut with its wild-boundary
endpoints removed is still connected because it lies between its connected open segment and
that segment's closure.  Hence one surviving source endpoint joins it to the old nonboundary
carrier, while the swallowed grid edge joins it to the grid. -/
theorem graph_isConnected_diff_of_crosscut_grid_edge_of_end_not_outer (hs : 0 < s)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hJsource : J.1 ∈ P.src.skeletonSet ∧ J.2 ∈ P.src.skeletonSet)
    (hJattach : J.1 ∉ srcOuter ∨ J.2 ∉ srcOuter)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg) :
    IsConnected (_root_.Graph.pointSet w.graph w.drawing \ srcOuter) := by
  let Jset := J.seg \ srcOuter
  let Kset := _root_.Graph.pointSet
    (localGrid p s (localGridCount s epsilon)) segmentDrawing
  have hJinteriorConn : IsConnected J.interior :=
    (convex_openSegment J.1 J.2).isConnected
      ⟨midpoint ℝ J.1 J.2, midpoint_mem_openSegment J.1 J.2⟩
  have hJconn : IsConnected Jset := by
    apply hJinteriorConn.subset_closure
    · intro x hx
      exact ⟨openSegment_subset_segment ℝ _ _ hx, (hJgeom.interior_subset hx).2⟩
    · change J.seg \ srcOuter ⊆ closure (openSegment ℝ J.1 J.2)
      rw [closure_openSegment]
      exact sdiff_subset
  have hKconn : IsConnected Kset :=
    Schoenflies.Graph.IsDrawing.isConnected_pointSet
      (localGrid_isDrawing hs (one_le_localGridCount s epsilon))
      (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon)).connected
  have hKmiss : Kset ⊆ srcOuterᶜ := by
    intro x hxK hxOuter
    have hxCover : x ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK
    have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxCover
    exact (hwindow hxWindow).2 hxOuter
  have hcarrier : _root_.Graph.pointSet w.graph w.drawing \ srcOuter =
      ((P.src.skeletonSet \ srcOuter) ∪ Jset) ∪ Kset := by
    ext x
    rw [Set.mem_sdiff, Set.mem_union, Set.mem_union, Set.mem_sdiff, Set.mem_sdiff]
    constructor
    · rintro ⟨hxGraph, hxNotOuter⟩
      rw [w.graph_pointSet] at hxGraph
      rcases hxGraph with hxOuter | hxRest
      · exact (hxNotOuter hxOuter).elim
      · rcases hxRest with hxCoreJ | hxGrid
        · rcases hxCoreJ with hxCore | hxJ
          · exact Or.inl (Or.inl ⟨by
              rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
              exact Or.inl hxCore, hxNotOuter⟩)
          · exact Or.inl (Or.inr ⟨hxJ, hxNotOuter⟩)
        · exact Or.inr (by
            simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxGrid)
    · rintro (⟨⟨hxSource, hxNotOuter⟩ | ⟨hxJ, hxNotOuter⟩⟩ | hxK)
      · refine ⟨?_, hxNotOuter⟩
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSource
        rw [w.graph_pointSet]
        rcases hxSource with hxCore | hxOuter
        · exact Or.inr (Or.inl (Or.inl hxCore))
        · exact Or.inl hxOuter
      · exact ⟨by
          rw [w.graph_pointSet]
          exact Or.inr (Or.inl (Or.inr hxJ)), hxNotOuter⟩
      · exact ⟨by
          rw [w.graph_pointSet]
          exact Or.inr (Or.inr (by
            simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK)), hKmiss hxK⟩
  have hsourceJmeet : ((P.src.skeletonSet \ srcOuter) ∩ Jset).Nonempty := by
    rcases hJattach with hleft | hright
    · exact ⟨J.1, ⟨hJsource.1, hleft⟩, ⟨left_mem_segment ℝ _ _, hleft⟩⟩
    · exact ⟨J.2, ⟨hJsource.2, hright⟩, ⟨right_mem_segment ℝ _ _, hright⟩⟩
  have hsourceJconn : IsConnected ((P.src.skeletonSet \ srcOuter) ∪ Jset) :=
    IsConnected.union hsourceJmeet hsource hJconn
  have hA1J : A.1 ∈ J.seg := hAJ (left_mem_segment ℝ _ _)
  have hA1K : A.1 ∈ Kset := by
    apply _root_.Graph.edgeArc_subset_pointSet hA
    rw [edgeArc_segmentDrawing]
    exact left_mem_segment ℝ _ _
  have hA1NotOuter : A.1 ∉ srcOuter := hKmiss hA1K
  rw [hcarrier]
  exact IsConnected.union
    ⟨A.1, Or.inr ⟨hA1J, hA1NotOuter⟩, hA1K⟩ hsourceJconn hKconn

/-- Once its two global attachment properties are known, the mixed crosscut graph is a complete
source extension. -/
theorem isSourceExtension (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (htwo : w.graph.IsTwoConnected)
    (hconnected : IsConnected
      (_root_.Graph.pointSet w.graph w.drawing \ srcOuter)) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing where
  finite := w.graph_finite
  isDrawing := w.graph_isDrawing hs hJ hJgeom hwindow
  isTwoConnected := htwo
  vertexSet_subset := w.sourceVertices_subset_graph hs hJ
  skeletonSet_subset := w.sourceSkeleton_subset_graph
  edge_subset := by
    intro e he f hf hmeet
    exact w.graph_edge_subset hs hJ hJgeom hwindow he hf hmeet
  pointSet_subset := w.graph_pointSet_subset hs hJgeom hwindow
  edge_dichotomy := by
    intro f hf
    exact w.graph_edge_dichotomy hs hJ hJgeom hwindow hf
  isConnected := hconnected

/-- The crosscut construction is a source extension once its concrete geometric attachment
data are supplied; no separate graph-theoretic 2-connectivity or carrier-connectedness
hypotheses remain. -/
theorem isSourceExtension_of_crosscut_grid_edge (hs : 0 < s) (hJ : J.Nondeg)
    (hJopen : J.seg ⊆ srcDom \ srcOuter)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hJsource : J.1 ∈ P.src.skeletonSet ∧ J.2 ∈ P.src.skeletonSet)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing := by
  let hJgeom : SourceCrosscutGeometry P J :=
    SourceCrosscutGeometry.of_seg_subset_interior hJopen
  exact w.isSourceExtension hs hJ hJgeom hwindow
    (w.graph_isTwoConnected_of_crosscut_grid_edge hs hJ hJgeom hwindow
      hJsource hA hAJ)
    (w.graph_isConnected_diff_of_crosscut_grid_edge hs hJopen hwindow
      hsource hJsource.1 hA hAJ)

/-- Boundary-tolerant packaging: once one crosscut endpoint survives deletion of the wild outer
curve, the generalized crosscut geometry gives the complete source extension. -/
theorem isSourceExtension_of_crosscut_grid_edge_of_end_not_outer
    (hs : 0 < s) (hJ : J.Nondeg)
    (hJgeom : SourceCrosscutGeometry P J)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hJsource : J.1 ∈ P.src.skeletonSet ∧ J.2 ∈ P.src.skeletonSet)
    (hJattach : J.1 ∉ srcOuter ∨ J.2 ∉ srcOuter)
    {A : Piece} (hA : A ∈ E(localGrid p s (localGridCount s epsilon)))
    (hAJ : A.seg ⊆ J.seg) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing :=
  w.isSourceExtension hs hJ hJgeom hwindow
    (w.graph_isTwoConnected_of_crosscut_grid_edge hs hJ hJgeom hwindow
      hJsource hA hAJ)
    (w.graph_isConnected_diff_of_crosscut_grid_edge_of_end_not_outer hs hJgeom hwindow
      hsource hJsource hJattach hA hAJ)

end CrosscutOverlayRelabeling

end SourceNonboundarySegmentCover

/-- The concrete output required from a local-grid source attachment: a finite source extension
whose carrier contains the complete raw local grid. -/
structure LocalGridSourceExtensionData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (p : Plane) (s epsilon : ℝ) where
  /-- Finite graph extending the source skeleton and local grid. -/
  graph : _root_.Graph Plane γ
  /-- Planar parametrizations of the extension edges. -/
  drawing : γ → ℝ → Plane
  isSourceExtension : IsSourceExtension P.src srcOuter srcDom graph drawing
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet graph drawing

/-- The boundary-touching crosscut construction after its two endpoint subdivisions.  This
packages every global graph property except connectedness after deleting the wild outer curve;
that last property is exactly what the blueprint's finite component-joining loop supplies. -/
structure RefinedCrosscutOverlayData
    {F : γ} {A : Piece} (r : RefinedSourceFaceCrosscutData P F A)
    (p : Plane) (s epsilon : ℝ) where
  /-- Finite segment cover of the subdivided nonboundary skeleton. -/
  cover : SourceNonboundarySegmentCover r.subdivision.pair
  /-- Fresh names for the crosscut and local-grid overlay. -/
  relabeling : cover.CrosscutOverlayRelabeling r.crosscutData.crosscut p s epsilon []
  isDrawing : relabeling.graph.IsDrawing relabeling.drawing
  isTwoConnected : relabeling.graph.IsTwoConnected
  sourceSkeleton_subset :
    r.subdivision.pair.src.skeletonSet ⊆
      _root_.Graph.pointSet relabeling.graph relabeling.drawing
  pointSet_subset :
    _root_.Graph.pointSet relabeling.graph relabeling.drawing ⊆ srcDom
  localGrid_subset :
    _root_.Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      _root_.Graph.pointSet relabeling.graph relabeling.drawing

namespace RefinedCrosscutOverlayData

/-- A refined crosscut overlay is already a complete local-grid source extension whenever at
least one crosscut endpoint is not on the wild outer curve. -/
noncomputable def toLocalGridSourceExtensionData
    {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    {r : RefinedSourceFaceCrosscutData P F A}
    (o : RefinedCrosscutOverlayData r p s epsilon)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected r.subdivision.pair.src.nonboundary)
    (hattach : r.crosscutData.crosscut.1 ∉ srcOuter ∨
      r.crosscutData.crosscut.2 ∉ srcOuter)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    LocalGridSourceExtensionData r.subdivision.pair p s epsilon := by
  have hsource' : IsConnected
      (r.subdivision.pair.src.skeletonSet \ srcOuter) := by
    rwa [r.subdivision.pair.src_nonboundary_eq] at hsource
  have hJsource :
      r.crosscutData.crosscut.1 ∈ r.subdivision.pair.src.skeletonSet ∧
        r.crosscutData.crosscut.2 ∈ r.subdivision.pair.src.skeletonSet := by
    rw [r.subdivision.skeletonSet_eq]
    exact ⟨r.crosscutData.left_mem_skeleton, r.crosscutData.right_mem_skeleton⟩
  exact {
    graph := o.relabeling.graph
    drawing := o.relabeling.drawing
    isSourceExtension :=
      o.relabeling.isSourceExtension_of_crosscut_grid_edge_of_end_not_outer
        hs r.crosscutData.nondeg r.geometry hwindow hsource' hJsource hattach
        hA r.crosscutData.grid_subset
    localGrid_subset := o.localGrid_subset
  }

end RefinedCrosscutOverlayData

/-- The boundary-touching branch now constructs a plane, 2-connected, domain-contained mixed
overlay after a matched subdivision at the two crosscut endpoints.  The construction also
retains the entire refined source skeleton and the raw local grid. -/
theorem GeneratedPair.exists_refinedCrosscutOverlayData
    [Infinite γ] {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (Σ r : RefinedSourceFaceCrosscutData P F A,
      RefinedCrosscutOverlayData r p s epsilon) := by
  obtain ⟨d⟩ := P.exists_sourceFaceCrosscutData hF hFbdd hab hAline hy
  obtain ⟨r⟩ := d.exists_refinement
  obtain ⟨Q⟩ := r.subdivision.pair.exists_sourceNonboundarySegmentCover
  obtain ⟨w⟩ := Q.exists_crosscutOverlayRelabeling
    r.crosscutData.crosscut p s epsilon []
  have hJsource :
      r.crosscutData.crosscut.1 ∈ r.subdivision.pair.src.skeletonSet ∧
        r.crosscutData.crosscut.2 ∈ r.subdivision.pair.src.skeletonSet := by
    rw [r.subdivision.skeletonSet_eq]
    exact ⟨r.crosscutData.left_mem_skeleton, r.crosscutData.right_mem_skeleton⟩
  exact ⟨⟨r, {
    cover := Q
    relabeling := w
    isDrawing := w.graph_isDrawing hs r.crosscutData.nondeg r.geometry hwindow
    isTwoConnected := w.graph_isTwoConnected_of_crosscut_grid_edge
      hs r.crosscutData.nondeg r.geometry hwindow hJsource hA r.crosscutData.grid_subset
    sourceSkeleton_subset := w.sourceSkeleton_subset_graph
    pointSet_subset := w.graph_pointSet_subset hs r.geometry hwindow
    localGrid_subset := w.localGrid_subset_graph
  }⟩⟩

/-- Complete local-grid source attachment for the crosscut case in which the selected source
face has no wild-boundary points on its frontier.  The face crosscut swallows the chosen raw
grid edge, its traced subdivision is attached as an ear, and the grid trace is then glued along
the two distinct ends of that edge. -/
theorem GeneratedPair.exists_localGridSourceExtension_of_face_frontier
    [Infinite γ] {F : γ} {A : Piece} {p : Plane} {s epsilon : ℝ}
    (hF : F ∈ P.str.faces) (hFbdd : Bornology.IsBounded (P.src.cell F))
    {a b y : Plane} (hab : a ≠ b)
    (hAline : A.interior ⊆ Plane.line a b ∩ P.src.cell F)
    (hy : y ∈ A.interior)
    (hfrontier : frontier (P.src.cell F) ⊆ srcDom \ srcOuter)
    (hs : 0 < s) (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected P.src.nonboundary)
    (hA : A ∈ E(localGrid p s (localGridCount s epsilon))) :
    Nonempty (LocalGridSourceExtensionData P p s epsilon) := by
  obtain ⟨d⟩ := P.exists_sourceFaceCrosscutData hF hFbdd hab hAline hy
  obtain ⟨Q⟩ := P.exists_sourceNonboundarySegmentCover
  obtain ⟨w⟩ := Q.exists_crosscutOverlayRelabeling d.crosscut p s epsilon []
  have hsource' : IsConnected (P.src.skeletonSet \ srcOuter) := by
    rwa [P.src_nonboundary_eq] at hsource
  exact ⟨{
    graph := w.graph
    drawing := w.drawing
    isSourceExtension :=
      w.isSourceExtension_of_crosscut_grid_edge hs d.nondeg
        (d.seg_subset_interior hfrontier) hwindow hsource'
        ⟨d.left_mem_skeleton, d.right_mem_skeleton⟩ hA d.grid_subset
    localGrid_subset := w.localGrid_subset_graph
  }⟩

end Schoenflies
