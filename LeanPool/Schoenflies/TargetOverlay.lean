/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FiniteTransferTargetMesh
public import LeanPool.Schoenflies.SkeletonLocal

/-!
# Overlaying a target skeleton with the anchored square mesh

A fresh square mesh does not generally contain the current target skeleton: already at stage
zero the target has an arbitrary straight chord which need not be radial or lie on a mesh ring.
The ambient graph for reverse finite transfer must therefore be the polygonal overlay of the
two finite segment families.

`TargetSegmentCover` writes the whole current target skeleton as a finite exact segment cover.
It also remembers which old abstract edge supplied each segment; that provenance is what will
prove the subdivision clause after transverse intersections have been made vertices.

`TargetSegmentCover.meshOverlay` is the combined graph.  It overlays the target cover with the
already-subdivided edges of the anchored mesh, and its cut list contains both the mesh anchors
and every old target vertex.  The basic carrier, drawing, containment, edge-source, and
2-connectivity facts are established here.  The nonouter target-edge carriers form a canonical
finite connected cover of the old open skeleton.  A uniform positive width for this cover,
together with the radial mesh estimate, shows that every sufficiently fine dense mesh meets
every cover piece.  Consequently the combined overlay is a complete source extension at some
positive scale below `4`.  Relative boundary anchoring and no-new-nonouter-incidence are proved
for clean fresh lists and transported through edge relabelling, so the overlay now feeds directly
into reverse finite transfer.  `FreshDenseSelection.lean` constructs the required finite clean
separator list from the dense strongly-accessible boundary points and packages the resulting
reverse-transfer stage.

## Blueprint

* `Schoenflies.TargetSegmentCover` — the finite segment presentation of the current polygonal
  target skeleton.
* `Schoenflies.GeneratedPair.exists_targetSegmentCover` — every generated pair supplies that
  presentation.
* `Schoenflies.TargetSegmentCover.meshOverlay` — the current target skeleton overlaid with the
  anchored square mesh.
* `Schoenflies.TargetSegmentCover.meshOverlay_pointSet` — the combined graph occupies exactly
  the union of the two carriers.
* `Schoenflies.TargetSegmentCover.meshOverlay_isTwoConnected` — the two subdivision traces glue
  along two fresh boundary vertices to make the combined overlay 2-connected.
* `Schoenflies.TargetSegmentCover.noNewNonouterIncidenceAtBoundary_meshOverlay` — clean fresh
  spokes cannot create a second nonouter incidence against the current target trace.
* `Schoenflies.finiteOpenTargetCover` — the nonouter edge carriers, with the model curve
  removed, form a finite connected nontrivial cover of the old open target skeleton.
* `Schoenflies.exists_fine_openTarget_scale` — every generated target has a positive scale
  below `4` at which all pieces of that cover are wider than the mesh.
* `Schoenflies.TargetSegmentCover.exists_scale_isSourceExtension_relabelledMeshOverlay` — at
  that scale, every dense anchored mesh gives the complete relabelled source extension.
* `Schoenflies.TargetSegmentCover.finite_transfer_toward_source_relabelledMeshOverlay_of_outerCycle`
  — the accessible clean overlay performs the complete reverse finite transfer.
-/

@[expose] public section

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- A finite exact segment presentation of the target skeleton, with each segment traced back
to an old abstract edge. -/
structure TargetSegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) where
  /-- The straight segments covering the target skeleton. -/
  pieces : List Piece
  /-- No listed segment is degenerate. -/
  nondeg : ∀ Q ∈ pieces, Q.Nondeg
  /-- The listed segments occupy exactly the target skeleton. -/
  cover_eq : cover pieces = P.tgt.skeletonSet
  /-- Every listed segment came from one old target edge. -/
  source : ∀ Q ∈ pieces, ∃ e ∈ E(P.str.skel), Q.seg ⊆ edgeArc P.tgt.drawing e

namespace GeneratedPair

/-- Every generated pair has a finite segment presentation of its polygonal target skeleton. -/
theorem exists_targetSegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    Nonempty (TargetSegmentCover P) := by
  let _ : Graph.Finite P.tgt.graph :=
    CellStructure.Realization.finite_graph P.tgt
  have hincident : ∀ z ∈ V(P.tgt.graph), ∃ e, P.tgt.graph.Inc e z := by
    intro z hz
    obtain ⟨w, hw, hwz, -⟩ :=
      P.tgt_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne z z
    obtain ⟨D, hD⟩ :=
      (P.tgt_isWeaklyAdmissible.isTwoConnected.connected.reaches hz hw).exists_isPath
    obtain ⟨e, -, hinc⟩ := hD.isWalk.exists_inc_source
      (hD.ne_nil (Ne.symm hwz))
    exact ⟨e, hinc⟩
  have hpoly : ∀ e ∈ E(P.tgt.graph), IsPolygonal (edgeArc P.tgt.drawing e) := by
    intro e he
    apply P.tgt_isPolygonal
    rwa [P.tgt.edgeSet_graph] at he
  obtain ⟨pieces, hnd, hcover, hsource⟩ :=
    P.tgt.isDrawing.exists_segmentCover (G := P.tgt.graph) hpoly hincident
  refine ⟨⟨pieces, hnd, hcover, ?_⟩⟩
  intro Q hQ
  obtain ⟨e, he, hsub⟩ := hsource Q hQ
  exact ⟨e, by rwa [P.tgt.edgeSet_graph] at he, hsub⟩

end GeneratedPair

namespace TargetSegmentCover

variable {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}

/-- The already-subdivided edges of the anchored square mesh, listed as straight pieces. -/
noncomputable def squareMeshPieces (delta : ℝ) (fresh anchors : List Plane) : List Piece :=
  (squareMesh delta fresh anchors).edgeFinset.toList

@[simp] theorem mem_squareMeshPieces {delta : ℝ} {fresh anchors : List Plane} {R : Piece} :
    R ∈ squareMeshPieces delta fresh anchors ↔ R ∈ E(squareMesh delta fresh anchors) := by
  simp [squareMeshPieces, Graph.mem_edgeFinset]

/-- Listing the edges loses no carrier: every square-mesh vertex is an end of one of its
edges. -/
theorem cover_squareMeshPieces (delta : ℝ) (fresh anchors : List Plane) :
    cover (squareMeshPieces delta fresh anchors) =
      Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing := by
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ := mem_cover_iff.1 hx
    exact Or.inr (Set.mem_iUnion₂_of_mem (mem_squareMeshPieces.1 hR) (by
      rwa [edgeArc_segmentDrawing]))
  · intro hx
    rcases hx with hxV | hxE
    · obtain ⟨R, hR, hxR⟩ := meshGraph_mem_vertexSet.1 hxV
      exact mem_cover_iff.2 ⟨R, mem_squareMeshPieces.2 hR, by
        rcases hxR with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩
    · obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.1 hxE
      exact mem_cover_iff.2 ⟨R, mem_squareMeshPieces.2 hR, by
        rwa [← edgeArc_segmentDrawing]⟩

/-- The two source families for the combined target overlay. -/
noncomputable def meshPieces (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : List Piece :=
  Q.pieces ++ squareMeshPieces delta fresh anchors

/-- The target skeleton overlaid with the anchored square mesh.  Old vertices and prescribed
mesh anchors are explicitly included in the cut list. -/
noncomputable def meshOverlay (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : Graph Plane Piece :=
  attachGraph (Q.meshPieces delta fresh anchors)
    (anchors ++ P.tgt.graph.vertexFinset.toList)

instance meshOverlay_finite (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : (Q.meshOverlay delta fresh anchors).Finite :=
  attachGraph_finite _ _

/-- Every source segment of the combined overlay is nondegenerate. -/
theorem meshPieces_nondeg (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (delta : ℝ)
    (anchors : List Plane) :
    ∀ R ∈ Q.meshPieces delta fresh anchors, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact Q.nondeg R hR
  · exact meshGraph_edge_nondeg (two_le_meshCount delta) hfresh
      (mem_squareMeshPieces.1 hR)

/-- The combined overlay is a finite straight-line plane graph. -/
theorem meshOverlay_isDrawing (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    Graph.IsDrawing (Q.meshOverlay delta fresh anchors) segmentDrawing :=
  attachGraph_isDrawing (Q.meshPieces_nondeg hfresh delta anchors) _

/-- The combined overlay occupies exactly the current target skeleton together with the square
mesh. -/
theorem meshOverlay_pointSet (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing =
      P.tgt.skeletonSet ∪
        Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing := by
  rw [meshOverlay, attachGraph_pointSet, meshPieces, cover_append, Q.cover_eq,
    cover_squareMeshPieces]

/-- The current target skeleton is contained in the combined overlay. -/
theorem targetSkeleton_subset_meshOverlay (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    P.tgt.skeletonSet ⊆
      Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing := by
  rw [Q.meshOverlay_pointSet]
  exact subset_union_left

/-- The whole anchored square mesh is contained in the combined overlay. -/
theorem squareMesh_subset_meshOverlay (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing ⊆
      Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing := by
  rw [Q.meshOverlay_pointSet]
  exact subset_union_right

/-- Every old target vertex is explicitly retained as a vertex of the combined overlay. -/
theorem targetVertices_subset_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    V(P.tgt.graph) ⊆ V(Q.meshOverlay delta fresh anchors) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.meshPieces_nondeg hfresh delta anchors)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right anchors (by
      rw [Finset.mem_toList, mem_vertexFinset]
      exact hx)
  · rw [meshPieces, cover_append, Q.cover_eq]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- Every square-mesh vertex is an endpoint of a source piece for the combined overlay. -/
theorem squareMeshVertices_subset_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    V(squareMesh delta fresh anchors) ⊆ V(Q.meshOverlay delta fresh anchors) := by
  intro x hx
  obtain ⟨R, hR, hxR⟩ := meshGraph_mem_vertexSet.1 hx
  change x ∈ V(overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.meshPieces_nondeg hfresh delta anchors)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right Q.pieces (mem_squareMeshPieces.2 hR)) x hxR
  · exact mem_cover_iff.2 ⟨R,
      List.mem_append_right Q.pieces (mem_squareMeshPieces.2 hR), by
        rcases hxR with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩

/-- Every edge of the combined overlay is a subsegment either of an old target segment or of a
square-mesh source segment. -/
theorem meshOverlay_edge_source (Q : TargetSegmentCover P)
    {delta : ℝ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ E(Q.meshOverlay delta fresh anchors)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      ∃ A ∈ meshSegments (meshCount delta) fresh, R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, hA, hsub⟩
  · obtain ⟨B, hB, hAB⟩ := meshGraph_edge_source (mem_squareMeshPieces.1 hA)
    exact Or.inr ⟨B, hB, hsub.trans hAB⟩

/-- The sharper edge-source dichotomy used at the boundary: a mesh-sourced overlay edge lies
inside one actual edge of the already-subdivided square mesh. -/
theorem meshOverlay_edge_source_squareMesh (Q : TargetSegmentCover P)
    {delta : ℝ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ E(Q.meshOverlay delta fresh anchors)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      ∃ A ∈ E(squareMesh delta fresh anchors), R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, hA, hsub⟩
  · exact Or.inr ⟨A, mem_squareMeshPieces.1 hA, hsub⟩

/-- Two subsegments of one nondegenerate segment that start at the same end are comparable by
inclusion. -/
theorem segments_from_common_end_comparable {z a r s : Plane} (hza : z ≠ a)
    (hr : r ∈ segment ℝ z a) (hs : s ∈ segment ℝ z a) :
    segment ℝ z r ⊆ segment ℝ z s ∨ segment ℝ z s ⊆ segment ℝ z r := by
  rcases le_total (dist z r) (dist z s) with hrs | hsr
  · apply Or.inl
    apply (convex_segment z s).segment_subset (left_mem_segment ℝ z s)
    exact mem_segment_of_dist_le hza (left_mem_segment ℝ z a) hs hr
      (by simp) hrs
  · apply Or.inr
    apply (convex_segment z r).segment_subset (left_mem_segment ℝ z r)
    exact mem_segment_of_dist_le hza (left_mem_segment ℝ z a) hr hs
      (by simp) hsr

/-- Two pieces contained in the same nondegenerate source piece and sharing one of its ends
are comparable.  This is the piece-level form needed to identify two overlay fragments cut
from the unique square-mesh spoke at a fresh boundary point. -/
theorem piece_segments_comparable_of_common_source_end
    {A R S : Piece} {z : Plane} (hA : A.Nondeg)
    (hzA : z = A.1 ∨ z = A.2) (hRA : R.seg ⊆ A.seg) (hSA : S.seg ⊆ A.seg)
    (hzR : z = R.1 ∨ z = R.2) (hzS : z = S.1 ∨ z = S.2) :
    R.seg ⊆ S.seg ∨ S.seg ⊆ R.seg := by
  obtain ⟨a, hAseg, hza⟩ : ∃ a, A.seg = segment ℝ z a ∧ z ≠ a := by
    rcases hzA with hzA | hzA
    · refine ⟨A.2, ?_, ?_⟩
      · simp only [Piece.seg, hzA]
      · intro h
        exact hA (hzA.symm.trans h)
    · refine ⟨A.1, ?_, ?_⟩
      · simp only [Piece.seg, hzA, segment_symm]
      · intro h
        exact hA (h.symm.trans hzA)
  obtain ⟨r, hRseg, hrA⟩ : ∃ r, R.seg = segment ℝ z r ∧ r ∈ A.seg := by
    rcases hzR with hzR | hzR
    · exact ⟨R.2, by simp only [Piece.seg, hzR],
        hRA (right_mem_segment ℝ R.1 R.2)⟩
    · exact ⟨R.1, by simp only [Piece.seg, hzR, segment_symm],
        hRA (left_mem_segment ℝ R.1 R.2)⟩
  obtain ⟨s, hSseg, hsA⟩ : ∃ s, S.seg = segment ℝ z s ∧ s ∈ A.seg := by
    rcases hzS with hzS | hzS
    · exact ⟨S.2, by simp only [Piece.seg, hzS],
        hSA (right_mem_segment ℝ S.1 S.2)⟩
    · exact ⟨S.1, by simp only [Piece.seg, hzS, segment_symm],
        hSA (left_mem_segment ℝ S.1 S.2)⟩
  rw [hRseg, hSseg]
  exact segments_from_common_end_comparable hza (hAseg ▸ hrA) (hAseg ▸ hsA)

/-- Away from the vertices created by the overlay, an overlay edge meeting an old open target
edge is one of its subdivision pieces.  At a transverse crossing the common point is an overlay
vertex, so the hypothesis is intentionally false there. -/
theorem meshOverlay_edge_subset (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    ∀ ⦃e⦄, e ∈ E(P.str.skel) → ∀ ⦃R : Piece⦄,
      R ∈ E(Q.meshOverlay delta fresh anchors) →
      (edgeArc segmentDrawing R ∩
        (P.tgt.cell e \ V(Q.meshOverlay delta fresh anchors))).Nonempty →
      edgeArc segmentDrawing R ⊆ edgeArc P.tgt.drawing e := by
  intro e he R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ edgeArc P.tgt.drawing e := by
    rw [P.tgt.cell_edge hab] at hzCell
    exact hzCell.1
  have hznotOldVertex : z ∉ V(P.tgt.graph) := by
    intro hzV
    rcases P.tgt.isDrawing.vertex_mem_edgeArc (hab.map P.tgt.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.tgt.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.tgt.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have hzSkeleton : z ∈ P.tgt.skeletonSet :=
    P.tgt.cell_subset_skeletonSet (Or.inr he) hzCell
  have hzCover : z ∈ cover Q.pieces := by
    rw [Q.cover_eq]
    exact hzSkeleton
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, hAg⟩ := Q.source A hA
  have hzg : z ∈ edgeArc P.tgt.drawing g := hAg hzA
  have heg : e = g := P.tgt.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ edgeArc P.tgt.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.meshPieces delta fresh anchors)
        (anchors ++ P.tgt.graph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_left _ hA) hzA
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-- The combined overlay locally contains an edge subdivision of the old target drawing. -/
theorem target_isPlaneSubdivisionExtension (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    IsPlaneSubdivisionExtension P.tgt.graph P.tgt.drawing
      (Q.meshOverlay delta fresh anchors) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := P.tgt.isDrawing
  isDrawing := Q.meshOverlay_isDrawing hfresh delta anchors
  vertexSet_subset := Q.targetVertices_subset_meshOverlay hfresh delta anchors
  pointSet_subset := by
    change P.tgt.skeletonSet ⊆ _
    exact Q.targetSkeleton_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he R hR hmeet
    have heS : e ∈ E(P.str.skel) := by
      rwa [P.tgt.edgeSet_graph] at he
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heS
    apply Q.meshOverlay_edge_subset hfresh delta anchors heS hR
    obtain ⟨z, hzR, hze, hznot⟩ := hmeet
    refine ⟨z, hzR, ?_, hznot⟩
    rw [P.tgt.cell_edge hab]
    refine ⟨hze, ?_⟩
    intro hzEnds
    rcases hzEnds with hza | hzb
    · apply hznot
      rw [hza]
      exact Q.targetVertices_subset_meshOverlay hfresh delta anchors (by
        rw [P.tgt.vertexSet_graph]
        exact ⟨a, hab.left_mem, rfl⟩)
    · apply hznot
      rw [hzb]
      exact Q.targetVertices_subset_meshOverlay hfresh delta anchors (by
        rw [P.tgt.vertexSet_graph]
        exact ⟨b, hab.right_mem, rfl⟩)

/-- The combined overlay also locally contains an edge subdivision of the anchored square
mesh.  Using the mesh's already-subdivided edges as source pieces makes the proof immediate. -/
theorem squareMesh_isPlaneSubdivisionExtension (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    IsPlaneSubdivisionExtension (squareMesh delta fresh anchors) segmentDrawing
      (Q.meshOverlay delta fresh anchors) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := squareMesh_isDrawing hfresh delta anchors
  isDrawing := Q.meshOverlay_isDrawing hfresh delta anchors
  vertexSet_subset := Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
  pointSet_subset := Q.squareMesh_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he R hR hmeet
    obtain ⟨z, hzR, hze, hznot⟩ := hmeet
    obtain ⟨R', hR', hzR', hR'e⟩ :=
      exists_overlayPiece_mem_subset
        (points := attachPoints (Q.meshPieces delta fresh anchors)
          (anchors ++ P.tgt.graph.vertexFinset.toList))
        (P₀ := e) (List.mem_append_right Q.pieces (mem_squareMeshPieces.2 he))
        (by rwa [edgeArc_segmentDrawing] at hze)
    have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
      rwa [edgeArc_segmentDrawing]
    have hRR' : R = R' :=
      (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
        hR hR' hznot hzR hzR'Arc
    rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
    exact hR'e

/-- The old-target trace inside the combined overlay remains 2-connected. -/
theorem targetTrace_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    (Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
      P.tgt.skeletonSet).IsTwoConnected :=
  (Q.target_isPlaneSubdivisionExtension hfresh delta anchors).trace_isTwoConnected
    P.tgt_isWeaklyAdmissible.isTwoConnected

/-- Under the usual density hypotheses, the square-mesh trace inside the combined overlay
remains 2-connected. -/
theorem squareMeshTrace_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) :
    (Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
      (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)).IsTwoConnected :=
  (Q.squareMesh_isPlaneSubdivisionExtension hfresh delta anchors).trace_isTwoConnected
    (squareMesh_isTwoConnected hfresh hdense hdelta anchors)

/-- The combined target/mesh overlay is 2-connected.  The two subdivision traces are glued at
two distinct fresh boundary vertices, and together they contain every overlay vertex. -/
theorem meshOverlay_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) :
    (Q.meshOverlay delta fresh anchors).IsTwoConnected := by
  let T := Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
    P.tgt.skeletonSet
  let M := Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
    (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)
  have hT2 : T.IsTwoConnected := Q.targetTrace_isTwoConnected hfresh delta anchors
  have hM2 : M.IsTwoConnected :=
    Q.squareMeshTrace_isTwoConnected hfresh hdense hdelta anchors
  obtain ⟨z, hz, w, hw, hzw⟩ := exists_two_distinct_fresh_of_freshDense hdense hdelta
  have hzSquare : z ∈ V(squareMesh delta fresh anchors) :=
    end_mem_vertexSet_meshGraph (spokePiece_mem_meshSegments hz) (Or.inl rfl)
  have hwSquare : w ∈ V(squareMesh delta fresh anchors) :=
    end_mem_vertexSet_meshGraph (spokePiece_mem_meshSegments hw) (Or.inl rfl)
  have hzOverlay : z ∈ V(Q.meshOverlay delta fresh anchors) :=
    Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
      hzSquare
  have hwOverlay : w ∈ V(Q.meshOverlay delta fresh anchors) :=
    Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
      hwSquare
  have hzTarget : z ∈ P.tgt.skeletonSet := by
    apply P.tgt.outerSet_subset_skeletonSet
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hfresh z hz
  have hwTarget : w ∈ P.tgt.skeletonSet := by
    apply P.tgt.outerSet_subset_skeletonSet
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hfresh w hw
  have hzMesh : z ∈ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hzSquare
  have hwMesh : w ∈ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hwSquare
  have hzT : z ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hzOverlay, hzTarget⟩
  have hwT : w ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hwOverlay, hwTarget⟩
  have hzM : z ∈ V(M) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hzOverlay, hzMesh⟩
  have hwM : w ∈ V(M) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hwOverlay, hwMesh⟩
  have hcompat : T.Compatible M :=
    Graph.Compatible.of_le_le (Graph.traceGraph_le _) (Graph.traceGraph_le _)
  have hU2 : (T.union M).IsTwoConnected :=
    hT2.union hcompat hM2 hzw hzT hzM hwT hwM
  apply hU2.of_le_of_vertexSet_subset
    (Graph.union_le (Graph.traceGraph_le _) (Graph.traceGraph_le _))
  intro x hx
  rw [Graph.vertexSet_union]
  have hxPoint : x ∈ Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hx
  rw [Q.meshOverlay_pointSet] at hxPoint
  rcases hxPoint with hxTarget | hxMesh
  · exact Or.inl (by rw [Graph.traceGraph_vertexSet]; exact ⟨hx, hxTarget⟩)
  · exact Or.inr (by rw [Graph.traceGraph_vertexSet]; exact ⟨hx, hxMesh⟩)

/-- The combined overlay stays in the closed target square. -/
theorem meshOverlay_pointSet_subset (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing ⊆
      Plane.closedSquare 0 1 := by
  rw [Q.meshOverlay_pointSet]
  exact Set.union_subset P.tgt_isWeaklyAdmissible.skeletonSet_subset
    (squareMesh_pointSet_subset hfresh delta anchors)

/-- Every combined-overlay edge either lies on the model curve or is a polygonal edge whose
nonvertex points lie in the open target square.  A nonouter edge cannot meet the model curve
away from overlay vertices: the outer-ring segment through such a point would give a second
edge of the plane drawing there. -/
theorem meshOverlay_edge_dichotomy (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    ∀ ⦃R⦄, R ∈ E(Q.meshOverlay delta fresh anchors) →
      edgeArc segmentDrawing R ⊆ modelCurve ∨
        (IsPolygonal (edgeArc segmentDrawing R) ∧
          edgeArc segmentDrawing R \ V(Q.meshOverlay delta fresh anchors) ⊆
            Plane.closedSquare 0 1 \ modelCurve) := by
  intro R hR
  by_cases houter : edgeArc segmentDrawing R ⊆ modelCurve
  · exact Or.inl houter
  · refine Or.inr ⟨?_, ?_⟩
    · rw [edgeArc_segmentDrawing]
      exact isPolygonal_segment _ _
    · intro x hx
      refine ⟨Q.meshOverlay_pointSet_subset hfresh delta anchors
        (Graph.edgeArc_subset_pointSet hR hx.1), ?_⟩
      intro hxOuter
      have hxMeshOuter :
          x ∈ ⋃ A ∈ outerEdges (meshCount delta) fresh anchors, A.seg := by
        rw [squareMesh_cover_outerEdges]
        exact hxOuter
      obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hxMeshOuter
      obtain ⟨R', hR', hxR', hR'A⟩ :=
        exists_overlayPiece_mem_subset
          (points := attachPoints (Q.meshPieces delta fresh anchors)
            (anchors ++ P.tgt.graph.vertexFinset.toList))
          (P₀ := A) (List.mem_append_right Q.pieces
            (mem_squareMeshPieces.2 hA.1)) hxA
      have hxR'Arc : x ∈ edgeArc segmentDrawing R' := by
        rwa [edgeArc_segmentDrawing]
      have hRR' : R = R' :=
        (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
          hR hR' hx.2 hx.1 hxR'Arc
      apply houter
      rw [hRR', edgeArc_segmentDrawing]
      exact hR'A.trans hA.2

/-- New nonouter boundary edges of the combined overlay come from the square mesh and hence
end at prescribed fresh points.  Old-target-sourced overlay edges are already covered by every
trace containing the original target skeleton, so they cannot be new. -/
theorem newTargetBoundaryAnchored_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ) (anchors : List Plane) :
    NewTargetBoundaryAnchored P P.tgt.skeletonSet
      (Q.meshOverlay delta fresh anchors) segmentDrawing := by
  intro B hBH hbase R z hR hRnew hinc hz hnot
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hinc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  rcases Q.meshOverlay_edge_source_squareMesh hR with hOld | hMesh
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, hAe⟩ := Q.source A hA
    have hRbase : edgeArc segmentDrawing R ⊆ P.tgt.skeletonSet := by
      rw [edgeArc_segmentDrawing]
      exact hRA.trans (hAe.trans (Graph.edgeArc_subset_pointSet (by
        rw [P.tgt.edgeSet_graph]
        exact he)))
    exact (hRnew (edge_mem_of_edgeArc_subset_pointSet hdraw hBH hR
      (hRbase.trans hbase))).elim
  · obtain ⟨A, hA, hRA⟩ := hMesh
    have hzA : z ∈ A.seg := hRA hzRseg
    have hAnot : ¬ A.seg ⊆ modelCurve := by
      intro hAouter
      apply hnot
      rw [edgeArc_segmentDrawing]
      exact hRA.trans hAouter
    obtain ⟨w, hwFresh, hinter, -, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hinter ▸ ⟨hzA, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    rw [hzw]
    exact hstrong w hwFresh

/-- Fresh mesh anchors avoid the carriers of all old nonouter target edges.  This is the
finite cleanliness condition which separates a genuinely new spoke from the current target
trace at the distinguished boundary. -/
def FreshAvoidsTargetNonouterEdges
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (fresh : List Plane) : Prop :=
  ∀ z ∈ fresh, ∀ e ∈ E(P.str.skel), e ∉ E(P.str.outerGraph) →
    z ∉ edgeArc P.tgt.drawing e

/-- A nonouter target edge can meet the distinguished boundary only at an old target vertex.
This turns the cleanliness requirement into avoidance of one finite vertex set. -/
theorem mem_targetVertex_of_mem_nonouter_edgeArc_modelCurve
    {e : γ} (he : e ∈ E(P.str.skel)) (heNotOuter : e ∉ E(P.str.outerGraph))
    {z : Plane} (hze : z ∈ edgeArc P.tgt.drawing e) (hz : z ∈ modelCurve) :
    z ∈ V(P.tgt.graph) := by
  have hzOuter : z ∈ P.tgt.outerSet := by
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hz
  rcases hzOuter with hzV | hzE
  · exact (P.str.outerGraph_le.map P.tgt.pos).vertexSet_mono hzV
  · obtain ⟨f, hfOuter, hzf⟩ := Set.mem_iUnion₂.1 hzE
    have hf : f ∈ E(P.str.outerGraph) := by
      rwa [Graph.edgeSet_map] at hfOuter
    have heTgt : e ∈ E(P.tgt.graph) := by rwa [P.tgt.edgeSet_graph]
    have hfTgt : f ∈ E(P.tgt.graph) := by
      rw [P.tgt.edgeSet_graph]
      exact P.str.outerGraph_le.edgeSet_mono hf
    exact (P.tgt.isDrawing.edge_inter heTgt hfTgt
      (fun hef => heNotOuter (hef ▸ hf)) hze hzf).1

/-- Avoiding the finite old target vertex set is sufficient for clean fresh anchors. -/
theorem freshAvoidsTargetNonouterEdges_of_avoids_targetVertices
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (havoid : ∀ z ∈ fresh, z ∉ V(P.tgt.graph)) :
    FreshAvoidsTargetNonouterEdges P fresh := by
  intro z hzFresh e he heNotOuter hze
  exact havoid z hzFresh
    (mem_targetVertex_of_mem_nonouter_edgeArc_modelCurve he heNotOuter hze
      (hfresh z hzFresh))

/-- Incidence with an edge of the target/mesh overlay means being one of the two endpoints of
that piece. -/
theorem meshOverlay_inc_endpoint (Q : TargetSegmentCover P)
    {delta : ℝ} {fresh anchors : List Plane} {R : Piece} {z : Plane}
    (hinc : (Q.meshOverlay delta fresh anchors).Inc R z) :
    z = R.1 ∨ z = R.2 := by
  obtain ⟨w, hw⟩ := hinc
  change (overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList))).IsLink R z w at hw
  rcases (overlayGraph_isLink.1 hw).2 with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Two mesh-sourced, nonouter overlay edges incident at the same boundary point coincide.
The square mesh has one spoke there; both overlay pieces start at the boundary end of that
spoke, so their segment carriers are nested, and planarity identifies their edge names. -/
theorem meshOverlay_mesh_edges_eq_at_boundary (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) {z : Plane} (hz : z ∈ modelCurve)
    {R S : Piece} (hR : R ∈ E(Q.meshOverlay delta fresh anchors))
    (hS : S ∈ E(Q.meshOverlay delta fresh anchors))
    (hRinc : (Q.meshOverlay delta fresh anchors).Inc R z)
    (hSinc : (Q.meshOverlay delta fresh anchors).Inc S z)
    (hRnot : ¬ edgeArc segmentDrawing R ⊆ modelCurve)
    (hSnot : ¬ edgeArc segmentDrawing S ⊆ modelCurve)
    {A C : Piece} (hA : A ∈ E(squareMesh delta fresh anchors))
    (hC : C ∈ E(squareMesh delta fresh anchors))
    (hRA : R.seg ⊆ A.seg) (hSC : S.seg ⊆ C.seg) : R = S := by
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hRinc
  have hzSarc : z ∈ edgeArc segmentDrawing S := hdraw.inc_mem_edgeArc hSinc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  have hzSseg : z ∈ S.seg := by rwa [edgeArc_segmentDrawing] at hzSarc
  have hzA : z ∈ A.seg := hRA hzRseg
  have hzC : z ∈ C.seg := hSC hzSseg
  have hAnot : ¬ A.seg ⊆ modelCurve := by
    intro hAouter
    apply hRnot
    rw [edgeArc_segmentDrawing]
    exact hRA.trans hAouter
  have hCnot : ¬ C.seg ⊆ modelCurve := by
    intro hCouter
    apply hSnot
    rw [edgeArc_segmentDrawing]
    exact hSC.trans hCouter
  obtain ⟨w, hwFresh, hAw, hwA, -⟩ :=
    squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
  obtain ⟨v, hvFresh, hCv, hvC, -⟩ :=
    squareMesh_inner_edge_at_fresh hfresh delta hC ⟨z, hzC, hz⟩ hCnot
  have hzw : z = w := by
    have : z ∈ ({w} : Set Plane) := hAw ▸ ⟨hzA, hz⟩
    simpa only [Set.mem_singleton_iff] using this
  have hzv : z = v := by
    have : z ∈ ({v} : Set Plane) := hCv ▸ ⟨hzC, hz⟩
    simpa only [Set.mem_singleton_iff] using this
  have hzFresh : z ∈ fresh := hzw ▸ hwFresh
  have hzAend : z = A.1 ∨ z = A.2 := hzw ▸ hwA
  have hzCend : z = C.1 ∨ z = C.2 := hzv ▸ hvC
  obtain ⟨U, hU, huniq⟩ :=
    squareMesh_unique_inner_edge hfresh delta anchors hzFresh
  have hAU : A = U := huniq A ⟨hA, hzAend, hAnot⟩
  have hCU : C = U := huniq C ⟨hC, hzCend, hCnot⟩
  have hAC : A = C := hAU.trans hCU.symm
  have hSA : S.seg ⊆ A.seg := by rwa [hAC]
  have hcomp := piece_segments_comparable_of_common_source_end
    (meshGraph_edge_nondeg (two_le_meshCount delta) hfresh hA)
    hzAend hRA hSA (Q.meshOverlay_inc_endpoint hRinc)
      (Q.meshOverlay_inc_endpoint hSinc)
  rcases hcomp with hsub | hsub
  · exact eq_of_edgeArc_subset hdraw hR hS (by
      simpa only [edgeArc_segmentDrawing] using hsub)
  · exact (eq_of_edgeArc_subset hdraw hS hR (by
      simpa only [edgeArc_segmentDrawing] using hsub)).symm

/-- Under the finite cleanliness condition, no new nonouter overlay edge can meet a nonouter
edge of a trace already covering the old target skeleton at the distinguished boundary. -/
theorem noNewNonouterIncidenceAtBoundary_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (havoid : FreshAvoidsTargetNonouterEdges P fresh)
    (delta : ℝ) (anchors : List Plane) :
    NoNewNonouterIncidenceAtBoundary P.tgt.skeletonSet
      (Q.meshOverlay delta fresh anchors) segmentDrawing modelCurve := by
  intro B hBH hbase z R S hz hR hSB hRinc hSincB hRnot hSnot hRnew
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hS : S ∈ E(Q.meshOverlay delta fresh anchors) := hBH.edgeSet_mono hSB
  have hSinc : (Q.meshOverlay delta fresh anchors).Inc S z :=
    (hBH.inc_congr hSB).1 hSincB
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hRinc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  rcases Q.meshOverlay_edge_source_squareMesh hR with hROld | hRMesh
  · obtain ⟨A, hA, hRA⟩ := hROld
    obtain ⟨e, he, hAe⟩ := Q.source A hA
    have hRbase : edgeArc segmentDrawing R ⊆ P.tgt.skeletonSet := by
      rw [edgeArc_segmentDrawing]
      exact hRA.trans (hAe.trans (Graph.edgeArc_subset_pointSet (by
        rw [P.tgt.edgeSet_graph]
        exact he)))
    exact (hRnew (edge_mem_of_edgeArc_subset_pointSet hdraw hBH hR
      (hRbase.trans hbase))).elim
  · obtain ⟨A, hA, hRA⟩ := hRMesh
    have hzA : z ∈ A.seg := hRA hzRseg
    have hAnot : ¬ A.seg ⊆ modelCurve := by
      intro hAouter
      apply hRnot
      rw [edgeArc_segmentDrawing]
      exact hRA.trans hAouter
    obtain ⟨w, hwFresh, hAw, -, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hAw ▸ ⟨hzA, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    have hzFresh : z ∈ fresh := hzw ▸ hwFresh
    rcases Q.meshOverlay_edge_source_squareMesh hS with hSOld | hSMesh
    · obtain ⟨C, hC, hSC⟩ := hSOld
      obtain ⟨e, he, hCe⟩ := Q.source C hC
      have heNotOuter : e ∉ E(P.str.outerGraph) := by
        intro heOuter
        apply hSnot
        rw [edgeArc_segmentDrawing]
        apply hSC.trans
        apply hCe.trans
        intro x hx
        rw [← P.tgt_isWeaklyAdmissible.outerSet_eq]
        exact Graph.edgeArc_subset_pointSet (by
          rw [Graph.edgeSet_map]
          exact heOuter) hx
      apply havoid z hzFresh e he heNotOuter
      apply hCe
      apply hSC
      have hzSarc : z ∈ edgeArc segmentDrawing S := hdraw.inc_mem_edgeArc hSinc
      rwa [edgeArc_segmentDrawing] at hzSarc
    · obtain ⟨C, hC, hSC⟩ := hSMesh
      have hRS : R = S := Q.meshOverlay_mesh_edges_eq_at_boundary hfresh delta anchors
        hz hR hS hRinc hSinc hRnot hSnot hA hC hRA hSC
      exact hRnew (hRS ▸ hSB)

/-- The relative boundary anchoring of the overlay survives its injective edge renaming. -/
theorem newTargetBoundaryAnchored_relabelledMeshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors)) :
    NewTargetBoundaryAnchored P P.tgt.skeletonSet
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) := by
  intro B hBH hbase d z hd hdnew hinc hz hnot
  obtain ⟨R, hR, rfl⟩ := hd
  obtain ⟨R', hR', hR'name, hR'inc⟩ :=
    (Graph.relabelEdges_inc (Q.meshOverlay delta fresh anchors) name hname
      (name R) z).1 hinc
  have hR'R : R' = R := hname hR' hR hR'name
  subst R'
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hdrawRelabelled := hdraw.relabelEdges hname
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hR'inc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  have hRnot : ¬ edgeArc segmentDrawing R ⊆ modelCurve := by
    intro hsub
    apply hnot
    rwa [Graph.edgeArc_relabelDrawing hname hR]
  rcases Q.meshOverlay_edge_source_squareMesh hR with hOld | hMesh
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, hAe⟩ := Q.source A hA
    have hRbase :
        edgeArc ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing)
          (name R) ⊆ P.tgt.skeletonSet := by
      rw [Graph.edgeArc_relabelDrawing hname hR, edgeArc_segmentDrawing]
      exact hRA.trans (hAe.trans (Graph.edgeArc_subset_pointSet (by
        rw [P.tgt.edgeSet_graph]
        exact he)))
    exact (hdnew (edge_mem_of_edgeArc_subset_pointSet hdrawRelabelled hBH
      ⟨R, hR, rfl⟩ (hRbase.trans hbase))).elim
  · obtain ⟨A, hA, hRA⟩ := hMesh
    have hzA : z ∈ A.seg := hRA hzRseg
    have hAnot : ¬ A.seg ⊆ modelCurve := by
      intro hAouter
      apply hRnot
      rw [edgeArc_segmentDrawing]
      exact hRA.trans hAouter
    obtain ⟨w, hwFresh, hinter, -, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hinter ▸ ⟨hzA, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    rw [hzw]
    exact hstrong w hwFresh

/-- The relative no-new-incidence property of a clean overlay survives its injective edge
renaming. -/
theorem noNewNonouterIncidenceAtBoundary_relabelledMeshOverlay
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (havoid : FreshAvoidsTargetNonouterEdges P fresh)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors)) :
    NoNewNonouterIncidenceAtBoundary P.tgt.skeletonSet
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing)
      modelCurve := by
  intro B hBH hbase z d k hz hd hk hdinc hkinc hdnot hknot hdnew
  obtain ⟨R, hR, rfl⟩ := hd
  have hkH : k ∈ E((Q.meshOverlay delta fresh anchors).relabelEdges name hname) :=
    hBH.edgeSet_mono hk
  obtain ⟨S, hS, rfl⟩ := hkH
  obtain ⟨R', hR', hR'name, hR'inc⟩ :=
    (Graph.relabelEdges_inc (Q.meshOverlay delta fresh anchors) name hname
      (name R) z).1 hdinc
  have hR'R : R' = R := hname hR' hR hR'name
  subst R'
  have hSincRelabelled :
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname).Inc
        (name S) z := (hBH.inc_congr hk).1 hkinc
  obtain ⟨S', hS', hS'name, hS'inc⟩ :=
    (Graph.relabelEdges_inc (Q.meshOverlay delta fresh anchors) name hname
      (name S) z).1 hSincRelabelled
  have hS'S : S' = S := hname hS' hS hS'name
  subst S'
  have hdraw := Q.meshOverlay_isDrawing hfresh delta anchors
  have hdrawRelabelled := hdraw.relabelEdges hname
  have hRnot : ¬ edgeArc segmentDrawing R ⊆ modelCurve := by
    intro hsub
    apply hdnot
    rwa [Graph.edgeArc_relabelDrawing hname hR]
  have hSnot : ¬ edgeArc segmentDrawing S ⊆ modelCurve := by
    intro hsub
    apply hknot
    rwa [Graph.edgeArc_relabelDrawing hname hS]
  have hzRarc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hR'inc
  have hzRseg : z ∈ R.seg := by rwa [edgeArc_segmentDrawing] at hzRarc
  rcases Q.meshOverlay_edge_source_squareMesh hR with hROld | hRMesh
  · obtain ⟨A, hA, hRA⟩ := hROld
    obtain ⟨e, he, hAe⟩ := Q.source A hA
    have hRbase :
        edgeArc ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing)
          (name R) ⊆ P.tgt.skeletonSet := by
      rw [Graph.edgeArc_relabelDrawing hname hR, edgeArc_segmentDrawing]
      exact hRA.trans (hAe.trans (Graph.edgeArc_subset_pointSet (by
        rw [P.tgt.edgeSet_graph]
        exact he)))
    exact (hdnew (edge_mem_of_edgeArc_subset_pointSet hdrawRelabelled hBH
      ⟨R, hR, rfl⟩ (hRbase.trans hbase))).elim
  · obtain ⟨A, hA, hRA⟩ := hRMesh
    have hzA : z ∈ A.seg := hRA hzRseg
    have hAnot : ¬ A.seg ⊆ modelCurve := by
      intro hAouter
      apply hRnot
      rw [edgeArc_segmentDrawing]
      exact hRA.trans hAouter
    obtain ⟨w, hwFresh, hAw, -, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hA ⟨z, hzA, hz⟩ hAnot
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hAw ▸ ⟨hzA, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    have hzFresh : z ∈ fresh := hzw ▸ hwFresh
    rcases Q.meshOverlay_edge_source_squareMesh hS with hSOld | hSMesh
    · obtain ⟨C, hC, hSC⟩ := hSOld
      obtain ⟨e, he, hCe⟩ := Q.source C hC
      have heNotOuter : e ∉ E(P.str.outerGraph) := by
        intro heOuter
        apply hSnot
        rw [edgeArc_segmentDrawing]
        apply hSC.trans
        apply hCe.trans
        intro x hx
        rw [← P.tgt_isWeaklyAdmissible.outerSet_eq]
        exact Graph.edgeArc_subset_pointSet (by
          rw [Graph.edgeSet_map]
          exact heOuter) hx
      apply havoid z hzFresh e he heNotOuter
      apply hCe
      apply hSC
      have hzSarc : z ∈ edgeArc segmentDrawing S := hdraw.inc_mem_edgeArc hS'inc
      rwa [edgeArc_segmentDrawing] at hzSarc
    · obtain ⟨C, hC, hSC⟩ := hSMesh
      have hRS : R = S := Q.meshOverlay_mesh_edges_eq_at_boundary hfresh delta anchors
        hz hR hS hR'inc hS'inc hRnot hSnot hA hC hRA hSC
      exact hdnew (hRS ▸ hk)

/-- A quantitative local-width condition on the old open target skeleton.  Every point lies in
a connected subset containing two points farther apart than the proposed mesh scale. -/
def OpenTargetLocallyWiderThan (P : GeneratedPair S₀ srcOuter srcDom modelCurve
    (Plane.closedSquare 0 1)) (delta : ℝ) : Prop :=
  ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
    ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
      IsPreconnected A ∧ z ∈ A ∧
        ∃ x ∈ A, ∃ y ∈ A, delta < dist x y

/-- Finitely many nontrivial connected pieces cover the old open target skeleton.  This is the
purely target-side finiteness datum from which a uniform positive mesh scale is extracted. -/
structure FiniteOpenTargetCover
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) where
  /-- The connected pieces. -/
  pieces : List (Set Plane)
  /-- Every open-skeleton point lies in one listed piece. -/
  covers : ∀ z ∈ P.tgt.skeletonSet \ modelCurve, ∃ A ∈ pieces, z ∈ A
  /-- Every listed piece lies in the old open skeleton. -/
  subset_open : ∀ A ∈ pieces, A ⊆ P.tgt.skeletonSet \ modelCurve
  /-- Every listed piece is connected. -/
  preconnected : ∀ A ∈ pieces, IsPreconnected A
  /-- No listed piece is a singleton. -/
  nontrivial : ∀ A ∈ pieces, ∃ x ∈ A, ∃ y ∈ A, x ≠ y

/-- The interior of a nondegenerate arc contains two distinct points. -/
theorem IsArcBetween.exists_two_mem_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) :
    ∃ x ∈ A \ {p, q}, ∃ y ∈ A \ {p, q}, x ≠ y := by
  obtain ⟨f, -, hinj, himage, hzero, hone⟩ := h
  let x := f (1 / 3)
  let y := f (2 / 3)
  have hxI : (1 / 3 : ℝ) ∈ unitInterval := by norm_num [unitInterval]
  have hyI : (2 / 3 : ℝ) ∈ unitInterval := by norm_num [unitInterval]
  have hzeroI : (0 : ℝ) ∈ unitInterval := zero_mem_I
  have honeI : (1 : ℝ) ∈ unitInterval := one_mem_I
  have hxA : x ∈ A := by
    rw [← himage]
    exact ⟨1 / 3, hxI, rfl⟩
  have hyA : y ∈ A := by
    rw [← himage]
    exact ⟨2 / 3, hyI, rfl⟩
  have hxEnds : x ∉ ({p, q} : Set Plane) := by
    rintro (hxp | hxq)
    · have hfun : f (1 / 3) = f 0 := by
        calc f (1 / 3) = x := rfl
          _ = p := hxp
          _ = f 0 := hzero.symm
      have : (1 / 3 : ℝ) = 0 := hinj hxI hzeroI hfun
      norm_num at this
    · have hxq' : x = q := by simpa using hxq
      have hfun : f (1 / 3) = f 1 := by
        calc f (1 / 3) = x := rfl
          _ = q := hxq'
          _ = f 1 := hone.symm
      have : (1 / 3 : ℝ) = 1 := hinj hxI honeI hfun
      norm_num at this
  have hyEnds : y ∉ ({p, q} : Set Plane) := by
    rintro (hyp | hyq)
    · have hfun : f (2 / 3) = f 0 := by
        calc f (2 / 3) = y := rfl
          _ = p := hyp
          _ = f 0 := hzero.symm
      have : (2 / 3 : ℝ) = 0 := hinj hyI hzeroI hfun
      norm_num at this
    · have hyq' : y = q := by simpa using hyq
      have hfun : f (2 / 3) = f 1 := by
        calc f (2 / 3) = y := rfl
          _ = q := hyq'
          _ = f 1 := hone.symm
      have : (2 / 3 : ℝ) = 1 := hinj hyI honeI hfun
      norm_num at this
  refine ⟨x, ⟨hxA, hxEnds⟩, y, ⟨hyA, hyEnds⟩, ?_⟩
  intro hxy
  have : (1 / 3 : ℝ) = 2 / 3 := hinj hxI hyI hxy
  norm_num at this

/-- The finite family of nonouter target-edge carriers, with the model curve removed. -/
noncomputable def openTargetEdgePieces
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    List (Set Plane) := by
  classical
  let _ : P.str.skel.Finite :=
    ⟨P.str.finite_vertexSet, P.str.finite_edgeSet⟩
  exact (P.str.skel.edgeFinset.filter fun e => e ∉ E(P.str.outerGraph)).toList.map
    fun e => edgeArc P.tgt.drawing e \ modelCurve

@[simp] theorem mem_openTargetEdgePieces
    {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}
    {A : Set Plane} :
    A ∈ openTargetEdgePieces P ↔
      ∃ e ∈ E(P.str.skel), e ∉ E(P.str.outerGraph) ∧
        A = edgeArc P.tgt.drawing e \ modelCurve := by
  let _ : P.str.skel.Finite :=
    ⟨P.str.finite_vertexSet, P.str.finite_edgeSet⟩
  simp only [openTargetEdgePieces, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Graph.mem_edgeFinset]
  constructor
  · rintro ⟨e, ⟨he, hnot⟩, hEq⟩
    exact ⟨e, he, hnot, hEq.symm⟩
  · rintro ⟨e, he, hnot, hEq⟩
    exact ⟨e, ⟨he, hnot⟩, hEq.symm⟩

/-- The nonouter edge carriers form a finite connected, nontrivial cover of the whole old open
target skeleton. -/
noncomputable def finiteOpenTargetCover
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    FiniteOpenTargetCover P where
  pieces := openTargetEdgePieces P
  covers := by
    intro z hz
    have edge_mem_open : ∀ {e : γ}, e ∈ E(P.str.skel) →
        e ∉ E(P.str.outerGraph) → z ∈ edgeArc P.tgt.drawing e →
        ∃ A ∈ openTargetEdgePieces P, z ∈ A := by
      intro e he hnot hze
      refine ⟨edgeArc P.tgt.drawing e \ modelCurve,
        mem_openTargetEdgePieces.2 ⟨e, he, hnot, rfl⟩, hze, hz.2⟩
    rcases hz.1 with hzV | hzE
    · rw [P.tgt.vertexSet_graph] at hzV
      obtain ⟨v, hv, rfl⟩ := hzV
      have hvNotOuter : v ∉ V(P.str.outerGraph) := by
        intro hvOuter
        have hmem : P.tgt.pos v ∈ P.tgt.outerSet := Or.inl (by
          rw [Graph.vertexSet_map]
          exact ⟨v, hvOuter, rfl⟩)
        rw [P.tgt_isWeaklyAdmissible.outerSet_eq] at hmem
        exact hz.2 hmem
      obtain ⟨w, hw, hwv, -⟩ :=
        P.tgt_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne
          (P.tgt.pos v) (P.tgt.pos v)
      have hvReal : P.tgt.pos v ∈ V(P.tgt.graph) := by
        rw [P.tgt.vertexSet_graph]
        exact ⟨v, hv, rfl⟩
      obtain ⟨D, hD⟩ :=
        (P.tgt_isWeaklyAdmissible.isTwoConnected.connected.reaches hvReal hw).exists_isPath
      obtain ⟨e, -, hinc⟩ := hD.isWalk.exists_inc_source
        (hD.ne_nil (Ne.symm hwv))
      change (P.str.skel.map P.tgt.pos).Inc e (P.tgt.pos v) at hinc
      rw [Graph.map_inc] at hinc
      obtain ⟨a, hinca, hva⟩ := hinc
      have hav : v = a := P.tgt.injOn_pos hv hinca.vertex_mem hva
      have hincv : P.str.skel.Inc e v := by rwa [hav]
      obtain ⟨b, hab⟩ := hincv
      have heNotOuter : e ∉ E(P.str.outerGraph) := by
        intro heOuter
        have hlinkOuter := isLink_of_le_of_mem_edgeSet P.str.outerGraph_le heOuter hab
        exact hvNotOuter hlinkOuter.left_mem
      apply edge_mem_open hab.edge_mem heNotOuter
      have hArc := P.tgt.isDrawing.edge_isArcBetween (hab.map P.tgt.pos)
      exact hArc.left_mem
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
      have heS : e ∈ E(P.str.skel) := by rwa [P.tgt.edgeSet_graph] at he
      have heNotOuter : e ∉ E(P.str.outerGraph) := by
        intro heOuter
        have hmem : z ∈ P.tgt.outerSet := Or.inr (Set.mem_iUnion₂_of_mem (by
          rw [Graph.edgeSet_map]
          exact heOuter) hze)
        rw [P.tgt_isWeaklyAdmissible.outerSet_eq] at hmem
        exact hz.2 hmem
      exact edge_mem_open heS heNotOuter hze
  subset_open := by
    intro A hA
    obtain ⟨e, he, ⟨-, rfl⟩⟩ := mem_openTargetEdgePieces.1 hA
    exact Set.sdiff_subset_sdiff_left (Graph.edgeArc_subset_pointSet (by
      rwa [P.tgt.edgeSet_graph]))
  preconnected := by
    intro A hA
    obtain ⟨e, he, ⟨heNotOuter, rfl⟩⟩ := mem_openTargetEdgePieces.1 hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hArc := P.tgt.isDrawing.edge_isArcBetween (hab.map P.tgt.pos)
    have hcell : P.tgt.cell e =
        edgeArc P.tgt.drawing e \ {P.tgt.pos a, P.tgt.pos b} := P.tgt.cell_edge hab
    apply hArc.isPreconnected_diff.subset_closure
    · intro x hx
      have hxCell : x ∈ P.tgt.cell e := by
        rw [hcell]
        exact hx
      exact ⟨hx.1, (P.tgt_isWeaklyAdmissible.cell_subset he heNotOuter hxCell).2⟩
    · rw [Schoenflies.IsArcBetween.closure_diff_eq hArc]
      exact Set.sdiff_subset
  nontrivial := by
    intro A hA
    obtain ⟨e, he, ⟨heNotOuter, rfl⟩⟩ := mem_openTargetEdgePieces.1 hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hArc := P.tgt.isDrawing.edge_isArcBetween (hab.map P.tgt.pos)
    obtain ⟨x, hx, y, hy, hxy⟩ := IsArcBetween.exists_two_mem_diff hArc
    have hcell : P.tgt.cell e =
        edgeArc P.tgt.drawing e \ {P.tgt.pos a, P.tgt.pos b} := P.tgt.cell_edge hab
    have hsub : edgeArc P.tgt.drawing e \ {P.tgt.pos a, P.tgt.pos b} ⊆
        edgeArc P.tgt.drawing e \ modelCurve := by
      intro u hu
      have huCell : u ∈ P.tgt.cell e := by
        rw [hcell]
        exact hu
      exact ⟨hu.1, (P.tgt_isWeaklyAdmissible.cell_subset he heNotOuter huCell).2⟩
    exact ⟨x, hsub hx, y, hsub hy, hxy⟩

/-- A finite list of nontrivial sets has a uniform positive lower bound on one pairwise
distance chosen from each set. -/
theorem exists_uniform_piece_width (pieces : List (Set Plane))
    (hnontrivial : ∀ A ∈ pieces, ∃ x ∈ A, ∃ y ∈ A, x ≠ y) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ A ∈ pieces, ∃ x ∈ A, ∃ y ∈ A, delta < dist x y := by
  induction pieces with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons A pieces ih =>
      have htail : ∀ B ∈ pieces, ∃ x ∈ B, ∃ y ∈ B, x ≠ y :=
        fun B hB => hnontrivial B (List.mem_cons_of_mem A hB)
      obtain ⟨delta, hdelta, hwide⟩ := ih htail
      obtain ⟨x, hx, y, hy, hxy⟩ := hnontrivial A (List.mem_cons_self ..)
      let epsilon := min (delta / 2) (dist x y / 2)
      have hdist : 0 < dist x y := dist_pos.2 hxy
      have hepsilon : 0 < epsilon := by
        dsimp only [epsilon]
        positivity
      refine ⟨epsilon, hepsilon, ?_⟩
      intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · refine ⟨x, hx, y, hy, ?_⟩
        dsimp only [epsilon]
        linarith [min_le_right (delta / 2) (dist x y / 2)]
      · obtain ⟨u, hu, v, hv, huv⟩ := hwide B hB
        refine ⟨u, hu, v, hv, ?_⟩
        dsimp only [epsilon]
        linarith [min_le_left (delta / 2) (dist x y / 2)]

/-- A finite open-target cover supplies a positive scale at which every open-skeleton point
has a connected neighborhood wider than the mesh. -/
theorem FiniteOpenTargetCover.exists_locallyWiderThan
    (C : FiniteOpenTargetCover P) :
    ∃ delta : ℝ, 0 < delta ∧ OpenTargetLocallyWiderThan P delta := by
  obtain ⟨delta, hdelta, hwide⟩ :=
    exists_uniform_piece_width C.pieces C.nontrivial
  refine ⟨delta, hdelta, ?_⟩
  intro z hz
  obtain ⟨A, hA, hzA⟩ := C.covers z hz
  obtain ⟨x, hx, y, hy, hxy⟩ := hwide A hA
  exact ⟨A, C.subset_open A hA, C.preconnected A hA, hzA, x, hx, y, hy, hxy⟩

/-- The local-width condition is preserved when the proposed mesh scale is decreased. -/
theorem OpenTargetLocallyWiderThan.mono
    {delta epsilon : ℝ} (h : OpenTargetLocallyWiderThan P delta)
    (hle : epsilon ≤ delta) : OpenTargetLocallyWiderThan P epsilon := by
  intro z hz
  obtain ⟨A, hA, hconn, hzA, x, hx, y, hy, hxy⟩ := h z hz
  exact ⟨A, hA, hconn, hzA, x, hx, y, hy, lt_of_le_of_lt hle hxy⟩

/-- Every generated target has a positive mesh scale below `4` at which all of its open edge
pieces are wider than the mesh. -/
theorem exists_fine_openTarget_scale
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 4 ∧ OpenTargetLocallyWiderThan P delta := by
  obtain ⟨delta, hdelta, hwide⟩ :=
    (finiteOpenTargetCover P).exists_locallyWiderThan
  let epsilon := min delta 1
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  exact ⟨epsilon, hepsilon, lt_of_le_of_lt (min_le_right delta 1) (by norm_num),
    hwide.mono (min_le_left delta 1)⟩

/-- The locally-wide scale may be chosen below any prescribed positive bound. -/
theorem exists_fine_openTarget_scale_lt
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 4 ∧ delta < bound ∧
      OpenTargetLocallyWiderThan P delta := by
  obtain ⟨delta, hdelta, hwide⟩ :=
    (finiteOpenTargetCover P).exists_locallyWiderThan
  let epsilon := min delta (min 1 (bound / 2))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  refine ⟨epsilon, hepsilon,
    lt_of_le_of_lt (min_le_of_right_le (min_le_left 1 (bound / 2))) (by norm_num),
    ?_, hwide.mono (min_le_left delta (min 1 (bound / 2)))⟩
  have hle : epsilon ≤ bound / 2 :=
    (min_le_right delta (min 1 (bound / 2))).trans (min_le_right 1 (bound / 2))
  linarith

/-- A connected old-skeleton piece wider than the mesh scale must meet the mesh.  Otherwise the
radial mesh estimate bounds all of its pairwise distances by a number strictly below `delta`. -/
theorem mesh_hits_openTarget_of_locallyWider
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    {fresh : List Plane}
    {delta : ℝ} (hdelta : 0 < delta) (hdense : FreshDense fresh delta)
    (hwide : OpenTargetLocallyWiderThan P delta) (anchors : List Plane) :
    ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty := by
  intro z hz
  obtain ⟨A, hA, hAconn, hzA, x, hxA, y, hyA, hxy⟩ := hwide z hz
  refine ⟨A, hA, hAconn, hzA, ?_⟩
  have hmeet :
      (A ∩ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
    have hdisj : ∀ u ∈ A, u ∉ cover (meshSegments (meshCount delta) fresh) := by
      intro u huA huMesh
      apply hempty u
      refine ⟨huA, ?_⟩
      rwa [squareMesh_pointSet]
    have hzOpen := hA hzA
    have hzlt : Plane.supNorm z < 1 := by
      refine lt_of_le_of_ne
        (mem_closedSquare_zero_one.1
          (P.tgt_isWeaklyAdmissible.skeletonSet_subset hzOpen.1)) ?_
      exact hzOpen.2
    obtain ⟨-, hdist⟩ := radial_diam_bound (two_le_meshCount delta)
      (meshCount_spec hdelta).le hdense hAconn hdisj hzA hzlt
    have hNpos : (0 : ℝ) < meshCount delta := by
      exact_mod_cast Nat.zero_lt_of_lt (two_le_meshCount delta)
    have hthin : Real.sqrt 2 / (meshCount delta : ℝ) < delta / 2 := by
      rw [div_lt_div_iff₀ hNpos two_pos]
      linarith [meshCount_spec hdelta]
    have := hdist x hxA y hyA
    linarith
  obtain ⟨u, huA, huMesh⟩ := hmeet
  exact ⟨u, huA, huMesh, (hA huA).2⟩

/-- If every connected piece of the old open skeleton meets the connected open part of the
mesh, their union is connected.  This is the set-theoretic core of the quantitative
mesh-hitting argument. -/
theorem meshOverlay_isConnected_diff_of_hits (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {z₀ : Plane} (hz₀ : z₀ ∈ fresh) (delta : ℝ) (anchors : List Plane)
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsConnected
      (Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing \ modelCurve) := by
  let M := Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \ modelCurve
  have hM : IsConnected M := squareMesh_isConnected_diff hfresh delta anchors hz₀
  obtain ⟨r₀, hr₀⟩ := hM.nonempty
  have hunion : IsConnected ((P.tgt.skeletonSet \ modelCurve) ∪ M) := by
    refine ⟨⟨r₀, Or.inr hr₀⟩, isPreconnected_of_forall r₀ ?_⟩
    intro z hz
    rcases hz with hzOld | hzMesh
    · obtain ⟨A, hA, hAconn, hzA, w, hwA, hwM⟩ := hhit z hzOld
      refine ⟨A ∪ M, Set.union_subset (hA.trans subset_union_left) subset_union_right,
        Or.inr hr₀, Or.inl hzA, ?_⟩
      exact hAconn.union' ⟨w, hwA, hwM⟩ hM.isPreconnected
    · exact ⟨M, subset_union_right, hr₀, hzMesh, hM.isPreconnected⟩
  rw [Q.meshOverlay_pointSet]
  have heq :
      (P.tgt.skeletonSet ∪
          Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing) \ modelCurve =
        (P.tgt.skeletonSet \ modelCurve) ∪ M := by
    ext x
    constructor
    · rintro ⟨hxOld | hxMesh, hxOuter⟩
      · exact Or.inl ⟨hxOld, hxOuter⟩
      · exact Or.inr ⟨hxMesh, hxOuter⟩
    · rintro (⟨hxOld, hxOuter⟩ | ⟨hxMesh, hxOuter⟩)
      · exact ⟨Or.inl hxOld, hxOuter⟩
      · exact ⟨Or.inr hxMesh, hxOuter⟩
  rw [heq]
  exact hunion

/-- After injective edge relabelling, the combined overlay is a target extension as soon as its
two genuinely global assembly properties—2-connectivity and connectedness off the boundary—are
available.  Every local subdivision and geometric field is discharged above. -/
theorem isSourceExtension_relabelledMeshOverlay
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (htwo : (Q.meshOverlay delta fresh anchors).IsTwoConnected)
    (hconnected : IsConnected
      (Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing \ modelCurve)) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) where
  finite := Graph.Finite.relabelEdges hname
  isDrawing := (Q.meshOverlay_isDrawing hfresh delta anchors).relabelEdges hname
  isTwoConnected := htwo.relabelEdges hname
  vertexSet_subset := by
    rw [Graph.vertexSet_relabelEdges]
    exact Q.targetVertices_subset_meshOverlay hfresh delta anchors
  skeletonSet_subset := by
    rw [Graph.pointSet_relabelEdges hname]
    exact Q.targetSkeleton_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he d hd hmeet
    obtain ⟨R, hR, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hR,
      Graph.vertexSet_relabelEdges] at hmeet
    rw [Graph.edgeArc_relabelDrawing hname hR]
    exact Q.meshOverlay_edge_subset hfresh delta anchors he hR hmeet
  pointSet_subset := by
    rw [Graph.pointSet_relabelEdges hname]
    exact Q.meshOverlay_pointSet_subset hfresh delta anchors
  edge_dichotomy := by
    intro d hd
    obtain ⟨R, hR, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hR,
      Graph.vertexSet_relabelEdges]
    exact Q.meshOverlay_edge_dichotomy hfresh delta anchors hR
  isConnected := by
    rw [Graph.pointSet_relabelEdges hname]
    exact hconnected

/-- The mesh-hitting condition is enough to discharge the connectedness field of the target
extension.  Thus only 2-connectivity and the quantitative fact that the mesh meets every
connected piece of the old open skeleton remain. -/
theorem isSourceExtension_relabelledMeshOverlay_of_hits
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {z₀ : Plane} (hz₀ : z₀ ∈ fresh)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (htwo : (Q.meshOverlay delta fresh anchors).IsTwoConnected)
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) :=
  Q.isSourceExtension_relabelledMeshOverlay hfresh delta anchors name hname htwo
    (Q.meshOverlay_isConnected_diff_of_hits hfresh hz₀ delta anchors hhit)

/-- With a dense fresh boundary list, 2-connectivity and the nonempty-fresh requirement are
automatic.  The mesh-hitting condition is then the only remaining assembly hypothesis. -/
theorem isSourceExtension_relabelledMeshOverlay_of_dense_hits
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) := by
  obtain ⟨z, hz, -, -, -⟩ := exists_two_distinct_fresh_of_freshDense hdense hdelta
  exact Q.isSourceExtension_relabelledMeshOverlay_of_hits hfresh hz delta anchors name hname
    (Q.meshOverlay_isTwoConnected hfresh hdense hdelta anchors) hhit

/-- A sufficiently fine mesh gives the target extension from the local-width condition alone:
the radial diameter estimate supplies the mesh hits, while density supplies 2-connectivity. -/
theorem isSourceExtension_relabelledMeshOverlay_of_locallyWider
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdelta : 0 < delta) (hdense : FreshDense fresh delta)
    (hdelta4 : delta < 4) (hwide : OpenTargetLocallyWiderThan P delta)
    (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors)) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) :=
  Q.isSourceExtension_relabelledMeshOverlay_of_dense_hits hfresh hdense hdelta4 anchors
    name hname (mesh_hits_openTarget_of_locallyWider P hdelta hdense hwide anchors)

/-- There is a positive scale below `4` such that every dense anchored mesh at that scale,
after fresh injective edge relabelling, is a complete target source extension. -/
theorem exists_scale_isSourceExtension_relabelledMeshOverlay
    (Q : TargetSegmentCover P) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 4 ∧
      ∀ (fresh anchors : List Plane) (name : Piece → γ),
        (∀ z ∈ fresh, z ∈ modelCurve) → FreshDense fresh delta →
        (hname : InjOn name E(Q.meshOverlay delta fresh anchors)) →
        IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
          ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
          ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) := by
  obtain ⟨delta, hdelta, hdelta4, hwide⟩ := exists_fine_openTarget_scale P
  refine ⟨delta, hdelta, hdelta4, ?_⟩
  intro fresh anchors name hfresh hdense hname
  exact Q.isSourceExtension_relabelledMeshOverlay_of_locallyWider
    hfresh hdelta hdense hdelta4 hwide anchors name hname

/-- Fresh cell names for every edge of the combined target overlay, avoiding all names already
used by the current generated structure. -/
theorem exists_meshOverlay_edgeRelabeling
    [Infinite γ] (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) :
    ∃ name : Piece → γ, InjOn name E(Q.meshOverlay delta fresh anchors) ∧
      ∀ e ∈ E(Q.meshOverlay delta fresh anchors), name e ∉ P.str.cells :=
  exists_finiteGraph_edgeRelabeling_avoiding γ (Q.meshOverlay delta fresh anchors)
    P.str.cells P.str.finite_cells

/-- **Reverse finite transfer through the combined target/mesh overlay.**  Once the overlay is
a source extension, strong accessibility of its fresh anchors and avoidance of the finitely
many old nonouter target edges discharge all remaining reverse-ear hypotheses. -/
theorem finite_transfer_toward_source_relabelledMeshOverlay_of_outerCycle
    [Infinite γ] (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (havoid : FreshAvoidsTargetNonouterEdges P fresh)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (hH : IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing))
    (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
        (par : γ → γ),
      IsTargetTransferOf T P
        ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
        ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par :=
  finite_transfer_toward_source_of_relativeBoundaryGeometry hH
    (Q.newTargetBoundaryAnchored_relabelledMeshOverlay
      hfresh hstrong delta anchors name hname)
    (Q.noNewNonouterIncidenceAtBoundary_relabelledMeshOverlay
      hfresh havoid delta anchors name hname)
    hcycle

/-- At a locally wide scale, the dense clean overlay automatically supplies both the source
extension and its reverse finite transfer; fresh abstract edge names are chosen internally. -/
theorem exists_finite_transfer_toward_source_meshOverlay_of_locallyWider
    [Infinite γ] (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (havoid : FreshAvoidsTargetNonouterEdges P fresh)
    {delta : ℝ} (hdelta : 0 < delta) (hdense : FreshDense fresh delta)
    (hdelta4 : delta < 4) (hwide : OpenTargetLocallyWiderThan P delta)
    (anchors : List Plane) (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (name : Piece → γ) (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
        (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
        (par : γ → γ),
      IsTargetTransferOf T P
        ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
        ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par := by
  obtain ⟨name, hname, -⟩ := Q.exists_meshOverlay_edgeRelabeling delta fresh anchors
  have hH := Q.isSourceExtension_relabelledMeshOverlay_of_locallyWider
    hfresh hdelta hdense hdelta4 hwide anchors name hname
  obtain ⟨T, par, hT⟩ :=
    Q.finite_transfer_toward_source_relabelledMeshOverlay_of_outerCycle
      hfresh hstrong havoid delta anchors name hname hH hcycle
  exact ⟨name, hname, T, par, hT⟩

/-- Every generated target has one positive scale below `4` at which any dense, accessible,
clean fresh list produces the complete reverse finite transfer through the combined overlay. -/
theorem exists_scale_finite_transfer_toward_source_meshOverlay
    [Infinite γ] (Q : TargetSegmentCover P) (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 4 ∧
      ∀ (fresh anchors : List Plane),
        (∀ z ∈ fresh, z ∈ modelCurve) →
        (∀ z ∈ fresh,
          StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)) →
        FreshAvoidsTargetNonouterEdges P fresh → FreshDense fresh delta →
        ∃ (name : Piece → γ)
            (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
            (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
            (par : γ → γ),
          IsTargetTransferOf T P
            ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
            ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par := by
  obtain ⟨delta, hdelta, hdelta4, hwide⟩ := exists_fine_openTarget_scale P
  refine ⟨delta, hdelta, hdelta4, ?_⟩
  intro fresh anchors hfresh hstrong havoid hdense
  exact Q.exists_finite_transfer_toward_source_meshOverlay_of_locallyWider
    hfresh hstrong havoid hdelta hdense hdelta4 hwide anchors hcycle

/-- The complete reverse-transfer scale may be forced below any prescribed positive bound. -/
theorem exists_scale_finite_transfer_toward_source_meshOverlay_lt
    [Infinite γ] (Q : TargetSegmentCover P) (hcycle : S₀.OuterEdgesFormCycle)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 4 ∧ delta < bound ∧
      ∀ (fresh anchors : List Plane),
        (∀ z ∈ fresh, z ∈ modelCurve) →
        (∀ z ∈ fresh,
          StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)) →
        FreshAvoidsTargetNonouterEdges P fresh → FreshDense fresh delta →
        ∃ (name : Piece → γ)
            (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
            (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
            (par : γ → γ),
          IsTargetTransferOf T P
            ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
            ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par := by
  obtain ⟨delta, hdelta, hdelta4, hdeltabound, hwide⟩ :=
    exists_fine_openTarget_scale_lt P hbound
  refine ⟨delta, hdelta, hdelta4, hdeltabound, ?_⟩
  intro fresh anchors hfresh hstrong havoid hdense
  exact Q.exists_finite_transfer_toward_source_meshOverlay_of_locallyWider
    hfresh hstrong havoid hdelta hdense hdelta4 hwide anchors hcycle

end TargetSegmentCover

end Schoenflies
