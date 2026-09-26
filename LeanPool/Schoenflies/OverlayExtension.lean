/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SourceAttachment

/-!
# Extending an existing straight overlay

The final component-joining step of the local-grid construction starts from an already
subdivided straight inner overlay and appends one polygonal joining arc.  Reusing the original
source pieces would lose the old cut points.  Instead, this module lists the *current overlay
edges* as the new source pieces and retains every current vertex as a prescribed cut point.

The resulting overlay is automatically a plane subdivision of the old overlay.  This is the
finite straight-line engine needed before the wild outer graph and the joining ear are glued.
-/

public section

open Set
open scoped Graph

namespace Schoenflies

open _root_.Graph

namespace IsPlaneSubdivisionExtension

variable {β δ κ : Type*}
  {G : Graph Plane β} {Gdraw : β → ℝ → Plane}
  {H : Graph Plane δ} {Hdraw : δ → ℝ → Plane}
  {K : Graph Plane κ} {Kdraw : κ → ℝ → Plane}

/-- Plane subdivision extensions compose.  At a point of an old edge away from final vertices,
the intermediate carrier supplies an intermediate edge; both absorption clauses then apply. -/
theorem trans (hGH : IsPlaneSubdivisionExtension G Gdraw H Hdraw)
    (hHK : IsPlaneSubdivisionExtension H Hdraw K Kdraw) :
    IsPlaneSubdivisionExtension G Gdraw K Kdraw where
  finite := hHK.finite
  oldIsDrawing := hGH.oldIsDrawing
  isDrawing := hHK.isDrawing
  vertexSet_subset := hGH.vertexSet_subset.trans hHK.vertexSet_subset
  pointSet_subset := hGH.pointSet_subset.trans hHK.pointSet_subset
  edge_subset := by
    intro e he f hf hmeet
    obtain ⟨z, hzf, hze, hznotK⟩ := hmeet
    have hzH : z ∈ Graph.pointSet H Hdraw :=
      hGH.pointSet_subset (Graph.edgeArc_subset_pointSet he hze)
    rcases hzH with hzHV | hzHE
    · exact (hznotK (hHK.vertexSet_subset hzHV)).elim
    · obtain ⟨g, hg, hzg⟩ := Set.mem_iUnion₂.1 hzHE
      have hznotH : z ∉ V(H) := fun hzV => hznotK (hHK.vertexSet_subset hzV)
      exact (hHK.edge_subset hg hf ⟨z, hzf, hzg, hznotK⟩).trans
        (hGH.edge_subset he hg ⟨z, hzg, hze, hznotH⟩)

end IsPlaneSubdivisionExtension

/-- The already-subdivided edges of a finite straight overlay, listed as pieces. -/
noncomputable def currentOverlayPieces (pieces : List Piece) (extra : List Plane) : List Piece :=
  (attachGraph pieces extra).edgeFinset.toList

@[simp] theorem mem_currentOverlayPieces {pieces : List Piece} {extra : List Plane} {R : Piece} :
    R ∈ currentOverlayPieces pieces extra ↔ R ∈ E(attachGraph pieces extra) := by
  rw [currentOverlayPieces, Finset.mem_toList, Graph.mem_edgeFinset]

/-- Append further straight pieces to the current overlay edge list. -/
noncomputable def extendedOverlayPieces
    (pieces : List Piece) (extra : List Plane) (joins : List Piece) : List Piece :=
  currentOverlayPieces pieces extra ++ joins

/-- Re-overlay the current straight graph together with the joining pieces, retaining every
old vertex as a cut point. -/
noncomputable def extendOverlay
    (pieces : List Piece) (extra : List Plane) (joins : List Piece) : Graph Plane Piece :=
  attachGraph (extendedOverlayPieces pieces extra joins)
    (attachGraph pieces extra).vertexFinset.toList

instance extendOverlay_finite (pieces : List Piece) (extra : List Plane) (joins : List Piece) :
    (extendOverlay pieces extra joins).Finite := attachGraph_finite _ _

/-- Every current overlay edge is nondegenerate. -/
theorem currentOverlayPieces_nondeg {pieces : List Piece} {extra : List Plane}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) :
    ∀ R ∈ currentOverlayPieces pieces extra, R.Nondeg := by
  intro R hR
  have hRedge : R ∈ E(attachGraph pieces extra) := mem_currentOverlayPieces.1 hR
  change R ∈ overlayPieces pieces (attachPoints pieces extra) at hRedge
  exact overlayPieces_nondeg _ hpieces R hRedge

/-- The edge list of the current overlay has exactly the current overlay's carrier. -/
theorem cover_currentOverlayPieces (pieces : List Piece) (extra : List Plane) :
    cover (currentOverlayPieces pieces extra) =
      Graph.pointSet (attachGraph pieces extra) segmentDrawing := by
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ := mem_cover_iff.1 hx
    exact Graph.edgeArc_subset_pointSet (mem_currentOverlayPieces.1 hR) (by
      rwa [edgeArc_segmentDrawing])
  · intro hx
    rcases hx with hxV | hxE
    · change x ∈ V(overlayGraph pieces (attachPoints pieces extra)) at hxV
      obtain ⟨R, hR, hxR⟩ := hxV
      apply mem_cover_iff.2
      refine ⟨R, mem_currentOverlayPieces.2 hR, ?_⟩
      rcases hxR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.1 hxE
      exact mem_cover_iff.2 ⟨R, mem_currentOverlayPieces.2 hR, by
        rwa [edgeArc_segmentDrawing] at hxR⟩

/-- The extended overlay occupies exactly the old carrier together with the joining carrier. -/
theorem extendOverlay_pointSet
    (pieces : List Piece) (extra : List Plane) (joins : List Piece) :
    Graph.pointSet (extendOverlay pieces extra joins) segmentDrawing =
      Graph.pointSet (attachGraph pieces extra) segmentDrawing ∪ cover joins := by
  rw [extendOverlay, attachGraph_pointSet, extendedOverlayPieces, cover_append,
    cover_currentOverlayPieces]

/-- The extended overlay is a finite straight-line plane graph. -/
theorem extendOverlay_isDrawing
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg) :
    Graph.IsDrawing (extendOverlay pieces extra joins) segmentDrawing := by
  apply attachGraph_isDrawing
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact currentOverlayPieces_nondeg hpieces R hR
  · exact hjoins R hR

/-- Every old overlay vertex is retained by the extended overlay. -/
theorem attachGraphVertices_subset_extendOverlay
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg) :
    V(attachGraph pieces extra) ⊆ V(extendOverlay pieces extra joins) := by
  intro x hx
  change x ∈ V(overlayGraph (extendedOverlayPieces pieces extra joins)
    (attachPoints (extendedOverlayPieces pieces extra joins)
      (attachGraph pieces extra).vertexFinset.toList))
  apply overlayGraph_mem_vertexSet_of_mem_cover
  · intro R hR
    rcases List.mem_append.1 hR with hR | hR
    · exact currentOverlayPieces_nondeg hpieces R hR
    · exact hjoins R hR
  · apply mem_attachPoints_of_mem
    rw [Finset.mem_toList, Graph.mem_vertexFinset]
    exact hx
  · rw [extendedOverlayPieces, cover_append, cover_currentOverlayPieces]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- A new overlay edge meeting an old straight edge away from new vertices is one of its
subdivision pieces. -/
theorem extendOverlay_edge_subset
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg) :
    ∀ {A : Piece}, A ∈ E(attachGraph pieces extra) → ∀ {R : Piece},
      R ∈ E(extendOverlay pieces extra joins) →
      (Graph.edgeArc segmentDrawing R ∩
        (Graph.edgeArc segmentDrawing A \ V(extendOverlay pieces extra joins))).Nonempty →
      Graph.edgeArc segmentDrawing R ⊆ Graph.edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  obtain ⟨z, hzR, hzA, hznot⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (extendedOverlayPieces pieces extra joins)
        (attachGraph pieces extra).vertexFinset.toList)
      (P₀ := A)
      (List.mem_append_left joins (mem_currentOverlayPieces.2 hA))
      (by rwa [edgeArc_segmentDrawing] at hzA)
  have hzR'Arc : z ∈ Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (extendOverlay_isDrawing hpieces hjoins).unique_edge_at
      hR hR' hznot hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'A

/-- Every edge of the extended overlay is cut either from a current overlay edge or from one
of the newly appended pieces. -/
theorem extendOverlay_edge_source
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    {R : Piece} (hR : R ∈ E(extendOverlay pieces extra joins)) :
    (∃ A ∈ E(attachGraph pieces extra), R.seg ⊆ A.seg) ∨
      ∃ A ∈ joins, R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (extendedOverlayPieces pieces extra joins)
    (attachPoints (extendedOverlayPieces pieces extra joins)
      (attachGraph pieces extra).vertexFinset.toList) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, mem_currentOverlayPieces.1 hA, hsub⟩
  · exact Or.inr ⟨A, hA, hsub⟩

/-- Re-overlaying after adjoining joining pieces is a plane subdivision extension of the
current straight overlay. -/
theorem attachGraph_isPlaneSubdivisionExtension_extendOverlay
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg) :
    IsPlaneSubdivisionExtension (attachGraph pieces extra) segmentDrawing
      (extendOverlay pieces extra joins) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := attachGraph_isDrawing hpieces extra
  isDrawing := extendOverlay_isDrawing hpieces hjoins
  vertexSet_subset := attachGraphVertices_subset_extendOverlay hpieces hjoins
  pointSet_subset := by
    rw [extendOverlay_pointSet]
    exact subset_union_left
  edge_subset := by
    intro A hA R hR hmeet
    exact extendOverlay_edge_subset hpieces hjoins hA hR hmeet

/-- In particular, a 2-connected current overlay remains 2-connected on its exact traced
carrier after adjoining and subdividing the joining pieces. -/
theorem attachGraphTrace_isTwoConnected_extendOverlay
    {pieces : List Piece} {extra : List Plane} {joins : List Piece}
    (hpieces : ∀ R ∈ pieces, R.Nondeg) (hjoins : ∀ R ∈ joins, R.Nondeg)
    (htwo : (attachGraph pieces extra).IsTwoConnected) :
    (Graph.traceGraph (extendOverlay pieces extra joins) segmentDrawing
      (Graph.pointSet (attachGraph pieces extra) segmentDrawing)).IsTwoConnected :=
  (attachGraph_isPlaneSubdivisionExtension_extendOverlay hpieces hjoins).trace_isTwoConnected
    htwo

end Schoenflies
