/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicGraphPL
import LeanPool.ClassificationOfSurfaces.Moise.PlaneCycle

/-!
# Polygonal boundaries of intrinsic two-simplexes

The edge approximation of an intrinsic finite complex constructs each replacement edge in its
own finite line arrangement.  A two-cell extension needs the three edges of one abstract face in
one common plane complex.  This file enumerates only the one-dimensional arrangement faces which
actually carry those three edges, resolves all their segments simultaneously, and extracts the
resulting simple polygonal cycle.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- The selected replacement arc on cyclic edge `i` of the intrinsic face `t`. -/
noncomputable abbrev faceReplacementArc (t : K.Face) (i : ZMod 3) :=
  K.replacementArc hcont hinj D C (K.faceEdge t i)

/-- A one-dimensional face in the private arrangement of one replacement edge, together with
the proof that it is subordinate to that edge. -/
noncomputable abbrev FaceGraphSimplex (t : K.Face) (i : ZMod 3) :=
  {s : Finset (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.completeChain.arrangementMesh.toPlaneComplex.Vertex) //
    s ∈ (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        |>.completeChain.arrangementMesh.toPlaneComplex.simplexes) ∧
      s.card ≤ 2 ∧
      (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        |>.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s) ⊆
      (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        |>.completeCarrier)}

noncomputable instance faceGraphSimplexFintype (t : K.Face) (i : ZMod 3) :
    Fintype (FaceGraphSimplex (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i) :=
  by
    classical
    unfold FaceGraphSimplex
    infer_instance

/-- An ordered pair of vertices in a subordinate one-dimensional face, indexed also by the
abstract edge to which it belongs. -/
noncomputable abbrev FaceGraphSegment (t : K.Face) :=
  Σ i : ZMod 3, Σ s : FaceGraphSimplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i,
      ({v // v ∈ s.1} × {v // v ∈ s.1})

noncomputable instance faceGraphSegmentFintype (t : K.Face) :
    Fintype (FaceGraphSegment
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :=
  by
    classical
    unfold FaceGraphSegment
    infer_instance

/-- Segment labels for the common face arrangement.  The left summand lists actual graph
segments.  The right summand inserts the three abstract vertex images explicitly as degenerate
segments, making them canonical arrangement vertices. -/
noncomputable abbrev FaceBoundaryPiece (t : K.Face) :=
  FaceGraphSegment (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ⊕ ZMod 3

noncomputable instance faceBoundaryPieceFintype (t : K.Face) :
    Fintype (FaceBoundaryPiece
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :=
  by
    classical
    unfold FaceBoundaryPiece
    infer_instance

/-- The `faceGraphSegmentLeft` declaration. -/
noncomputable def faceGraphSegmentLeft (t : K.Face)
    (p : FaceGraphSegment (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1
    |>.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1)

/-- The `faceGraphSegmentRight` declaration. -/
noncomputable def faceGraphSegmentRight (t : K.Face)
    (p : FaceGraphSegment (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1
    |>.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1)

/-- The `faceBoundaryLeft` declaration. -/
noncomputable def faceBoundaryLeft (t : K.Face)
    (p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  Sum.elim (faceGraphSegmentLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (fun i => h (K.vertexPoint (K.faceUsedVertex t i))) p

/-- The `faceBoundaryRight` declaration. -/
noncomputable def faceBoundaryRight (t : K.Face)
    (p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Plane :=
  Sum.elim (faceGraphSegmentRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (fun i => h (K.vertexPoint (K.faceUsedVertex t i))) p

/-- The union of the three complete replacement-edge carriers around one intrinsic face. -/
def faceReplacementCarrier (t : K.Face) : Set Plane :=
  ⋃ i : ZMod 3,
    (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.completeCarrier)

/-- Every listed family segment lies in the replacement boundary carrier. -/
theorem faceBoundaryPiece_segment_subset (t : K.Face)
    (p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    segment ℝ
      (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
      (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) ⊆
      faceReplacementCarrier (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  classical
  rcases p with p | i
  · let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1
    have hleft : A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1 ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier p.2.1.1 :=
      subset_convexHull ℝ _ ⟨p.2.2.1.1, p.2.2.1.2, rfl⟩
    have hright : A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1 ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier p.2.1.1 :=
      subset_convexHull ℝ _ ⟨p.2.2.2.1, p.2.2.2.2, rfl⟩
    change segment ℝ
      (A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.1.1)
      (A.completeChain.arrangementMesh.toPlaneComplex.position p.2.2.2.1) ⊆ _
    exact (((convex_convexHull ℝ _).segment_subset hleft hright).trans
      p.2.1.2.2.2).trans (Set.subset_iUnion (fun j : ZMod 3 =>
        (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j
          |>.completeCarrier)) p.1)
  · change segment ℝ (h (K.vertexPoint (K.faceUsedVertex t i)))
      (h (K.vertexPoint (K.faceUsedVertex t i))) ⊆ _
    rw [segment_same]
    rintro x rfl
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    apply (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.vertex_mem_completeCarrier)
    simp [faceUsedVertex]

/-- Every boundary-carrier point lies on one of the explicitly indexed family segments. -/
theorem exists_faceBoundaryPiece_segment (t : K.Face) {x : Plane}
    (hx : x ∈ faceReplacementCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    ∃ p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t,
      x ∈ segment ℝ
        (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
        (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) := by
  classical
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  obtain ⟨s, hs, hxs, hsub, hcard⟩ := A.exists_completeTarget_face hxi
  obtain ⟨v, w, hvs, hws, hxvw⟩ :=
    A.completeChain.arrangementMesh.toPlaneComplex
      |>.exists_vertex_pair_segment_of_mem_cellCarrier hs hcard hxs
  let q : FaceGraphSimplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    ⟨s, hs, hcard, hsub⟩
  let p : FaceBoundaryPiece
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
    Sum.inl ⟨i, q, ⟨v, hvs⟩, ⟨w, hws⟩⟩
  refine ⟨p, ?_⟩
  exact hxvw

/-- The common auxiliary chain listing every relevant segment around one intrinsic face. -/
noncomputable def faceBoundaryChain (t : K.Face) : BrokenLineData (Set.univ : Set Plane) :=
  BrokenLineData.segmentFamilyChain
    (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)

/-- One finite plane complex carrying all three replacement edges face-to-face. -/
noncomputable abbrev faceBoundaryComplex (t : K.Face) : PlaneComplex :=
  (faceBoundaryChain (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
    |>.arrangementMesh.toPlaneComplex).restrictedTo
      (faceReplacementCarrier (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)

/-- The common face complex has exactly the union of the three replacement edges as support. -/
theorem faceBoundaryComplex_support (t : K.Face) :
    (faceBoundaryComplex (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).support =
      faceReplacementCarrier (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  classical
  let B := faceBoundaryChain (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  apply B.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨p, hxp⟩ := K.exists_faceBoundaryPiece_segment t hx
  obtain ⟨s, hs, hxs, hsSegment⟩ := BrokenLineData.exists_face_on_segmentFamily
    (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) p hxp
  refine ⟨s, hs, hxs, ?_⟩
  exact hsSegment.trans (K.faceBoundaryPiece_segment_subset t p)

/-- The explicit degenerate family piece used to mark abstract corner `i`. -/
noncomputable def faceVertexPiece (t : K.Face) (i : ZMod 3) :
    FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
  Sum.inr i

/-- The canonical common-arrangement vertex at abstract corner `i`. -/
noncomputable def faceBoundaryVertex (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex :=
  let left := faceBoundaryLeft
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let right := faceBoundaryRight
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  (BrokenLineData.segmentFamilyChain left right).arrangementVertex
    (BrokenLineData.segmentFamilyIndex left right (K.faceVertexPiece t i)).castSucc

theorem faceBoundaryVertex_position (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position
        (K.faceBoundaryVertex t i) = h (K.vertexPoint (K.faceUsedVertex t i)) := by
  exact BrokenLineData.segmentFamily_arrangementVertex_position_left _ _
    (K.faceVertexPiece t i)

private theorem singleton_cellCarrier_eq_position {L : PlaneComplex} (v : L.Vertex) :
    L.cellCarrier {v} = {L.position v} := by
  rw [PlaneComplex.cellCarrier]
  have himage : L.position '' (({v} : Finset L.Vertex) : Set L.Vertex) =
      {L.position v} := by ext x; simp
  rw [himage, convexHull_singleton]

/-- Every abstract corner is a zero-face of the common boundary complex. -/
theorem faceBoundaryVertex_face (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t i} : Finset
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex) ∈
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes := by
  classical
  let left := faceBoundaryLeft
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let right := faceBoundaryRight
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let B := BrokenLineData.segmentFamilyChain left right
  let q := BrokenLineData.segmentFamilyIndex left right (K.faceVertexPiece t i)
  apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
  refine ⟨B.arrangementVertex_face q.castSucc, ?_⟩
  change B.arrangementMesh.toPlaneComplex.cellCarrier
    {B.arrangementVertex q.castSucc} ⊆ _
  rw [singleton_cellCarrier_eq_position,
    BrokenLineData.segmentFamily_arrangementVertex_position_left]
  rintro x rfl
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  apply (faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
    |>.vertex_mem_completeCarrier)
  simp [faceUsedVertex]

/-- A family segment on edge `i` containing the given edge-carrier point, together with its
subordination to that one edge. -/
theorem exists_faceBoundaryPiece_segment_on_edge (t : K.Face) (i : ZMod 3) {x : Plane}
    (hx : x ∈ (faceReplacementArc
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier) :
    ∃ p : FaceBoundaryPiece (hcont := hcont) (hinj := hinj) (D := D) (C := C) t,
      x ∈ segment ℝ
        (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
        (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) ∧
      segment ℝ
        (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p)
        (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p) ⊆
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  classical
  let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  obtain ⟨s, hs, hxs, hsub, hcard⟩ := A.exists_completeTarget_face hx
  obtain ⟨v, w, hvs, hws, hxvw⟩ :=
    A.completeChain.arrangementMesh.toPlaneComplex
      |>.exists_vertex_pair_segment_of_mem_cellCarrier hs hcard hxs
  let q : FaceGraphSimplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    ⟨s, hs, hcard, hsub⟩
  let vq : {u // u ∈ q.1} := ⟨v, hvs⟩
  let wq : {u // u ∈ q.1} := ⟨w, hws⟩
  let p : FaceBoundaryPiece
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
    Sum.inl ⟨i, q, vq, wq⟩
  refine ⟨p, hxvw, ?_⟩
  have hvCarrier :
      A.completeChain.arrangementMesh.toPlaneComplex.position v ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s :=
    subset_convexHull ℝ _ ⟨v, hvs, rfl⟩
  have hwCarrier :
      A.completeChain.arrangementMesh.toPlaneComplex.position w ∈
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s :=
    subset_convexHull ℝ _ ⟨w, hws, rfl⟩
  exact ((convex_convexHull ℝ _).segment_subset hvCarrier hwCarrier).trans hsub

/-- The common arrangement has a face subordinate to edge `i` through every point of that
edge. -/
theorem exists_faceBoundary_face_on_edge (t : K.Face) (i : ZMod 3) {x : Plane}
    (hx : x ∈ (faceReplacementArc
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier) :
    ∃ s ∈ (faceBoundaryChain
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
      |>.arrangementMesh.toPlaneComplex.simplexes),
      x ∈ (faceBoundaryChain
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
        |>.arrangementMesh.toPlaneComplex.cellCarrier s) ∧
      (faceBoundaryChain
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
        |>.arrangementMesh.toPlaneComplex.cellCarrier s) ⊆
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  obtain ⟨p, hxp, hpSub⟩ := K.exists_faceBoundaryPiece_segment_on_edge t i hx
  obtain ⟨s, hs, hxs, hsSub⟩ := BrokenLineData.exists_face_on_segmentFamily
    (faceBoundaryLeft (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (faceBoundaryRight (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) p hxp
  exact ⟨s, hs, hxs, hsSub.trans hpSub⟩

/-- The subcomplex of the common face arrangement carried by cyclic edge `i`. -/
noncomputable abbrev faceEdgeComplex (t : K.Face) (i : ZMod 3) : PlaneComplex :=
  (faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).restrictedTo
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier

theorem faceEdgeComplex_support (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).support =
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  classical
  let B := faceBoundaryChain (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  apply (faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsub⟩ := K.exists_faceBoundary_face_on_edge t i hx
  have hsBoundary : s ∈ (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes := by
    apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
    exact ⟨hs, hsub.trans (Set.subset_iUnion (fun j : ZMod 3 =>
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j).completeCarrier) i)⟩
  exact ⟨s, hsBoundary, hxs, hsub⟩

private theorem faceBoundaryVertex_cellCarrier_subset_edge (t : K.Face)
    (i j : ZMod 3) (hj : j = i ∨ j = i + 1) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).cellCarrier
        {K.faceBoundaryVertex t j} ⊆
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  rw [singleton_cellCarrier_eq_position, K.faceBoundaryVertex_position t j]
  rintro x rfl
  apply (faceReplacementArc
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
      |>.vertex_mem_completeCarrier)
  rcases hj with rfl | rfl
  · simp [faceUsedVertex]
  · simp [faceUsedVertex]

theorem faceBoundaryVertex_face_edge_start (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t i} : Finset
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).Vertex) ∈
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).simplexes := by
  apply ((faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      |>.mem_restrictedTo_simplexes_iff _).mpr
  exact ⟨K.faceBoundaryVertex_face t i,
    K.faceBoundaryVertex_cellCarrier_subset_edge t i i (Or.inl rfl)⟩

theorem faceBoundaryVertex_face_edge_finish (t : K.Face) (i : ZMod 3) :
    ({K.faceBoundaryVertex t (i + 1)} : Finset
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).Vertex) ∈
      (faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).simplexes := by
  apply ((faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      |>.mem_restrictedTo_simplexes_iff _).mpr
  exact ⟨K.faceBoundaryVertex_face t (i + 1),
    K.faceBoundaryVertex_cellCarrier_subset_edge t i (i + 1) (Or.inr rfl)⟩

theorem isPreconnected_faceEdgeComplex_support (t : K.Face) (i : ZMod 3) :
    IsPreconnected (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).support := by
  rw [K.faceEdgeComplex_support t i]
  let A := faceReplacementArc (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  rw [← A.completeTarget_support]
  exact A.isPreconnected_completeTarget_support

/-- A loop-free path through cyclic replacement edge `i`, oriented from corner `i` to corner
`i+1`. -/
noncomputable def faceEdgeVertexPath (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).vertexGraph.Path
      (K.faceBoundaryVertex t i) (K.faceBoundaryVertex t (i + 1)) := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := ((faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
    |>.vertexGraph_reachable_of_isPreconnected
      (K.isPreconnected_faceEdgeComplex_support t i)
      (K.faceBoundaryVertex_face_edge_start t i)
      (K.faceBoundaryVertex_face_edge_finish t i)).exists_isPath
  exact ⟨⟨p, hp⟩⟩

theorem faceEdgeComplex_vertexGraph_le (t : K.Face) (i : ZMod 3) :
    (faceEdgeComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).vertexGraph ≤
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph := by
  intro v w hvw
  rw [(faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).vertexGraph_adj_iff] at hvw
  rw [(faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph_adj_iff]
  exact ⟨hvw.1, ((faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      |>.mem_restrictedTo_simplexes_iff _).mp hvw.2 |>.1⟩

/-- The oriented edge path, regarded in the common boundary complex. -/
noncomputable def faceBoundaryEdgePath (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph.Path
      (K.faceBoundaryVertex t i) (K.faceBoundaryVertex t (i + 1)) := by
  let p := K.faceEdgeVertexPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := (p.1.mapLe hle)
  refine ⟨q, ?_⟩
  exact p.property.mapLe hle

/-- Every vertex visited by the oriented path for edge `i` lies geometrically on that replacement
edge. -/
theorem faceBoundaryEdgePath_position_mem (t : K.Face) (i : ZMod 3)
    {v : (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hv : v ∈ (K.faceBoundaryEdgePath t i).1.support) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  let p := K.faceEdgeVertexPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  have hvLocal : v ∈ p.1.support := by
    change v ∈ (p.1.mapLe hle).support at hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact hv
  have hpos := (faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
      |>.position_mem_support_of_mem_walk
        p.1
        (K.faceBoundaryVertex_face_edge_finish t i) hvLocal
  rw [K.faceEdgeComplex_support t i] at hpos
  exact hpos

/-- The straight geometric path traced by the selected graph path on one replacement edge. -/
noncomputable def faceEdgeGeometricPath (t : K.Face) (i : ZMod 3) :
    Path
      ((faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).position
          (K.faceBoundaryVertex t i))
      ((faceEdgeComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).position
          (K.faceBoundaryVertex t (i + 1))) :=
  (faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).walkGeometricPath
      (K.faceEdgeVertexPath t i).1

/-- The selected finite graph path covers the entire polygonal replacement edge.  The key input
is that a connected subpath of an embedded arc containing both endpoints must be the whole arc. -/
theorem range_faceEdgeGeometricPath (t : K.Face) (i : ZMod 3) :
    Set.range (K.faceEdgeGeometricPath
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i) =
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  let B := faceEdgeComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let p := K.faceEdgeGeometricPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let e := K.faceEdge t i
  let A := faceReplacementArc
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  have hpSub : Set.range p ⊆ A.completeCarrier := by
    rw [← K.faceEdgeComplex_support t i]
    exact B.range_walkGeometricPath_subset_support
      (K.faceEdgeVertexPath t i).1 (K.faceBoundaryVertex_face_edge_finish t i)
  rcases K.faceEdge_endpoint_order t i with hforward | hreverse
  · have hsource : h (K.edgeFirstPoint e) =
        B.position (K.faceBoundaryVertex t i) := by
      calc
        h (K.edgeFirstPoint e) = h (K.vertexPoint (K.faceUsedVertex t i)) :=
          congrArg h (K.edgeFirstPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t i) hforward.1)
        _ = B.position (K.faceBoundaryVertex t i) := by
          symm
          exact K.faceBoundaryVertex_position t i
    have htarget : h (K.edgeSecondPoint e) =
        B.position (K.faceBoundaryVertex t (i + 1)) := by
      calc
        h (K.edgeSecondPoint e) = h (K.vertexPoint (K.faceUsedVertex t (i + 1))) :=
          congrArg h (K.edgeSecondPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t (i + 1)) hforward.2)
        _ = B.position (K.faceBoundaryVertex t (i + 1)) := by
          symm
          exact K.faceBoundaryVertex_position t (i + 1)
    let arc : Path
        (B.position (K.faceBoundaryVertex t i))
        (B.position (K.faceBoundaryVertex t (i + 1))) :=
      Path.copy A.completePath hsource htarget
    have harcRange : Set.range arc = A.completeCarrier := by
      exact (Path.copy_range A.completePath hsource htarget).trans A.range_completePath
    have harcInj : Function.Injective arc := by
      intro x y hxy
      exact A.completePath_injective hxy
    calc
      Set.range p = Set.range arc :=
        Path.range_eq_of_subset_of_injective arc p harcInj (harcRange.symm ▸ hpSub)
      _ = A.completeCarrier := harcRange
  · have hsource : h (K.edgeSecondPoint e) =
        B.position (K.faceBoundaryVertex t i) := by
      calc
        h (K.edgeSecondPoint e) = h (K.vertexPoint (K.faceUsedVertex t i)) :=
          congrArg h (K.edgeSecondPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t i) hreverse.2)
        _ = B.position (K.faceBoundaryVertex t i) := by
          symm
          exact K.faceBoundaryVertex_position t i
    have htarget : h (K.edgeFirstPoint e) =
        B.position (K.faceBoundaryVertex t (i + 1)) := by
      calc
        h (K.edgeFirstPoint e) = h (K.vertexPoint (K.faceUsedVertex t (i + 1))) :=
          congrArg h (K.edgeFirstPoint_eq_vertexPoint_of_eq e
            (K.faceUsedVertex t (i + 1)) hreverse.1)
        _ = B.position (K.faceBoundaryVertex t (i + 1)) := by
          symm
          exact K.faceBoundaryVertex_position t (i + 1)
    let arc : Path
        (B.position (K.faceBoundaryVertex t i))
        (B.position (K.faceBoundaryVertex t (i + 1))) :=
      Path.copy A.completePath.symm hsource htarget
    have harcRange : Set.range arc = A.completeCarrier := by
      exact (Path.copy_range A.completePath.symm hsource htarget).trans
        ((Path.symm_range A.completePath).trans A.range_completePath)
    have harcInj : Function.Injective arc := by
      intro x y hxy
      change A.completePath.symm x = A.completePath.symm y at hxy
      change A.completePath (unitInterval.symm x) =
          A.completePath (unitInterval.symm y) at hxy
      exact unitInterval.symm_bijective.injective (A.completePath_injective hxy)
    calc
      Set.range p = Set.range arc :=
        Path.range_eq_of_subset_of_injective arc p harcInj (harcRange.symm ▸ hpSub)
      _ = A.completeCarrier := harcRange

/-- The same edge path, mapped into the common face-boundary complex, still covers the complete
replacement edge. -/
theorem range_faceBoundaryEdgePath (t : K.Face) (i : ZMod 3) :
    Set.range ((faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).walkGeometricPath
        (K.faceBoundaryEdgePath t i).1) =
      (faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier := by
  let B := faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let A := faceReplacementArc
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let p := K.faceEdgeVertexPath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let hle := K.faceEdgeComplex_vertexGraph_le
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  calc
    Set.range (B.walkGeometricPath (K.faceBoundaryEdgePath t i).1) =
        Set.range ((B.restrictedTo A.completeCarrier).walkGeometricPath p.1) := by
      exact B.range_walkGeometricPath_mapLe_restrictedTo A.completeCarrier p.1 hle
    _ = A.completeCarrier := K.range_faceEdgeGeometricPath t i

/-- Distinct cyclic corners remain distinct as vertices of the common arrangement. -/
theorem faceBoundaryVertex_ne_next (t : K.Face) (i : ZMod 3) :
    K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i ≠
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1) := by
  intro hv
  have hpos := congrArg
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position hv
  rw [K.faceBoundaryVertex_position t i,
    K.faceBoundaryVertex_position t (i + 1)] at hpos
  have hused : K.faceUsedVertex t i = K.faceUsedVertex t (i + 1) :=
    K.injective_vertexPoint (hinj hpos)
  exact K.faceVertex_ne_next t i
    (congrArg (fun v : K.UsedVertex => v.1) hused)

/-- Every oriented replacement-edge path contains at least one edge. -/
theorem faceBoundaryEdgePath_length_pos (t : K.Face) (i : ZMod 3) :
    0 < (K.faceBoundaryEdgePath
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.length := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact K.faceBoundaryVertex_ne_next t i
    (SimpleGraph.Walk.eq_of_length_eq_zero hzero)

/-- Consecutive replacement-edge paths share only their common endpoint, which is removed from
the tail of the second path. -/
theorem faceBoundaryEdgePath_support_disjoint_next_tail (t : K.Face) (i : ZMod 3) :
    List.Disjoint
      (K.faceBoundaryEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.support
      (K.faceBoundaryEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)).1.support.tail := by
  classical
  rw [List.disjoint_left]
  intro v hvi hvnext
  have hposi := K.faceBoundaryEdgePath_position_mem
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i hvi
  have hposnext := K.faceBoundaryEdgePath_position_mem
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
      (List.tail_subset _ hvnext)
  have hinter :
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier ∩
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)).completeCarrier :=
    ⟨hposi, hposnext⟩
  rw [K.faceReplacementCarrier_inter_next hcont hinj D C t i] at hinter
  have hposition :
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
        h (K.vertexPoint (K.faceUsedVertex t (i + 1))) :=
    Set.mem_singleton_iff.mp hinter
  have hvCorner : v = K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1) :=
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position_injective
        (hposition.trans (K.faceBoundaryVertex_position t (i + 1)).symm)
  subst v
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  have hn := p.property.support_nodup
  rw [← p.1.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hvnext

/-- The first two oriented replacement edges form a simple path from corner `i` to the second
cyclic successor of `i`.  The unreduced successor expression keeps dependent elaboration cheap. -/
noncomputable def faceBoundaryTwoEdgePath (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph.Path
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)) := by
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  refine ⟨p.1.append q.1, ?_⟩
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨p.property.support_nodup, q.property.support_nodup.tail,
    K.faceBoundaryEdgePath_support_disjoint_next_tail
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i⟩

/-- The tail of the first two boundary edges is disjoint from the tail of the closing edge. -/
theorem faceBoundaryTwoEdgePath_tail_disjoint_closing_tail (t : K.Face) (i : ZMod 3) :
    List.Disjoint
      (K.faceBoundaryTwoEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.support.tail
      (K.faceBoundaryEdgePath
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
          (i + 1 + 1)).1.support.tail := by
  classical
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  rw [List.disjoint_left]
  intro v hvTwo hvr
  change v ∈ (p.1.append q.1).support.tail at hvTwo
  change v ∈ r.1.support.tail at hvr
  rw [SimpleGraph.Walk.tail_support_append, List.mem_append] at hvTwo
  rcases hvTwo with hvp | hvq
  · have hposp := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
        (List.tail_subset _ hvp)
    have hposr := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
        (List.tail_subset _ hvr)
    have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
    have hcycle : i + 1 + 1 + 1 = i := by
      calc
        i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
        _ = i + 0 := by rw [hthree]
        _ = i := add_zero i
    have hposp' :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1 + 1)).completeCarrier := by
      rw [hcycle]
      exact hposp
    have hinter :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1)).completeCarrier ∩
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1 + 1)).completeCarrier :=
      ⟨hposr, hposp'⟩
    rw [K.faceReplacementCarrier_inter_next hcont hinj D C t (i + 1 + 1)] at hinter
    have hpositionRaw :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
          h (K.vertexPoint (K.faceUsedVertex t (i + 1 + 1 + 1))) :=
      Set.mem_singleton_iff.mp hinter
    have hposition :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
          h (K.vertexPoint (K.faceUsedVertex t i)) := by
      rw [hcycle] at hpositionRaw
      exact hpositionRaw
    have hvCorner : v = K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position_injective
          (hposition.trans (K.faceBoundaryVertex_position t i).symm)
    subst v
    have hn := p.property.support_nodup
    rw [← p.1.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 hvp
  · have hposq := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
        (List.tail_subset _ hvq)
    have hposr := K.faceBoundaryEdgePath_position_mem
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
        (List.tail_subset _ hvr)
    have hinter :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v ∈
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1)).completeCarrier ∩
          (faceReplacementArc
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              (i + 1 + 1)).completeCarrier :=
      ⟨hposq, hposr⟩
    rw [K.faceReplacementCarrier_inter_next hcont hinj D C t (i + 1)] at hinter
    have hposition :
        (faceBoundaryComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position v =
          h (K.vertexPoint (K.faceUsedVertex t (i + 1 + 1))) :=
      Set.mem_singleton_iff.mp hinter
    have hvCorner : v = K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1) :=
      (faceBoundaryComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).position_injective
          (hposition.trans (K.faceBoundaryVertex_position t (i + 1 + 1)).symm)
    subst v
    have hn := r.property.support_nodup
    rw [← r.1.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 hvr

/-- The two-edge boundary path has length at least two. -/
theorem one_lt_faceBoundaryTwoEdgePath_length (t : K.Face) (i : ZMod 3) :
    1 < (K.faceBoundaryTwoEdgePath
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).1.length := by
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  change 1 < (p.1.append q.1).length
  rw [SimpleGraph.Walk.length_append]
  have hp := K.faceBoundaryEdgePath_length_pos
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  have hq := K.faceBoundaryEdgePath_length_pos
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  change 0 < p.1.length at hp
  change 0 < q.1.length at hq
  omega

/-- The three oriented replacement-edge paths, with the final cyclic endpoint identified. -/
noncomputable def faceBoundaryCycleWalk (t : K.Face) (i : ZMod 3) :
    (faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).vertexGraph.Walk
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)
      (K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i) := by
  let p := K.faceBoundaryTwoEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j) hcycle
  exact p.1.append (r.1.copy rfl hend)

/-- The boundary walk extracted from the common arrangement is a simple graph cycle. -/
theorem faceBoundaryCycleWalk_isCycle (t : K.Face) (i : ZMod 3) :
    (K.faceBoundaryCycleWalk
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).IsCycle := by
  let p := K.faceBoundaryTwoEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j) hcycle
  change (p.1.append (r.1.copy rfl hend)).IsCycle
  apply p.property.isCycle_append
  · exact (SimpleGraph.Walk.isPath_copy r.1 rfl hend).mpr r.property
  · simpa only [SimpleGraph.Walk.support_copy] using
      K.faceBoundaryTwoEdgePath_tail_disjoint_closing_tail
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  · exact Or.inl (K.one_lt_faceBoundaryTwoEdgePath_length
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i)

/-- The geometric range of the boundary cycle is the union of its three complete replacement
edges. -/
theorem range_faceBoundaryCycleWalk (t : K.Face) (i : ZMod 3) :
    Set.range ((faceBoundaryComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).walkGeometricPath
        (K.faceBoundaryCycleWalk t i)) =
      (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier ∪
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            (i + 1)).completeCarrier ∪
        (faceReplacementArc
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            (i + 1 + 1)).completeCarrier := by
  let B := faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let p := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i
  let q := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1)
  let r := K.faceBoundaryEdgePath
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1)
  have hthree : (1 : ZMod 3) + 1 + 1 = 0 := by decide
  have hcycle : i + 1 + 1 + 1 = i := by
    calc
      i + 1 + 1 + 1 = i + (1 + 1 + 1) := by abel
      _ = i + 0 := by rw [hthree]
      _ = i := add_zero i
  have hend : K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t (i + 1 + 1 + 1) =
      K.faceBoundaryVertex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i :=
    congrArg (fun j => K.faceBoundaryVertex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j) hcycle
  change Set.range (B.walkGeometricPath
    ((p.1.append q.1).append (r.1.copy rfl hend))) = _
  rw [B.range_walkGeometricPath_append, B.range_walkGeometricPath_append,
    B.range_walkGeometricPath_copy, K.range_faceBoundaryEdgePath t i,
    K.range_faceBoundaryEdgePath t (i + 1),
    K.range_faceBoundaryEdgePath t (i + 1 + 1)]

/-- The simple polygonal circle formed by the three replacement edges around `t`. -/
noncomputable def facePolygonalCircle (t : K.Face) : PolygonalCircle :=
  (faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).polygonalCircleOfCycle
      (K.faceBoundaryCycleWalk
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0)
      (K.faceBoundaryCycleWalk_isCycle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0)

/-- The extracted polygonal circle has exactly the prescribed three-edge replacement boundary. -/
theorem facePolygonalCircle_carrier (t : K.Face) :
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier =
      K.faceReplacementCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  let B := faceBoundaryComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let p := K.faceBoundaryCycleWalk
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0
  let hp := K.faceBoundaryCycleWalk_isCycle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t 0
  rw [show K.facePolygonalCircle t = B.polygonalCircleOfCycle p hp by rfl,
    B.polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath p hp,
    K.range_faceBoundaryCycleWalk t 0]
  let E : ZMod 3 → Set Plane := fun i =>
    (K.faceReplacementArc
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t i).completeCarrier
  change E 0 ∪ E (0 + 1) ∪ E (0 + 1 + 1) = ⋃ i, E i
  have hone : (0 : ZMod 3) + 1 = 1 := by decide
  have htwo : (1 : ZMod 3) + 1 = 2 := by decide
  rw [hone, htwo]
  apply Set.Subset.antisymm
  · exact Set.union_subset
      (Set.union_subset
        (Set.subset_iUnion E 0)
        (Set.subset_iUnion E 1))
      (Set.subset_iUnion E 2)
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl (Or.inl hxi)
    · exact Or.inl (Or.inr hxi)
    · exact Or.inr hxi

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
