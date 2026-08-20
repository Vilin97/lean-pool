/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicGraphPL
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceBoundary
import LeanPool.ClassificationOfSurfaces.Moise.PLApproximation

/-!
# A conforming plane model of an intrinsic replacement graph

The first intrinsic graph replacement need not be metrically close to the original embedding;
its role here is to polygonalize the abstract finite graph once.  A common segment arrangement
turns all replacement edges into one plane graph complex.  The original embedding can then be
transferred to that plane complex and the ordinary plane one-skeleton approximation theorem can
be applied at an arbitrary tolerance.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

/-- A nonempty face of cardinality at most two is the segment between two (possibly equal)
vertex positions. -/
theorem exists_cellCarrier_eq_segment (L : PlaneComplex)
    {s : Finset L.Vertex} (hs : s ∈ L.simplexes) (hcard : s.card ≤ 2) :
    ∃ a b : Plane, L.cellCarrier s = segment ℝ a b := by
  have hpos : 0 < s.card := Finset.card_pos.mpr (L.nonempty_of_mem s hs)
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
    refine ⟨L.position v, L.position v, ?_⟩
    simp [PlaneComplex.cellCarrier]
  · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp htwo
    refine ⟨L.position v, L.position w, ?_⟩
    rw [PlaneComplex.cellCarrier]
    have himage :
        L.position '' (↑({v, w} : Finset L.Vertex) : Set L.Vertex) =
          {L.position v, L.position w} := by
      ext x
      simp [eq_comm]
    rw [himage, convexHull_pair]

end PlaneComplex

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- A one- or two-vertex face from one finite complete-edge target complex.  These faces form a
finite segment cover of the corresponding complete replacement edge. -/
abbrev ReplacementSegmentFace :=
  Σ e : K.Edge,
    {s : Finset (K.replacementArc hcont hinj D C e).completeTarget.Vertex //
      s ∈ (K.replacementArc hcont hinj D C e).completeTarget.simplexes ∧ s.card ≤ 2}

private theorem replacementSegmentFace_has_endpoints
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    ∃ a b : Plane,
      (K.replacementArc hcont hinj D C q.1).completeTarget.cellCarrier q.2.1 =
        segment ℝ a b :=
  (K.replacementArc hcont hinj D C q.1).completeTarget.exists_cellCarrier_eq_segment
    q.2.2.1 q.2.2.2

/-- First endpoint of a selected replacement segment. -/
noncomputable def replacementSegmentLeft
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) : Plane :=
  Classical.choose (K.replacementSegmentFace_has_endpoints q)

/-- Second endpoint of a selected replacement segment. -/
noncomputable def replacementSegmentRight
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) : Plane :=
  Classical.choose (Classical.choose_spec (K.replacementSegmentFace_has_endpoints q))

theorem replacementSegment_eq_cellCarrier
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q) =
      (K.replacementArc hcont hinj D C q.1).completeTarget.cellCarrier q.2.1 := by
  exact (Classical.choose_spec
    (Classical.choose_spec (K.replacementSegmentFace_has_endpoints q))).symm

/-- Union of all selected segment faces over all complete replacement edges. -/
def replacementGraphCarrier : Set Plane :=
  ⋃ q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C),
    segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q)

/-- The common arrangement used to reconcile every edge's independent finite target complex. -/
noncomputable def replacementGraphArrangement : BrokenLineData (Set.univ : Set Plane) :=
  BrokenLineData.segmentFamilyChain
    (K.replacementSegmentLeft
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    (K.replacementSegmentRight
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))

/-- Restrict the common arrangement to the actual replacement segments. -/
noncomputable def replacementGraphBaseComplex : PlaneComplex :=
  (K.replacementGraphArrangement
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).arrangementMesh.toPlaneComplex
    |>.restrictToSet (K.replacementGraphCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))

/-- The conforming finite plane graph complex of the simultaneous intrinsic replacement. -/
noncomputable def replacementGraphComplex : PlaneComplex :=
  (K.replacementGraphBaseComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)).oneSkeleton

private theorem exists_replacementGraphBase_face
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    {x : Plane}
    (hx : x ∈ segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q)) :
    ∃ s ∈ (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes,
      x ∈ (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ∧
      (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ⊆
        segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q) ∧
      s.card ≤ 2 := by
  let left := K.replacementSegmentLeft
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  let right := K.replacementSegmentRight
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  obtain ⟨s, hs, hxs, hsSegment⟩ :=
    BrokenLineData.exists_face_on_segmentFamily left right q hx
  have hsCarrier :
      (K.replacementGraphArrangement).arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        K.replacementGraphCarrier
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
    exact hsSegment.trans (Set.subset_iUnion (fun q ↦ segment ℝ (left q) (right q)) q)
  have hsBase : s ∈ (K.replacementGraphBaseComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes :=
    ((K.replacementGraphArrangement).arrangementMesh.toPlaneComplex
      |>.mem_restrictToSet_simplexes_iff
        (K.replacementGraphCarrier
          (hcont := hcont) (hinj := hinj) (D := D) (C := C))).mpr
      ⟨hs, hsCarrier⟩
  refine ⟨s, hsBase, hxs, ?_, ?_⟩
  · exact hsSegment
  · apply (K.replacementGraphArrangement).arrangementMesh.toPlaneComplex
      |>.card_le_two_of_vertices_mem_segment hs
    · intro v hv
      apply hsSegment
      exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩

theorem replacementGraphBaseComplex_support :
    (K.replacementGraphBaseComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      K.replacementGraphCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  apply Set.Subset.antisymm
  · exact (K.replacementGraphArrangement).arrangementMesh.toPlaneComplex
      |>.restrictToSet_support_subset K.replacementGraphCarrier
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, hxs, -, -⟩ := K.exists_replacementGraphBase_face q hxq
    rw [PlaneComplex.support]
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hxs⟩

theorem replacementGraphComplex_support :
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      K.replacementGraphCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  apply Set.Subset.antisymm
  · exact (K.replacementGraphBaseComplex).oneSkeleton_support_subset.trans_eq
      K.replacementGraphBaseComplex_support
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, hxs, -, hscard⟩ := K.exists_replacementGraphBase_face q hxq
    rw [PlaneComplex.support]
    exact Set.mem_iUnion₂.mpr
      ⟨s, (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)
          |>.mem_oneSkeleton_simplexes).mpr ⟨hs, hscard⟩, hxs⟩

theorem replacementGraphCarrier_eq_image :
    K.replacementGraphCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) =
      K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    rw [K.replacementSegment_eq_cellCarrier q] at hxq
    have hxEdge : x ∈
        (K.replacementArc hcont hinj D C q.1).completeCarrier := by
      rw [← (K.replacementArc hcont hinj D C q.1).completeTarget_support]
      exact (K.replacementArc hcont hinj D C q.1).completeTarget
        |>.cellCarrier_subset_support q.2.2.1 hxq
    rw [← K.graphReplacementMap_image_faceCarrier] at hxEdge
    obtain ⟨y, hye, rfl⟩ := hxEdge
    exact ⟨y, ⟨q.1, hye⟩, rfl⟩
  · rintro x ⟨y, ⟨e, hye⟩, rfl⟩
    have hyEdge : K.graphReplacementMap hcont hinj D C y ∈
        (K.replacementArc hcont hinj D C e).completeCarrier := by
      rw [← K.graphReplacementMap_image_faceCarrier]
      exact ⟨y, hye, rfl⟩
    obtain ⟨s, hs, hys, hsSub, hscard⟩ :=
      (K.replacementArc hcont hinj D C e).exists_completeTarget_face hyEdge
    have hsTarget : s ∈
        (K.replacementArc hcont hinj D C e).completeTarget.simplexes := by
      apply ((K.replacementArc hcont hinj D C e).completeChain.arrangementMesh.toPlaneComplex
        |>.mem_restrictedTo_simplexes_iff
          (K.replacementArc hcont hinj D C e).completeCarrier).mpr
      exact ⟨hs, hsSub⟩
    let q : K.ReplacementSegmentFace
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) :=
      ⟨e, ⟨s, hsTarget, hscard⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    rw [K.replacementSegment_eq_cellCarrier q]
    exact hys

theorem replacementGraphComplex_support_eq_image :
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      K.graphReplacementMap hcont hinj D C '' K.oneSkeleton :=
  K.replacementGraphComplex_support.trans K.replacementGraphCarrier_eq_image

/-- Every point of one complete replacement edge has a face of the conforming global graph
complex which remains inside that edge. -/
theorem exists_replacementGraphComplex_face_of_mem_completeCarrier
    (e : K.Edge) {x : Plane}
    (hx : x ∈ (K.replacementArc hcont hinj D C e).completeCarrier) :
    ∃ s ∈ (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes,
      x ∈ (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ∧
      (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ⊆
        (K.replacementArc hcont hinj D C e).completeCarrier := by
  obtain ⟨u, hu, hxu, huSub, huCard⟩ :=
    (K.replacementArc hcont hinj D C e).exists_completeTarget_face hx
  have huTarget : u ∈ (K.replacementArc hcont hinj D C e).completeTarget.simplexes := by
    apply ((K.replacementArc hcont hinj D C e).completeChain.arrangementMesh.toPlaneComplex
      |>.mem_restrictedTo_simplexes_iff
        (K.replacementArc hcont hinj D C e).completeCarrier).mpr
    exact ⟨hu, huSub⟩
  let q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) :=
    ⟨e, ⟨u, huTarget, huCard⟩⟩
  have hxSegment : x ∈ segment ℝ
      (K.replacementSegmentLeft q) (K.replacementSegmentRight q) := by
    rw [K.replacementSegment_eq_cellCarrier q]
    exact hxu
  obtain ⟨s, hs, hxs, hsSub, hsCard⟩ :=
    K.exists_replacementGraphBase_face q hxSegment
  refine ⟨s, ?_, hxs, ?_⟩
  · exact (K.replacementGraphBaseComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)
        |>.mem_oneSkeleton_simplexes).mpr ⟨hs, hsCard⟩
  · exact hsSub.trans (by
      rw [K.replacementSegment_eq_cellCarrier q]
      exact (K.replacementArc hcont hinj D C e).completeTarget
        |>.cellCarrier_subset_support huTarget |>.trans_eq
          (K.replacementArc hcont hinj D C e).completeTarget_support)

/-- Each intrinsic face polygon is locally covered by faces of the one global conforming graph
complex. -/
theorem facePolygonalCircle_locallyCoveredBy_replacementGraphComplex (t : K.Face) :
    ∀ x ∈ (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier,
      ∃ s ∈ (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes,
        x ∈ (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ∧
        (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ⊆
          (K.facePolygonalCircle
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
  intro x hx
  rw [K.facePolygonalCircle_carrier] at hx ⊢
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs, hxs, hsSub⟩ :=
    K.exists_replacementGraphComplex_face_of_mem_completeCarrier (K.faceEdge t i) hxi
  exact ⟨s, hs, hxs, hsSub.trans (Set.subset_iUnion
    (fun j : ZMod 3 ↦
      (K.faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j).completeCarrier) i)⟩

theorem replacementGraphComplex_support_eq_range :
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      Set.range (fun x : K.oneSkeleton ↦
        K.graphReplacementMap hcont hinj D C x.1) := by
  rw [K.replacementGraphComplex_support_eq_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩

/-- The intrinsic one-skeleton is homeomorphic to the support of its conforming polygonal plane
graph model. -/
noncomputable def replacementGraphHomeomorph :
    K.oneSkeleton ≃ₜ
      (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support :=
  (K.graphReplacementMap_isEmbedding_oneSkeleton hcont hinj D C).toHomeomorph.trans
    (Homeomorph.setCongr K.replacementGraphComplex_support_eq_range.symm)

@[simp] theorem replacementGraphHomeomorph_coe (x : K.oneSkeleton) :
    ((K.replacementGraphHomeomorph
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x :
        (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support) : Plane) =
      K.graphReplacementMap hcont hinj D C x.1 := rfl

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
