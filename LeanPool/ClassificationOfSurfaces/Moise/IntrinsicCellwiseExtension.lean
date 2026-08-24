/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceFilling
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicMidpointSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalFamilyPolyhedron

/-!
# Cellwise assembly of intrinsic PL face fillings

The fillings supplied by `IntrinsicFaceFilling` use one standard triangle for every maximal
intrinsic face.  This file transports them back to the canonical barycentric realization and
glues the finite family.  Coherence is proved from the common global one-skeleton replacement;
it is not stored as an extra compatibility assumption.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

namespace FacePLFilling

/-- A standard-triangle filling transported to its intrinsic closed face. -/
noncomputable def intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    K.ClosedFace t → Plane :=
  fun x ↦ F.map (K.facePlaneHomeomorph t x).1

theorem continuous_intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Continuous F.intrinsicMap := by
  have hF : Continuous (fun p : standardFaceRegion ↦ F.map p.1) :=
    continuousOn_iff_continuous_domRestrict.mp F.continuousOn
  exact hF.comp (K.facePlaneHomeomorph t).continuous

theorem injective_intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Function.Injective F.intrinsicMap := by
  intro x y hxy
  apply (K.facePlaneHomeomorph t).injective
  apply Subtype.ext
  apply F.injectiveOn (K.facePlaneHomeomorph t x).2 (K.facePlaneHomeomorph t y).2
  exact hxy

theorem range_intrinsicMap {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Set.range F.intrinsicMap =
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion := by
  rw [← F.image_eq]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(K.facePlaneHomeomorph t x).1, (K.facePlaneHomeomorph t x).2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    let q : standardFaceRegion := ⟨p, hp⟩
    exact ⟨(K.facePlaneHomeomorph t).symm q, by
      change F.map (K.facePlaneHomeomorph t ((K.facePlaneHomeomorph t).symm q)).1 = F.map p
      rw [(K.facePlaneHomeomorph t).apply_symm_apply]⟩

/-- The relative interior of a filled intrinsic face maps to the bounded complementary region. -/
theorem mapsTo_interiorRegion {t : K.Face} (F : K.FacePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    Set.MapsTo F.map (interior standardFaceRegion)
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).interiorRegion := by
  intro p hp
  have hpRegion : p ∈ standardFaceRegion := interior_subset hp
  have hclosed : F.map p ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion := by
    rw [← F.image_eq]
    exact ⟨p, hpRegion, rfl⟩
  rw [(K.facePolygonalCircle t).closedRegion_eq_union] at hclosed
  rcases hclosed with hbounded | hcarrier
  · exact hbounded
  · rw [← K.faceBoundaryMap_image_polygon t] at hcarrier
    obtain ⟨q, hq, hqmap⟩ := hcarrier
    have hmapEq : F.map p = F.map q := by
      rw [F.eqOn_boundary hq]
      exact hqmap.symm
    have hpq : p = q := F.injectiveOn hpRegion
      (standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hq) hmapEq
    subst q
    exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hp hq)

end FacePLFilling

private theorem exists_edge_between_small_carriers
    (t : K.Face) {s : Finset K.Vertex} (hsCard : s.card ≤ 2)
    {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hxs : x ∈ K.faceCarrier s) :
    ∃ e : K.Edge, t.1 ∩ s ⊆ e.1 ∧ e.1 ⊆ t.1 ∧ x ∈ K.faceCarrier e.1 := by
  classical
  have hxInter : x ∈ K.faceCarrier (t.1 ∩ s) := by
    rw [← K.faceCarrier_inter]
    exact ⟨hxt, hxs⟩
  have hInterNonempty : (t.1 ∩ s).Nonempty := by
    by_contra h
    have hempty : t.1 ∩ s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty, K.faceCarrier_empty] at hxInter
    exact hxInter
  have hInterCard : (t.1 ∩ s).card ≤ 2 :=
    (Finset.card_le_card Finset.inter_subset_right).trans hsCard
  have hTwoLe : 2 ≤ t.1.card := by
    rw [K.faces_card t.1 t.2]
    norm_num
  obtain ⟨e, hInterE, hEt, hEcard⟩ :=
    Finset.exists_subsuperset_card_eq Finset.inter_subset_left hInterCard hTwoLe
  have heEdges : e ∈ K.edges := by
    apply Finset.mem_biUnion.mpr
    exact ⟨t.1, t.2, Finset.mem_powersetCard.mpr ⟨hEt, hEcard⟩⟩
  let E : K.Edge := ⟨e, heEdges⟩
  refine ⟨E, hInterE, hEt, ?_⟩
  intro v hvE
  apply hxInter v
  intro hvInter
  exact hvE (hInterE hvInter)

/-- A point of a face which is also carried by a set of at most two vertices lies on one of
that face's three intrinsic edges. -/
theorem exists_faceEdge_of_mem_small_carrier
    (t : K.Face) {s : Finset K.Vertex} (hsCard : s.card ≤ 2)
    {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hxs : x ∈ K.faceCarrier s) :
    ∃ i : ZMod 3, x ∈ K.faceCarrier (K.faceEdge t i).1 := by
  obtain ⟨e, -, het, hxe⟩ := K.exists_edge_between_small_carriers t hsCard hxt hxs
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset t e het
  exact ⟨i, by simpa only [hi] using hxe⟩

private theorem faceChart_mem_frontier_of_mem_small_carrier
    (t : K.Face) {s : Finset K.Vertex} (hsCard : s.card ≤ 2)
    {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hxs : x ∈ K.faceCarrier s) :
    (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion := by
  obtain ⟨i, hxi⟩ := K.exists_faceEdge_of_mem_small_carrier t hsCard hxt hxs
  have hpSide : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
      standardTriangleCircle.edgeSegment i := by
    rw [← K.facePlaneHomeomorph_image_edge t i]
    exact ⟨⟨x, hxt⟩, hxi, rfl⟩
  have hpCarrier : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
      standardTriangleCircle.carrier :=
    Set.mem_iUnion.mpr ⟨i, hpSide⟩
  rw [standardTriangleCircle_carrier] at hpCarrier
  simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier

/-- The standard coordinate of a point shared by two distinct faces lies on the standard
triangle frontier. -/
theorem faceChart_mem_frontier_of_mem_distinct_faces
    {t u : K.Face} (htu : t ≠ u) {x : K.realization}
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1) :
    (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion := by
  classical
  have hInterCard : (t.1 ∩ u.1).card ≤ 2 := by
    by_contra h
    have hge : 3 ≤ (t.1 ∩ u.1).card := by omega
    have hle : (t.1 ∩ u.1).card ≤ 3 := by
      simpa [K.faces_card t.1 t.2] using
        Finset.card_le_card (Finset.inter_subset_left : t.1 ∩ u.1 ⊆ t.1)
    have hcard : (t.1 ∩ u.1).card = 3 := by omega
    have hinterT : t.1 ∩ u.1 = t.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [K.faces_card t.1 t.2, hcard])
    have htuSub : t.1 ⊆ u.1 := by
      rw [← hinterT]
      exact Finset.inter_subset_right
    have htuEq : t.1 = u.1 :=
      Finset.eq_of_subset_of_card_le htuSub (by
        rw [K.faces_card t.1 t.2, K.faces_card u.1 u.2])
    exact htu (Subtype.ext htuEq)
  have hxInter : x ∈ K.faceCarrier (t.1 ∩ u.1) := by
    rw [← K.faceCarrier_inter]
    exact ⟨hxt, hxu⟩
  exact K.faceChart_mem_frontier_of_mem_small_carrier t hInterCard hxt hxInter

/-- A point shared by distinct maximal intrinsic faces belongs to the global one-skeleton. -/
theorem mem_oneSkeleton_of_mem_distinct_faces
    {t u : K.Face} (htu : t ≠ u) {x : K.realization}
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1) :
    x ∈ K.oneSkeleton := by
  have hp := K.faceChart_mem_frontier_of_mem_distinct_faces htu hxt hxu
  have hpCarrier : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
      standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  have hxi := K.facePlaneHomeomorph_symm_mem_edge t i hi
  have heq : ((K.facePlaneHomeomorph t).symm
      ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
        standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩).1 = x := by
    rw [show (⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
        standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩ :
      standardFaceRegion) = K.facePlaneHomeomorph t ⟨x, hxt⟩ by rfl,
      (K.facePlaneHomeomorph t).symm_apply_apply]
  exact ⟨K.faceEdge t i, by simpa only [heq] using hxi⟩

/-- Lifting the standard coordinate of an intrinsic boundary point recovers that point. -/
theorem faceBoundaryLift_facePlaneHomeomorph
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hp : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion) :
    (K.faceBoundaryLift t
      ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩).1 = x := by
  change ((K.facePlaneHomeomorph t).symm
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, _⟩).1 = x
  have hsubtype :
      (⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
          standardFaceBoundary_mem_region
            ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩⟩ :
        standardFaceRegion) = K.facePlaneHomeomorph t ⟨x, hxt⟩ := by
    rfl
  rw [hsubtype, (K.facePlaneHomeomorph t).symm_apply_apply]

theorem faceBoundaryLift_mem_faceCarrier (t : K.Face) (p : StandardFaceBoundary) :
    (K.faceBoundaryLift t p).1 ∈ K.faceCarrier t.1 := by
  change ((K.facePlaneHomeomorph t).symm
    ⟨p.1, standardFaceBoundary_mem_region p⟩).1 ∈ K.faceCarrier t.1
  exact ((K.facePlaneHomeomorph t).symm
    ⟨p.1, standardFaceBoundary_mem_region p⟩).2

/-- The transported fillings of two faces agree at every point of their overlap. -/
theorem facePLFilling_intrinsicMap_eq
    (t u : K.Face) {x : K.realization}
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1) :
    (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).intrinsicMap
        ⟨x, hxt⟩ =
      (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).intrinsicMap
        ⟨x, hxu⟩ := by
  by_cases htu : t = u
  · subst u
    rfl
  let p : StandardFaceBoundary :=
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
      K.faceChart_mem_frontier_of_mem_distinct_faces htu hxt hxu⟩
  let q : StandardFaceBoundary :=
    ⟨(K.facePlaneHomeomorph u ⟨x, hxu⟩).1,
      K.faceChart_mem_frontier_of_mem_distinct_faces (Ne.symm htu) hxu hxt⟩
  apply K.facePLFilling_eq_of_boundaryLift_eq (t := t) (u := u) (p := p) (q := q)
  rw [K.faceBoundaryLift_facePlaneHomeomorph t hxt p.2,
    K.faceBoundaryLift_facePlaneHomeomorph u hxu q.2]

/-- A chosen maximal face containing a point of the canonical realization. -/
noncomputable def containingFace (x : K.realization) : K.Face :=
  ⟨Classical.choose x.2.2, (Classical.choose_spec x.2.2).1⟩

theorem mem_faceCarrier_containingFace (x : K.realization) :
    x ∈ K.faceCarrier (K.containingFace x).1 :=
  (Classical.choose_spec x.2.2).2

/-- The finite family of intrinsic face fillings, glued into one map. -/
noncomputable def cellwisePLFillingMap (x : K.realization) : Plane :=
  (K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) (K.containingFace x)).intrinsicMap
    ⟨x, K.mem_faceCarrier_containingFace x⟩

/-- The glued map restricts to the chosen certified filling on every maximal face. -/
theorem cellwisePLFillingMap_eqOn_face (t : K.Face) (x : K.realization)
    (hxt : x ∈ K.faceCarrier t.1) :
    K.cellwisePLFillingMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) x =
      (K.facePLFilling
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).intrinsicMap ⟨x, hxt⟩ := by
  exact K.facePLFilling_intrinsicMap_eq (K.containingFace x) t
    (K.mem_faceCarrier_containingFace x) hxt

/-- The finite cellwise filling is continuous on the whole intrinsic realization. -/
theorem continuous_cellwisePLFillingMap :
    Continuous (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) := by
  let carriers : K.Face → Set K.realization := fun t ↦ K.faceCarrier t.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hclosed : ∀ t : K.Face, IsClosed (carriers t) := fun t ↦ K.faceCarrier_closed t.1
  have hlocal : ∀ t : K.Face,
      ContinuousOn (K.cellwisePLFillingMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)) (carriers t) := by
    intro t
    rw [continuousOn_iff_continuous_domRestrict]
    have hF := (K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).continuous_intrinsicMap
    convert hF using 1
    funext x
    exact K.cellwisePLFillingMap_eqOn_face t x.1 x.2
  exact hfinite.continuous K.realization_eq_iUnion_faceCarrier.symm hclosed hlocal

/-- On the global intrinsic one-skeleton, the cellwise filling is exactly the previously
constructed simultaneous graph replacement. -/
theorem cellwisePLFillingMap_eq_graphReplacement
    {x : K.realization} (hx : x ∈ K.oneSkeleton) :
    K.cellwisePLFillingMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) x =
      K.graphReplacementMap hcont hinj D C x := by
  obtain ⟨e, hxe⟩ := hx
  let t := K.containingFace x
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hp : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion :=
    K.faceChart_mem_frontier_of_mem_small_carrier t
      (by rw [K.card_of_mem_edges e.2]) hxt hxe
  rw [K.cellwisePLFillingMap_eqOn_face t x hxt]
  change (K.facePLFilling t).map (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 = _
  rw [(K.facePLFilling t).eqOn_boundary hp, K.faceBoundaryMap_apply t
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩,
    K.faceBoundaryLift_facePlaneHomeomorph t hxt hp]

/-- The original embedding written in the standard coordinates of one intrinsic face.  Values
outside the standard closed triangle are irrelevant. -/
noncomputable def faceOriginalMap (t : K.Face) (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ standardFaceRegion then
    h ((K.facePlaneHomeomorph t).symm ⟨p, hp⟩).1
  else 0

@[simp] theorem faceOriginalMap_apply (t : K.Face) (p : standardFaceRegion) :
    K.faceOriginalMap (h := h) t p.1 =
      h ((K.facePlaneHomeomorph t).symm p).1 := by
  simp [faceOriginalMap, p.2]

theorem continuousOn_faceOriginalMap (hcont : Continuous h) (t : K.Face) :
    ContinuousOn (K.faceOriginalMap (h := h) t) standardFaceRegion := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert hcont.comp
    (continuous_subtype_val.comp (K.facePlaneHomeomorph t).symm.continuous) using 1
  funext p
  exact K.faceOriginalMap_apply t p

theorem faceOriginalMap_mem_face_image (t : K.Face) (p : standardFaceRegion) :
    K.faceOriginalMap (h := h) t p.1 ∈ h '' K.faceCarrier t.1 := by
  refine ⟨((K.facePlaneHomeomorph t).symm p).1,
    ((K.facePlaneHomeomorph t).symm p).2, ?_⟩
  exact (K.faceOriginalMap_apply t p).symm

/-- A one-skeleton point lying in a face has a standard coordinate on that face's frontier. -/
theorem faceChart_mem_frontier_of_mem_oneSkeleton
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hx : x ∈ K.oneSkeleton) :
    (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion := by
  obtain ⟨e, hxe⟩ := hx
  exact K.faceChart_mem_frontier_of_mem_small_carrier t
    (by rw [K.card_of_mem_edges e.2]) hxt hxe

/-- Conversely, the inverse face chart takes the standard frontier into the global
one-skeleton. -/
theorem mem_oneSkeleton_of_faceChart_mem_frontier
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hp : (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈ frontier standardFaceRegion) :
    x ∈ K.oneSkeleton := by
  let p : StandardFaceBoundary := ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩
  have hlift := (K.faceBoundaryLift t p).2
  rw [K.faceBoundaryLift_facePlaneHomeomorph t hxt hp] at hlift
  exact hlift

/-- The graph-side condition needed for injective cellwise assembly: the simultaneous global
one-skeleton replacement avoids the bounded interior selected for every face. -/
def FaceFillingsGraphAvoidInteriors : Prop :=
  ∀ t : K.Face,
    Disjoint
      (K.graphReplacementMap hcont hinj D C '' K.oneSkeleton)
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).interiorRegion

/-- The finite vertex-side condition used to establish graph-side compatibility. -/
def FaceFillingsVerticesAvoidClosedRegions : Prop :=
  ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
    h (K.vertexPoint v) ∉
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion

/-- A finite embedded intrinsic two-complex has one positive separation radius for every
maximal face and every used vertex not belonging to that face. -/
theorem exists_uniform_vertex_face_separation
    (hcont : Continuous h) (hinj : Function.Injective h) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
        Disjoint (Metric.closedBall (h (K.vertexPoint v)) r)
          (Metric.cthickening r (h '' K.faceCarrier t.1)) := by
  classical
  let I := Option (K.Face × K.UsedVertex)
  let P : I → ℝ → Prop
    | none, _ => True
    | some (t, v), r =>
        v.1 ∈ t.1 ∨
          Disjoint (Metric.closedBall (h (K.vertexPoint v)) r)
            (Metric.cthickening r (h '' K.faceCarrier t.1))
  have hlocal : ∀ i : I, ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → P i r := by
    intro i
    rcases i with _ | ⟨t, v⟩
    · exact ⟨1, by norm_num, fun _ _ _ ↦ trivial⟩
    · by_cases hvt : v.1 ∈ t.1
      · exact ⟨1, by norm_num, fun _ _ _ ↦ Or.inl hvt⟩
      · have hdisjoint : Disjoint ({h (K.vertexPoint v)} : Set Plane)
            (h '' K.faceCarrier t.1) := by
          rw [Set.disjoint_singleton_left]
          rintro ⟨x, hxt, hvx⟩
          have hxv : x = K.vertexPoint v := hinj hvx
          rw [hxv] at hxt
          exact hvt ((K.vertexPoint_mem_faceCarrier_iff v t.1).mp hxt)
        have hcompact : IsCompact (h '' K.faceCarrier t.1) :=
          (K.faceCarrier_closed t.1).isCompact.image hcont
        obtain ⟨ε, hε, hthick⟩ := hdisjoint.exists_thickenings
          isCompact_singleton hcompact.isClosed
        refine ⟨ε, hε, fun r hr hrε ↦ Or.inr ?_⟩
        exact hthick.mono
          ((Metric.closedBall_subset_cthickening (Set.mem_singleton _) r).trans
            (Metric.cthickening_subset_thickening' hε hrε _))
          (Metric.cthickening_subset_thickening' hε hrε _)
  obtain ⟨ε, hε, huniform⟩ := exists_pos_uniform_fintype' P hlocal
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  refine ⟨r, hr, ?_⟩
  intro t v hvt
  have hP := huniform (some (t, v)) r hr (half_lt_self hε)
  rcases hP with hmem | hdis
  · exact (hvt hmem).elim
  · exact hdis

/-- Quantitative closeness and vertex-to-face separation put every nonincident vertex on the
unbounded side of every replacement polygon. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_close
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
      Disjoint (Metric.closedBall (h (K.vertexPoint v)) r)
        (Metric.cthickening r (h '' K.faceCarrier t.1)))
    (hclose : ∀ x ∈ K.oneSkeleton,
      dist (K.graphReplacementMap hcont hinj D C x) (h x) < r) :
    K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  intro t v hvt
  let b := K.faceBoundaryMap
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let hface := K.faceOriginalMap (h := h) t
  have hbcont : ContinuousOn b (frontier standardFaceRegion) :=
    K.continuousOn_faceBoundaryMap t
  have hhface : ContinuousOn hface standardFaceRegion :=
    K.continuousOn_faceOriginalMap hcont t
  have hbclose : ∀ p ∈ frontier standardFaceRegion, dist (b p) (hface p) < r := by
    intro p hp
    let q : StandardFaceBoundary := ⟨p, hp⟩
    have hq := hclose (K.faceBoundaryLift t q).1 (K.faceBoundaryLift t q).2
    rw [← K.faceBoundaryMap_apply t q] at hq
    have horiginal : hface p = h (K.faceBoundaryLift t q).1 := by
      change K.faceOriginalMap (h := h) t p = _
      rw [K.faceOriginalMap_apply t
        ⟨p, standardFaceBoundary_mem_region q⟩]
      rfl
    change dist (K.faceBoundaryMap t p) (K.faceOriginalMap (h := h) t p) < r
    have horiginal' : K.faceOriginalMap (h := h) t p =
        h (K.faceBoundaryLift t q).1 := horiginal
    rw [horiginal']
    exact hq
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      standardTrianglePlaneComplex.isCompact_support.isClosed hr hbcont hhface hbclose
  have hvAvoid : h (K.vertexPoint v) ∉ F '' standardFaceRegion := by
    rintro ⟨p, hp, hFp⟩
    have hvBall : h (K.vertexPoint v) ∈
        Metric.closedBall (h (K.vertexPoint v)) r :=
      Metric.mem_closedBall_self hr.le
    have hFthick : F p ∈ Metric.cthickening r (h '' K.faceCarrier t.1) := by
      apply Metric.mem_cthickening_of_dist_le (F p) (hface p) r
        (h '' K.faceCarrier t.1)
      · exact K.faceOriginalMap_mem_face_image t ⟨p, hp⟩
      · exact hFclose p hp
    exact Set.disjoint_left.mp (hsep t v hvt) hvBall (hFp ▸ hFthick)
  have hvExterior : h (K.vertexPoint v) ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).exteriorRegion := by
    apply (K.facePolygonalCircle t).mem_exteriorRegion_of_continuous_extension
      standardTrianglePlaneComplex_isTriangle hbcont
      (K.faceBoundaryMap_injectiveOn t) (K.faceBoundaryMap_image_polygon t)
      hFcont hFeq hvAvoid
  intro hvClosed
  exact Set.disjoint_left.mp
    (K.facePolygonalCircle t).disjoint_closedRegion_exteriorRegion hvClosed hvExterior

/-- Every filled face boundary is part of the single global replacement graph. -/
theorem facePolygonalCircle_carrier_subset_graphReplacement (t : K.Face) :
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier ⊆
      K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
  intro y hy
  rw [← K.faceBoundaryMap_image_polygon t] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  let q : StandardFaceBoundary := ⟨p, hp⟩
  exact ⟨(K.faceBoundaryLift t q).1, (K.faceBoundaryLift t q).2,
    (K.faceBoundaryMap_apply t q).symm⟩

/-- A replacement-graph point can lie on the polygon of a face only when its intrinsic source
lies in that face.  This is the exact-carrier consequence of boundary coherence and injectivity
of the simultaneous graph replacement. -/
theorem mem_faceCarrier_of_graphReplacement_mem_facePolygonalCircle
    (t : K.Face) {x : K.realization} (hx : x ∈ K.oneSkeleton)
    (himage : K.graphReplacementMap hcont hinj D C x ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier) :
    x ∈ K.faceCarrier t.1 := by
  rw [← K.faceBoundaryMap_image_polygon t] at himage
  obtain ⟨p, hp, hpEq⟩ := himage
  let q : StandardFaceBoundary := ⟨p, hp⟩
  have hgraphEq : K.graphReplacementMap hcont hinj D C x =
      K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q).1 := by
    rw [← K.faceBoundaryMap_apply t q]
    exact hpEq.symm
  have hxEq := K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C
    hx (K.faceBoundaryLift t q).2 hgraphEq
  rw [hxEq]
  exact K.faceBoundaryLift_mem_faceCarrier t q

/-- A point of a face which lies on the one-skeleton maps to that face's polygonal boundary. -/
theorem graphReplacement_mem_facePolygonalCircle
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hx : x ∈ K.oneSkeleton) :
    K.graphReplacementMap hcont hinj D C x ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
  have hp := K.faceChart_mem_frontier_of_mem_oneSkeleton t hxt hx
  rw [← K.faceBoundaryMap_image_polygon t]
  refine ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp, ?_⟩
  rw [K.faceBoundaryMap_apply t
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩,
    K.faceBoundaryLift_facePlaneHomeomorph t hxt hp]

/-- Vertex avoidance places every vertex not incident to a face in the unbounded component of
that face's replacement polygon. -/
theorem graphReplacement_vertex_mem_exterior
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    (t : K.Face) (v : K.UsedVertex) (hvt : v.1 ∉ t.1) :
    K.graphReplacementMap hcont hinj D C (K.vertexPoint v) ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).exteriorRegion := by
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  rw [K.graphReplacementMap_vertex hcont hinj D C]
  have hnotClosed := hvertices t v hvt
  have hnotInterior : h (K.vertexPoint v) ∉ J.interiorRegion := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inl hv
  have hnotCarrier : h (K.vertexPoint v) ∉ J.carrier := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inr hv
  have hoff : h (K.vertexPoint v) ∈ J.carrierᶜ := hnotCarrier
  rw [← J.interior_union_exterior] at hoff
  exact hoff.resolve_left hnotInterior

/-- Moise's finite vertex condition propagates along every intrinsic edge.  Thus the whole
simultaneous replacement graph avoids the bounded polygonal region selected for each face. -/
theorem faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    K.FaceFillingsGraphAvoidInteriors
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  intro t
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  have hinteriorCarrier : Disjoint J.interiorRegion J.carrier := by
    rw [← J.interior_closedRegion, ← J.frontier_closedRegion]
    exact disjoint_interior_frontier
  rw [Set.disjoint_left]
  rintro _ ⟨x, hxOne, rfl⟩ hxInterior
  obtain ⟨e, hxe⟩ := hxOne
  by_cases het : e.1 ⊆ t.1
  · have hxt : x ∈ K.faceCarrier t.1 := by
      intro v hvt
      exact hxe v (fun hve ↦ hvt (het hve))
    exact Set.disjoint_left.mp hinteriorCarrier hxInterior
      (K.graphReplacement_mem_facePolygonalCircle t hxt ⟨e, hxe⟩)
  let I := Set.Icc (0 : ℝ) 1
  let z0 : I := ⟨0, by simp [I]⟩
  let z1 : I := ⟨1, by simp [I]⟩
  let gpath : I → Plane := fun s ↦
    K.graphReplacementMap hcont hinj D C (K.edgePath e s)
  have hpathCarrier (s : I) : K.edgePath e s ∈ K.faceCarrier e.1 := by
    rw [← K.range_edgePath e]
    exact ⟨s, rfl⟩
  have hpathOne (s : I) : K.edgePath e s ∈ K.oneSkeleton :=
    ⟨e, hpathCarrier s⟩
  have hgpath : Continuous gpath := by
    have hgraph := K.continuousOn_graphReplacementMap_faceCarrier hcont hinj D C e
    simpa only [gpath, Function.comp_def] using
      hgraph.comp_continuous (K.continuous_edgePath e) hpathCarrier
  have hoffCarrier {A : Set I}
      (houtside : ∀ s ∈ A, K.edgePath e s ∉ K.faceCarrier t.1) :
      Set.MapsTo gpath A J.carrierᶜ := by
    intro s hs hcarrier
    exact houtside s hs
      (K.mem_faceCarrier_of_graphReplacement_mem_facePolygonalCircle t
        (hpathOne s) hcarrier)
  let r : I := K.edgeParameter e x hxe
  have hxPath : K.edgePath e r = x := K.edgePath_edgeParameter e x hxe
  have hsharedImpossible (hxt : x ∈ K.faceCarrier t.1) : False := by
    exact Set.disjoint_left.mp hinteriorCarrier hxInterior
      (K.graphReplacement_mem_facePolygonalCircle t hxt ⟨e, hxe⟩)
  by_cases hfirst : K.edgeFirst e ∈ t.1
  · have hsecond : K.edgeSecond e ∉ t.1 := by
      intro hsecond
      apply het
      rw [K.edge_eq_pair e]
      exact Finset.insert_subset_iff.mpr
        ⟨hfirst, Finset.singleton_subset_iff.mpr hsecond⟩
    by_cases hr0 : r.1 = 0
    · apply hsharedImpossible
      have hxFirst : x = K.edgeFirstPoint e := by
        calc
          x = K.edgePath e r := hxPath.symm
          _ = K.edgePath e z0 := by congr 1; exact Subtype.ext hr0
          _ = K.edgeFirstPoint e := K.edgePath_zero e
      rw [hxFirst, ← K.vertexPoint_edgeFirstUsed e]
      exact (K.vertexPoint_mem_faceCarrier_iff (K.edgeFirstUsed e) t.1).mpr hfirst
    · let A : Set I := Set.Ioc z0 z1
      have hApreconnected : IsPreconnected A := isPreconnected_Ioc
      have hAoutside : ∀ s ∈ A, K.edgePath e s ∉ K.faceCarrier t.1 := by
        intro s hs hsFace
        have hzero := hsFace (K.edgeSecond e) hsecond
        rw [K.edgePath_apply_second] at hzero
        have hspos : 0 < s.1 := by
          exact_mod_cast hs.1
        exact (ne_of_gt hspos) hzero
      have hz1Exterior : gpath z1 ∈ J.exteriorRegion := by
        have hvertex := K.graphReplacement_vertex_mem_exterior hvertices t
          (K.edgeSecondUsed e) hsecond
        simpa only [gpath, z1, K.edgePath_one, K.vertexPoint_edgeSecondUsed] using hvertex
      have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected hApreconnected hgpath.continuousOn
          (hoffCarrier hAoutside) ⟨z1, by simp [A, z0, z1], hz1Exterior⟩
      have hrA : r ∈ A := by
        constructor
        · change (0 : ℝ) < r.1
          exact lt_of_le_of_ne r.2.1 (Ne.symm hr0)
        · change r.1 ≤ (1 : ℝ)
          exact r.2.2
      have hrExterior := hAExterior hrA
      change K.graphReplacementMap hcont hinj D C (K.edgePath e r) ∈
        J.exteriorRegion at hrExterior
      rw [hxPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hxInterior hrExterior
  · by_cases hsecond : K.edgeSecond e ∈ t.1
    · by_cases hr1 : r.1 = 1
      · apply hsharedImpossible
        have hxSecond : x = K.edgeSecondPoint e := by
          calc
            x = K.edgePath e r := hxPath.symm
            _ = K.edgePath e z1 := by congr 1; exact Subtype.ext hr1
            _ = K.edgeSecondPoint e := K.edgePath_one e
        rw [hxSecond, ← K.vertexPoint_edgeSecondUsed e]
        exact (K.vertexPoint_mem_faceCarrier_iff (K.edgeSecondUsed e) t.1).mpr hsecond
      · let A : Set I := Set.Ico z0 z1
        have hApreconnected : IsPreconnected A := isPreconnected_Ico
        have hAoutside : ∀ s ∈ A, K.edgePath e s ∉ K.faceCarrier t.1 := by
          intro s hs hsFace
          have hzero := hsFace (K.edgeFirst e) hfirst
          rw [K.edgePath_apply_first] at hzero
          have hslt : s.1 < 1 := by
            exact_mod_cast hs.2
          linarith
        have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
          have hvertex := K.graphReplacement_vertex_mem_exterior hvertices t
            (K.edgeFirstUsed e) hfirst
          simpa only [gpath, z0, K.edgePath_zero, K.vertexPoint_edgeFirstUsed] using hvertex
        have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
          J.mapsTo_exteriorRegion_of_isPreconnected hApreconnected hgpath.continuousOn
            (hoffCarrier hAoutside) ⟨z0, by simp [A, z0, z1], hz0Exterior⟩
        have hrA : r ∈ A := by
          constructor
          · change (0 : ℝ) ≤ r.1
            exact r.2.1
          · change r.1 < (1 : ℝ)
            exact lt_of_le_of_ne r.2.2 hr1
        have hrExterior := hAExterior hrA
        change K.graphReplacementMap hcont hinj D C (K.edgePath e r) ∈
          J.exteriorRegion at hrExterior
        rw [hxPath] at hrExterior
        exact Set.disjoint_left.mp J.disjoint_interior_exterior hxInterior hrExterior
    · have hAllOutside : ∀ s : I, K.edgePath e s ∉ K.faceCarrier t.1 := by
        intro s hsFace
        have hzeroFirst := hsFace (K.edgeFirst e) hfirst
        have hzeroSecond := hsFace (K.edgeSecond e) hsecond
        rw [K.edgePath_apply_first] at hzeroFirst
        rw [K.edgePath_apply_second] at hzeroSecond
        linarith
      have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
        have hvertex := K.graphReplacement_vertex_mem_exterior hvertices t
          (K.edgeFirstUsed e) hfirst
        simpa only [gpath, z0, K.edgePath_zero, K.vertexPoint_edgeFirstUsed] using hvertex
      have hAllExterior : Set.MapsTo gpath Set.univ J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_univ hgpath.continuousOn
          (hoffCarrier fun s _ ↦ hAllOutside s) ⟨z0, Set.mem_univ _, hz0Exterior⟩
      have hrExterior := hAllExterior (Set.mem_univ r)
      change K.graphReplacementMap hcont hinj D C (K.edgePath e r) ∈
        J.exteriorRegion at hrExterior
      rw [hxPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hxInterior hrExterior

/-- Quantitative control of the cellwise filling.  If the original map oscillates by less than
`η` on every face and its replacement graph is `ρ`-close, the whole filled face is contained in
the closed ball of radius `η + ρ` about the original value. -/
theorem cellwisePLFillingMap_dist_le
    {η ρ : ℝ}
    (hsmall : ∀ t : K.Face, ∀ x ∈ K.faceCarrier t.1,
      ∀ y ∈ K.faceCarrier t.1, dist (h x) (h y) < η)
    (hclose : ∀ x ∈ K.oneSkeleton,
      dist (K.graphReplacementMap hcont hinj D C x) (h x) < ρ)
    (x : K.realization) :
    dist (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x) (h x) ≤ η + ρ := by
  let t := K.containingFace x
  let F := K.facePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hcarrierBall : J.carrier ⊆ Metric.closedBall (h x) (η + ρ) := by
    intro y hy
    rw [← K.faceBoundaryMap_image_polygon t] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    let q : StandardFaceBoundary := ⟨p, hp⟩
    let z : K.realization := (K.faceBoundaryLift t q).1
    have hzOne : z ∈ K.oneSkeleton := (K.faceBoundaryLift t q).2
    have hzFace : z ∈ K.faceCarrier t.1 := K.faceBoundaryLift_mem_faceCarrier t q
    have hzClose := hclose z hzOne
    have hxzSmall := hsmall t x hxt z hzFace
    rw [K.faceBoundaryMap_apply t q]
    rw [Metric.mem_closedBall]
    calc
      dist (K.graphReplacementMap hcont hinj D C z) (h x) ≤
          dist (K.graphReplacementMap hcont hinj D C z) (h z) +
            dist (h z) (h x) := dist_triangle _ _ _
      _ ≤ ρ + η := (add_lt_add hzClose
        (by simpa [dist_comm] using hxzSmall)).le
      _ = η + ρ := add_comm _ _
  have hmapClosed : K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x ∈ J.closedRegion := by
    rw [K.cellwisePLFillingMap_eqOn_face t x hxt]
    rw [← F.range_intrinsicMap]
    exact ⟨⟨x, hxt⟩, rfl⟩
  exact Metric.mem_closedBall.mp
    (J.closedRegion_subset_closedBall_of_carrier_subset hcarrierBall hmapClosed)

/-- Under graph-side compatibility, bounded interiors selected for distinct intrinsic faces are
disjoint. -/
theorem disjoint_facePolygonalCircle_interiors
    (hside : K.FaceFillingsGraphAvoidInteriors
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    (t u : K.Face) (htu : t ≠ u) :
    Disjoint
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).interiorRegion
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).interiorRegion := by
  classical
  have hnotSubset : ¬u.1 ⊆ t.1 := by
    intro hsub
    have heq : u.1 = t.1 := Finset.eq_of_subset_of_card_le hsub (by
      rw [K.faces_card u.1 u.2, K.faces_card t.1 t.2])
    exact htu (Subtype.ext heq.symm)
  obtain ⟨w, hwu, hwnt⟩ := Finset.not_subset.mp hnotSubset
  let v : K.UsedVertex := ⟨w, u.1, u.2, hwu⟩
  let x : K.realization := K.vertexPoint v
  have hxu : x ∈ K.faceCarrier u.1 := (K.vertexPoint_mem_faceCarrier_iff v u.1).mpr hwu
  have hxOne : x ∈ K.oneSkeleton := by
    obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem u hwu
    let e : K.Edge := K.faceEdge u i
    apply K.faceCarrier_edge_subset_oneSkeleton e
    apply (K.vertexPoint_mem_faceCarrier_iff v e.1).mpr
    change w ∈ (K.faceEdge u i).1
    rw [K.faceEdge_val, ← hi]
    simp
  have hpU : K.graphReplacementMap hcont hinj D C x ∈
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).carrier := by
    have hp := K.faceChart_mem_frontier_of_mem_oneSkeleton u hxu hxOne
    rw [← K.faceBoundaryMap_image_polygon u]
    refine ⟨(K.facePlaneHomeomorph u ⟨x, hxu⟩).1, hp, ?_⟩
    rw [K.faceBoundaryMap_apply u
      ⟨(K.facePlaneHomeomorph u ⟨x, hxu⟩).1, hp⟩,
      K.faceBoundaryLift_facePlaneHomeomorph u hxu hp]
  have hpNotT : K.graphReplacementMap hcont hinj D C x ∉
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
    intro hpT
    rw [← K.faceBoundaryMap_image_polygon t] at hpT
    obtain ⟨q, hq, hqEq⟩ := hpT
    let q' : StandardFaceBoundary := ⟨q, hq⟩
    have hgraphEq : K.graphReplacementMap hcont hinj D C x =
        K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q').1 := by
      rw [← K.faceBoundaryMap_apply t q']
      exact hqEq.symm
    have hxLift := K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C
      hxOne (K.faceBoundaryLift t q').2 hgraphEq
    have hxt : x ∈ K.faceCarrier t.1 := by
      rw [hxLift]
      exact K.faceBoundaryLift_mem_faceCarrier t q'
    exact hwnt ((K.vertexPoint_mem_faceCarrier_iff v t.1).mp hxt)
  apply (K.facePolygonalCircle t).disjoint_interiorRegion_of_boundary_avoidance
    (K.facePolygonalCircle u)
  · exact (hside u).mono_left (K.facePolygonalCircle_carrier_subset_graphReplacement t)
  · exact (hside t).mono_left (K.facePolygonalCircle_carrier_subset_graphReplacement u)
  · exact ⟨K.graphReplacementMap hcont hinj D C x, hpU, hpNotT⟩

/-- Once the global replacement graph avoids every selected face interior, the coherent
cellwise filling is injective. -/
theorem injective_cellwisePLFillingMap
    (hside : K.FaceFillingsGraphAvoidInteriors
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    Function.Injective (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) := by
  intro x y hxy
  let t := K.containingFace x
  let u := K.containingFace y
  let Ft := K.facePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let Fu := K.facePLFilling
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) u
  let Jt := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let Ju := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) u
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hyu : y ∈ K.faceCarrier u.1 := K.mem_faceCarrier_containingFace y
  have hmapX : K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x =
      Ft.intrinsicMap ⟨x, hxt⟩ :=
    K.cellwisePLFillingMap_eqOn_face t x hxt
  have hmapY : K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) y =
      Fu.intrinsicMap ⟨y, hyu⟩ :=
    K.cellwisePLFillingMap_eqOn_face u y hyu
  have hlocalEq : Ft.intrinsicMap ⟨x, hxt⟩ = Fu.intrinsicMap ⟨y, hyu⟩ :=
    hmapX.symm.trans (hxy.trans hmapY)
  by_cases htu : t = u
  · have hyt : y ∈ K.faceCarrier t.1 := by
      rw [htu]
      exact hyu
    have hyCompat : Ft.intrinsicMap ⟨y, hyt⟩ =
        Fu.intrinsicMap ⟨y, hyu⟩ :=
      K.facePLFilling_intrinsicMap_eq t u hyt hyu
    have hlocalEq' : Ft.intrinsicMap ⟨x, hxt⟩ = Ft.intrinsicMap ⟨y, hyt⟩ := by
      exact hlocalEq.trans hyCompat.symm
    exact congrArg Subtype.val (Ft.injective_intrinsicMap hlocalEq')
  let p : Plane := (K.facePlaneHomeomorph t ⟨x, hxt⟩).1
  let q : Plane := (K.facePlaneHomeomorph u ⟨y, hyu⟩).1
  have hpqMap : Ft.map p = Fu.map q := hlocalEq
  by_cases hpInt : p ∈ interior standardFaceRegion
  · have hpx : Ft.map p ∈ Jt.interiorRegion := Ft.mapsTo_interiorRegion hpInt
    by_cases hqInt : q ∈ interior standardFaceRegion
    · have hqy : Fu.map q ∈ Ju.interiorRegion := Fu.mapsTo_interiorRegion hqInt
      exact False.elim (Set.disjoint_left.mp
        (K.disjoint_facePolygonalCircle_interiors hside t u htu) hpx
        (by rw [show Ft.map p = Fu.map q from hlocalEq]
            exact hqy))
    · have hqFrontier : q ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨(K.facePlaneHomeomorph u ⟨y, hyu⟩).2, hqInt⟩
      have hyOne := K.mem_oneSkeleton_of_faceChart_mem_frontier u hyu hqFrontier
      have hqyGraph : Fu.map q ∈
          K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
        refine ⟨y, hyOne, ?_⟩
        calc
          K.graphReplacementMap hcont hinj D C y =
              K.cellwisePLFillingMap
                (hcont := hcont) (hinj := hinj) (D := D) (C := C) y :=
            (K.cellwisePLFillingMap_eq_graphReplacement hyOne).symm
          _ = Fu.intrinsicMap ⟨y, hyu⟩ := hmapY
          _ = Fu.map q := rfl
      exact False.elim (Set.disjoint_left.mp (hside t) hqyGraph
        (by rw [← hpqMap]; simpa only [Jt] using hpx))
  · have hpFrontier : p ∈ frontier standardFaceRegion := by
      rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
      exact ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).2, hpInt⟩
    have hxOne := K.mem_oneSkeleton_of_faceChart_mem_frontier t hxt hpFrontier
    by_cases hqInt : q ∈ interior standardFaceRegion
    · have hqy : Fu.map q ∈ Ju.interiorRegion := Fu.mapsTo_interiorRegion hqInt
      have hpxGraph : Ft.map p ∈
          K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
        refine ⟨x, hxOne, ?_⟩
        calc
          K.graphReplacementMap hcont hinj D C x =
              K.cellwisePLFillingMap
                (hcont := hcont) (hinj := hinj) (D := D) (C := C) x :=
            (K.cellwisePLFillingMap_eq_graphReplacement hxOne).symm
          _ = Ft.intrinsicMap ⟨x, hxt⟩ := hmapX
          _ = Ft.map p := rfl
      exact False.elim (Set.disjoint_left.mp (hside u) hpxGraph
        (by rw [hpqMap]; simpa only [Ju] using hqy))
    · have hqFrontier : q ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨(K.facePlaneHomeomorph u ⟨y, hyu⟩).2, hqInt⟩
      have hyOne := K.mem_oneSkeleton_of_faceChart_mem_frontier u hyu hqFrontier
      apply K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C hxOne hyOne
      rw [← K.cellwisePLFillingMap_eq_graphReplacement hxOne,
        ← K.cellwisePLFillingMap_eq_graphReplacement hyOne]
      exact hxy

/-- Vertex-side compatibility is sufficient to make the coherent cellwise filling a genuine
topological embedding of the compact intrinsic realization into the plane. -/
theorem cellwisePLFillingMap_isEmbedding
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    _root_.Topology.IsEmbedding (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) := by
  apply Topology.IsClosedEmbedding.toIsEmbedding
  apply Continuous.isClosedEmbedding
  · exact K.continuous_cellwisePLFillingMap
  · exact K.injective_cellwisePLFillingMap
      (K.faceFillingsGraphAvoidInteriors_of_verticesAvoid hvertices)

/-- The image of the coherent cellwise filling is exactly the finite union of its polygonal
closed face regions. -/
theorem range_cellwisePLFillingMap :
    Set.range (K.cellwisePLFillingMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) =
      ⋃ t : K.Face,
        (K.facePolygonalCircle
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    let t := K.containingFace x
    let F := K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
    have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
    apply Set.mem_iUnion.mpr
    refine ⟨t, ?_⟩
    rw [K.cellwisePLFillingMap_eqOn_face t x hxt, ← F.range_intrinsicMap]
    exact ⟨⟨x, hxt⟩, rfl⟩
  · intro y hy
    obtain ⟨t, hyt⟩ := Set.mem_iUnion.mp hy
    let F := K.facePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
    rw [← F.range_intrinsicMap] at hyt
    obtain ⟨x, rfl⟩ := hyt
    refine ⟨x.1, ?_⟩
    exact (K.cellwisePLFillingMap_eqOn_face t x.1 x.2).trans rfl

/-- The exact image of the coherent cellwise filling carries one conforming pure finite plane
complex.  The complex is built from a common arrangement of all face-polygon edge lines, rather
than by taking a nonconforming union of the independently certified face meshes. -/
theorem exists_cellwisePLFilling_targetComplex :
    ∃ L : PlaneComplex,
      L.support = Set.range (K.cellwisePLFillingMap
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)) ∧
      L.IsPure2 := by
  let J : K.Face → PolygonalCircle := fun t ↦ K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  obtain ⟨L, hLsupport, hLpure⟩ := PolygonalFamily.closedRegion_is_polyhedron J
  refine ⟨L, ?_, hLpure⟩
  rw [hLsupport, K.range_cellwisePLFillingMap]
  rfl

/-- A compatible cellwise filling gives a finite plane triangulation of the intrinsic source,
with the plane support coordinate equal to the filling map.  This is the concrete output needed
when a Radó chart replaces an abstract old patch by a polygonal patch in chart coordinates. -/
theorem exists_cellwisePLFilling_retriangulation
    (hvertices : K.FaceFillingsVerticesAvoidClosedRegions
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    ∃ (L : PlaneComplex) (_ : L.IsPure2)
      (e : L.support ≃ₜ K.realization),
      ∀ p : L.support,
        K.cellwisePLFillingMap
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) (e p) = p.1 := by
  let f := K.cellwisePLFillingMap
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  obtain ⟨L, hLsupport, hLpure⟩ := K.exists_cellwisePLFilling_targetComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  have hfEmbedding : _root_.Topology.IsEmbedding f :=
    K.cellwisePLFillingMap_isEmbedding hvertices
  let ef : K.realization ≃ₜ Set.range f := hfEmbedding.toHomeomorph
  let e : L.support ≃ₜ K.realization :=
    (Homeomorph.setCongr hLsupport).trans ef.symm
  refine ⟨L, hLpure, e, ?_⟩
  intro p
  have hpRange : p.1 ∈ Set.range f := by
    rw [← hLsupport]
    exact p.2
  change f (ef.symm ⟨p.1, hpRange⟩) = p.1
  exact congrArg Subtype.val (ef.apply_symm_apply ⟨p.1, hpRange⟩)

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
