/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicCloseGraphApproximation
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicCellwiseExtension
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision

/-!
# Cellwise extension of a close intrinsic graph approximation

This file applies polygonal Schoenflies face by face to the arbitrarily close graph embedding
from `IntrinsicCloseGraphApproximation`.  The proofs parallel the first intrinsic cellwise
construction, but the boundary map is now the second, metrically controlled graph replacement.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}
  {ε : ℝ}

namespace CloseGraphApproximation

variable (A : K.CloseGraphApproximation
  (hcont := hcont) (hinj := hinj) (D := D) (C := C) ε)

/-- The close graph embedding in standard coordinates on one face boundary. -/
noncomputable def faceBoundaryMap (t : K.Face) : Plane → Plane :=
  A.planeMap ∘
    K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t

theorem faceBoundaryMap_apply (t : K.Face) (p : StandardFaceBoundary) :
    A.faceBoundaryMap t p.1 = A.intrinsicMap (K.faceBoundaryLift t p).1 := by
  change A.planeMap (K.faceBoundaryMap t p.1) =
    A.planeMap (K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t p).1)
  rw [K.faceBoundaryMap_apply t p]

theorem continuousOn_faceBoundaryMap (t : K.Face) :
    ContinuousOn (A.faceBoundaryMap t) (frontier standardFaceRegion) := by
  apply A.isPLOnModel.continuousOn.comp (K.continuousOn_faceBoundaryMap t)
  intro p hp
  rw [K.replacementGraphComplex_support_eq_image]
  let q : StandardFaceBoundary := ⟨p, hp⟩
  exact ⟨(K.faceBoundaryLift t q).1, (K.faceBoundaryLift t q).2,
    (K.faceBoundaryMap_apply t q).symm⟩

theorem injOn_faceBoundaryMap (t : K.Face) :
    Set.InjOn (A.faceBoundaryMap t) (frontier standardFaceRegion) := by
  intro p hp q hq hpq
  apply K.faceBoundaryMap_injectiveOn t hp hq
  exact A.injOnModel
    (by
      rw [K.replacementGraphComplex_support_eq_image]
      let p' : StandardFaceBoundary := ⟨p, hp⟩
      exact ⟨(K.faceBoundaryLift t p').1, (K.faceBoundaryLift t p').2,
        (K.faceBoundaryMap_apply t p').symm⟩)
    (by
      rw [K.replacementGraphComplex_support_eq_image]
      let q' : StandardFaceBoundary := ⟨q, hq⟩
      exact ⟨(K.faceBoundaryLift t q').1, (K.faceBoundaryLift t q').2,
        (K.faceBoundaryMap_apply t q').symm⟩)
    hpq

theorem faceBoundaryMap_isPLOnSet (t : K.Face) :
    IsPLOnSet (frontier standardFaceRegion) (A.faceBoundaryMap t) := by
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let b₀ := K.faceBoundaryMap
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  have hsource : standardTriangleCircle.carrier = frontier standardFaceRegion := by
    rw [standardTriangleCircle_carrier]
    simp only [standardFaceRegion, standardTrianglePlaneComplex_support]
  have holdPL : IsPLOnSet standardTriangleCircle.carrier b₀ := by
    rw [hsource]
    exact K.faceBoundaryMap_isPLOnSet t
  have holdInj : Set.InjOn b₀ standardTriangleCircle.carrier := by
    rw [hsource]
    exact K.faceBoundaryMap_injectiveOn t
  have holdImage : b₀ '' standardTriangleCircle.carrier = J.carrier := by
    rw [hsource]
    exact K.faceBoundaryMap_image_polygon t
  have hcomp := IsPLOnSet.comp_polygonal_embedding standardTriangleCircle J
    holdPL holdInj holdImage (A.facewisePL t)
  rw [hsource] at hcomp
  exact hcomp

/-- The image of a close face-boundary map is a polygonal circle. -/
theorem exists_imagePolygon (t : K.Face) :
    ∃ J : PolygonalCircle,
      J.carrier = A.faceBoundaryMap t '' frontier standardFaceRegion := by
  obtain ⟨J, hJ⟩ := standardTriangleCircle.exists_image_of_isPLOnSet_embedding
    (by simpa only [standardTriangleCircle_carrier, standardFaceRegion,
      standardTrianglePlaneComplex_support] using A.faceBoundaryMap_isPLOnSet t)
    (by simpa only [standardTriangleCircle_carrier, standardFaceRegion,
      standardTrianglePlaneComplex_support] using A.injOn_faceBoundaryMap t)
  exact ⟨J, by simpa only [standardTriangleCircle_carrier, standardFaceRegion,
    standardTrianglePlaneComplex_support] using hJ⟩

/-- The polygon which is the exact image of one close face-boundary map. -/
noncomputable def imagePolygon (t : K.Face) : PolygonalCircle :=
  Classical.choose (A.exists_imagePolygon t)

theorem imagePolygon_carrier (t : K.Face) :
    (A.imagePolygon t).carrier =
      A.faceBoundaryMap t '' frontier standardFaceRegion := by
  exact Classical.choose_spec (A.exists_imagePolygon t)

/-- A certified PL filling of one close face boundary. -/
structure FaceFilling (t : K.Face) where
  /-- The `map` declaration. -/
  map : Plane → Plane
  eqOn_boundary : Set.EqOn map (A.faceBoundaryMap t) (frontier standardFaceRegion)
  continuousOn : ContinuousOn map standardFaceRegion
  injectiveOn : Set.InjOn map standardFaceRegion
  image_eq : map '' standardFaceRegion = (A.imagePolygon t).closedRegion
  isPLOnSet : IsPLOnSet standardFaceRegion map
  certificate : Nonempty (FinitePLHomeomorphBetween map standardFaceRegion
    (A.imagePolygon t).closedRegion)

theorem exists_faceFilling (t : K.Face) : Nonempty (A.FaceFilling t) := by
  obtain ⟨F, hboundary, hcontinuous, hFinj, himage, hpl, hcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary
      standardTrianglePlaneComplex_isTriangle (A.imagePolygon t)
      (A.faceBoundaryMap_isPLOnSet t) (A.injOn_faceBoundaryMap t)
      (A.imagePolygon_carrier t).symm
  exact ⟨{
    map := F
    eqOn_boundary := hboundary
    continuousOn := hcontinuous
    injectiveOn := hFinj
    image_eq := himage
    isPLOnSet := hpl
    certificate := hcert }⟩

/-- The `faceFilling` declaration. -/
noncomputable def faceFilling (t : K.Face) : A.FaceFilling t :=
  Classical.choice (A.exists_faceFilling t)

namespace FaceFilling

/-- The `faceInteriorMap` declaration. -/
noncomputable def faceInteriorMap {t : K.Face} (F : A.FaceFilling t) :
    K.ClosedFace t → Plane :=
  fun x ↦ F.map (K.facePlaneHomeomorph t x).1

theorem continuous_intrinsicMap {t : K.Face} (F : A.FaceFilling t) :
    Continuous F.faceInteriorMap := by
  have hF : Continuous (fun p : standardFaceRegion ↦ F.map p.1) :=
    continuousOn_iff_continuous_domRestrict.mp F.continuousOn
  exact hF.comp (K.facePlaneHomeomorph t).continuous

theorem injective_intrinsicMap {t : K.Face} (F : A.FaceFilling t) :
    Function.Injective F.faceInteriorMap := by
  intro x y hxy
  apply (K.facePlaneHomeomorph t).injective
  apply Subtype.ext
  exact F.injectiveOn (K.facePlaneHomeomorph t x).2
    (K.facePlaneHomeomorph t y).2 hxy

theorem range_intrinsicMap {t : K.Face} (F : A.FaceFilling t) :
    Set.range F.faceInteriorMap = (A.imagePolygon t).closedRegion := by
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

theorem mapsTo_interiorRegion {t : K.Face} (F : A.FaceFilling t) :
    Set.MapsTo F.map (interior standardFaceRegion)
      (A.imagePolygon t).interiorRegion := by
  intro p hp
  have hpRegion : p ∈ standardFaceRegion := interior_subset hp
  have hclosed : F.map p ∈ (A.imagePolygon t).closedRegion := by
    rw [← F.image_eq]
    exact ⟨p, hpRegion, rfl⟩
  rw [(A.imagePolygon t).closedRegion_eq_union] at hclosed
  rcases hclosed with hbounded | hcarrier
  · exact hbounded
  · rw [A.imagePolygon_carrier t] at hcarrier
    obtain ⟨q, hq, hqmap⟩ := hcarrier
    have hmapEq : F.map p = F.map q := by
      rw [F.eqOn_boundary hq]
      exact hqmap.symm
    have hpq : p = q := F.injectiveOn hpRegion
      (standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset hq) hmapEq
    subst q
    exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hp hq)

end FaceFilling

theorem faceFilling_eq_of_boundaryLift_eq
    {t u : K.Face} {p q : StandardFaceBoundary}
    (hpq : (K.faceBoundaryLift t p).1 = (K.faceBoundaryLift u q).1) :
    (A.faceFilling t).map p.1 = (A.faceFilling u).map q.1 := by
  rw [(A.faceFilling t).eqOn_boundary p.2,
    (A.faceFilling u).eqOn_boundary q.2,
    A.faceBoundaryMap_apply t p, A.faceBoundaryMap_apply u q, hpq]

theorem faceFilling_intrinsicMap_eq
    (t u : K.Face) {x : K.realization}
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1) :
    FaceFilling.faceInteriorMap A (A.faceFilling t) ⟨x, hxt⟩ =
      FaceFilling.faceInteriorMap A (A.faceFilling u) ⟨x, hxu⟩ := by
  by_cases htu : t = u
  · subst u
    rfl
  let p : StandardFaceBoundary :=
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1,
      K.faceChart_mem_frontier_of_mem_distinct_faces htu hxt hxu⟩
  let q : StandardFaceBoundary :=
    ⟨(K.facePlaneHomeomorph u ⟨x, hxu⟩).1,
      K.faceChart_mem_frontier_of_mem_distinct_faces (Ne.symm htu) hxu hxt⟩
  change (A.faceFilling t).map p.1 = (A.faceFilling u).map q.1
  apply A.faceFilling_eq_of_boundaryLift_eq
  rw [K.faceBoundaryLift_facePlaneHomeomorph t hxt p.2,
    K.faceBoundaryLift_facePlaneHomeomorph u hxu q.2]

/-- The finite family of close face fillings, glued on the canonical realization. -/
noncomputable def closeCellwiseMap (x : K.realization) : Plane :=
  FaceFilling.faceInteriorMap A (A.faceFilling (K.containingFace x))
    ⟨x, K.mem_faceCarrier_containingFace x⟩

theorem closeCellwiseMap_eqOn_face (t : K.Face) (x : K.realization)
    (hxt : x ∈ K.faceCarrier t.1) :
    A.closeCellwiseMap x =
      FaceFilling.faceInteriorMap A (A.faceFilling t) ⟨x, hxt⟩ := by
  exact A.faceFilling_intrinsicMap_eq (K.containingFace x) t
    (K.mem_faceCarrier_containingFace x) hxt

theorem continuous_closeCellwiseMap : Continuous A.closeCellwiseMap := by
  let carriers : K.Face → Set K.realization := fun t ↦ K.faceCarrier t.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hclosed : ∀ t : K.Face, IsClosed (carriers t) := fun t ↦ K.faceCarrier_closed t.1
  have hlocal : ∀ t : K.Face, ContinuousOn A.closeCellwiseMap (carriers t) := by
    intro t
    rw [continuousOn_iff_continuous_domRestrict]
    convert FaceFilling.continuous_intrinsicMap A (A.faceFilling t) using 1
    funext x
    exact A.closeCellwiseMap_eqOn_face t x.1 x.2
  exact hfinite.continuous K.realization_eq_iUnion_faceCarrier.symm hclosed hlocal

theorem closeCellwiseMap_eq_intrinsicMap {x : K.realization} (hx : x ∈ K.oneSkeleton) :
    A.closeCellwiseMap x = A.intrinsicMap x := by
  let t := K.containingFace x
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hp := K.faceChart_mem_frontier_of_mem_oneSkeleton t hxt hx
  rw [A.closeCellwiseMap_eqOn_face t x hxt]
  change (A.faceFilling t).map (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 = _
  rw [(A.faceFilling t).eqOn_boundary hp, A.faceBoundaryMap_apply t
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩,
    K.faceBoundaryLift_facePlaneHomeomorph t hxt hp]

theorem vertexPoint_mem_oneSkeleton (v : K.UsedVertex) :
    K.vertexPoint v ∈ K.oneSkeleton := by
  obtain ⟨t, ht, hvt⟩ := v.2
  let T : K.Face := ⟨t, ht⟩
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem T hvt
  let e : K.Edge := K.faceEdge T i
  refine ⟨e, (K.vertexPoint_mem_faceCarrier_iff v e.1).mpr ?_⟩
  change v.1 ∈ (K.faceEdge T i).1
  rw [K.faceEdge_val, ← hi]
  simp

/-- The approximated graph avoids the selected closed region of every nonincident face at all
outside vertices. -/
def VerticesAvoidClosedRegions : Prop :=
  ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
    A.intrinsicMap (K.vertexPoint v) ∉ (A.imagePolygon t).closedRegion

theorem verticesAvoidClosedRegions_of_close
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ (t : K.Face) (v : K.UsedVertex), v.1 ∉ t.1 →
      Disjoint (Metric.closedBall (h (K.vertexPoint v)) r)
        (Metric.cthickening r (h '' K.faceCarrier t.1)))
    (hclose : ∀ x ∈ K.oneSkeleton, dist (A.intrinsicMap x) (h x) < r) :
    A.VerticesAvoidClosedRegions := by
  intro t v hvt
  let b := A.faceBoundaryMap t
  let hface := K.faceOriginalMap (h := h) t
  have hbcont : ContinuousOn b (frontier standardFaceRegion) :=
    A.continuousOn_faceBoundaryMap t
  have hhface : ContinuousOn hface standardFaceRegion :=
    K.continuousOn_faceOriginalMap hcont t
  have hbclose : ∀ p ∈ frontier standardFaceRegion, dist (b p) (hface p) < r := by
    intro p hp
    let q : StandardFaceBoundary := ⟨p, hp⟩
    have hq := hclose (K.faceBoundaryLift t q).1 (K.faceBoundaryLift t q).2
    rw [← A.faceBoundaryMap_apply t q] at hq
    have horiginal : hface p = h (K.faceBoundaryLift t q).1 := by
      change K.faceOriginalMap (h := h) t p = _
      rw [K.faceOriginalMap_apply t ⟨p, standardFaceBoundary_mem_region q⟩]
      rfl
    rw [horiginal]
    exact hq
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      standardTrianglePlaneComplex.isCompact_support.isClosed hr hbcont hhface hbclose
  have hvGraph : K.vertexPoint v ∈ K.oneSkeleton :=
    vertexPoint_mem_oneSkeleton (K := K) v
  have hvAvoid : A.intrinsicMap (K.vertexPoint v) ∉ F '' standardFaceRegion := by
    rintro ⟨p, hp, hFp⟩
    have hvBall : A.intrinsicMap (K.vertexPoint v) ∈
        Metric.closedBall (h (K.vertexPoint v)) r :=
      Metric.mem_closedBall.mpr (hclose (K.vertexPoint v) hvGraph).le
    have hFthick : F p ∈ Metric.cthickening r (h '' K.faceCarrier t.1) := by
      apply Metric.mem_cthickening_of_dist_le (F p) (hface p) r
        (h '' K.faceCarrier t.1)
      · exact K.faceOriginalMap_mem_face_image t ⟨p, hp⟩
      · exact hFclose p hp
    exact Set.disjoint_left.mp (hsep t v hvt) hvBall (hFp ▸ hFthick)
  have hvExterior : A.intrinsicMap (K.vertexPoint v) ∈
      (A.imagePolygon t).exteriorRegion := by
    apply (A.imagePolygon t).mem_exteriorRegion_of_continuous_extension
      standardTrianglePlaneComplex_isTriangle hbcont
      (A.injOn_faceBoundaryMap t) (A.imagePolygon_carrier t).symm
      hFcont hFeq hvAvoid
  intro hvClosed
  exact Set.disjoint_left.mp
    (A.imagePolygon t).disjoint_closedRegion_exteriorRegion hvClosed hvExterior

theorem imagePolygon_carrier_subset_graph (t : K.Face) :
    (A.imagePolygon t).carrier ⊆ A.intrinsicMap '' K.oneSkeleton := by
  intro y hy
  rw [A.imagePolygon_carrier t] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  let q : StandardFaceBoundary := ⟨p, hp⟩
  exact ⟨(K.faceBoundaryLift t q).1, (K.faceBoundaryLift t q).2,
    (A.faceBoundaryMap_apply t q).symm⟩

theorem mem_faceCarrier_of_intrinsicMap_mem_imagePolygon
    (t : K.Face) {x : K.realization} (hx : x ∈ K.oneSkeleton)
    (himage : A.intrinsicMap x ∈ (A.imagePolygon t).carrier) :
    x ∈ K.faceCarrier t.1 := by
  rw [A.imagePolygon_carrier t] at himage
  obtain ⟨p, hp, hpEq⟩ := himage
  let q : StandardFaceBoundary := ⟨p, hp⟩
  have hgraphEq : A.intrinsicMap x = A.intrinsicMap (K.faceBoundaryLift t q).1 := by
    rw [← A.faceBoundaryMap_apply t q]
    exact hpEq.symm
  have hxEq := A.injOn_intrinsicMap hx (K.faceBoundaryLift t q).2 hgraphEq
  rw [hxEq]
  exact K.faceBoundaryLift_mem_faceCarrier t q

theorem intrinsicMap_mem_imagePolygon
    (t : K.Face) {x : K.realization} (hxt : x ∈ K.faceCarrier t.1)
    (hx : x ∈ K.oneSkeleton) :
    A.intrinsicMap x ∈ (A.imagePolygon t).carrier := by
  have hp := K.faceChart_mem_frontier_of_mem_oneSkeleton t hxt hx
  rw [A.imagePolygon_carrier t]
  refine ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp, ?_⟩
  rw [A.faceBoundaryMap_apply t
    ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).1, hp⟩,
    K.faceBoundaryLift_facePlaneHomeomorph t hxt hp]

/-- The global close graph avoids the bounded interior selected for every filled face. -/
def GraphAvoidsInteriors : Prop :=
  ∀ t : K.Face,
    Disjoint (A.intrinsicMap '' K.oneSkeleton) (A.imagePolygon t).interiorRegion

theorem vertex_mem_exterior
    (hvertices : A.VerticesAvoidClosedRegions)
    (t : K.Face) (v : K.UsedVertex) (hvt : v.1 ∉ t.1) :
    A.intrinsicMap (K.vertexPoint v) ∈ (A.imagePolygon t).exteriorRegion := by
  let J := A.imagePolygon t
  have hnotClosed := hvertices t v hvt
  have hnotInterior : A.intrinsicMap (K.vertexPoint v) ∉ J.interiorRegion := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inl hv
  have hnotCarrier : A.intrinsicMap (K.vertexPoint v) ∉ J.carrier := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inr hv
  have hoff : A.intrinsicMap (K.vertexPoint v) ∈ J.carrierᶜ := hnotCarrier
  rw [← J.interior_union_exterior] at hoff
  exact hoff.resolve_left hnotInterior

/-- The endpoint exterior condition propagates along each connected intrinsic edge, so the
whole close graph avoids every nonincident bounded face interior. -/
theorem graphAvoidsInteriors_of_verticesAvoid
    (hvertices : A.VerticesAvoidClosedRegions) : A.GraphAvoidsInteriors := by
  intro t
  let J := A.imagePolygon t
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
      (A.intrinsicMap_mem_imagePolygon t hxt ⟨e, hxe⟩)
  let I := Set.Icc (0 : ℝ) 1
  let z0 : I := ⟨0, by simp [I]⟩
  let z1 : I := ⟨1, by simp [I]⟩
  let gpath : I → Plane := fun s ↦ A.intrinsicMap (K.edgePath e s)
  have hpathCarrier (s : I) : K.edgePath e s ∈ K.faceCarrier e.1 := by
    rw [← K.range_edgePath e]
    exact ⟨s, rfl⟩
  have hpathOne (s : I) : K.edgePath e s ∈ K.oneSkeleton :=
    ⟨e, hpathCarrier s⟩
  have hgpath : Continuous gpath := by
    simpa only [gpath, Function.comp_def] using
      A.continuousOn_intrinsicMap.comp_continuous (K.continuous_edgePath e) hpathOne
  have hoffCarrier {B : Set I}
      (houtside : ∀ s ∈ B, K.edgePath e s ∉ K.faceCarrier t.1) :
      Set.MapsTo gpath B J.carrierᶜ := by
    intro s hs hcarrier
    exact houtside s hs
      (A.mem_faceCarrier_of_intrinsicMap_mem_imagePolygon t (hpathOne s) hcarrier)
  let r : I := K.edgeParameter e x hxe
  have hxPath : K.edgePath e r = x := K.edgePath_edgeParameter e x hxe
  have hsharedImpossible (hxt : x ∈ K.faceCarrier t.1) : False := by
    exact Set.disjoint_left.mp hinteriorCarrier hxInterior
      (A.intrinsicMap_mem_imagePolygon t hxt ⟨e, hxe⟩)
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
    · let B : Set I := Set.Ioc z0 z1
      have hBout : ∀ s ∈ B, K.edgePath e s ∉ K.faceCarrier t.1 := by
        intro s hs hsFace
        have hzero := hsFace (K.edgeSecond e) hsecond
        rw [K.edgePath_apply_second] at hzero
        have hspos : 0 < s.1 := by exact_mod_cast hs.1
        exact (ne_of_gt hspos) hzero
      have hz1Exterior : gpath z1 ∈ J.exteriorRegion := by
        have hv := A.vertex_mem_exterior hvertices t (K.edgeSecondUsed e) hsecond
        simpa only [gpath, z1, K.edgePath_one, K.vertexPoint_edgeSecondUsed] using hv
      have hBExterior : Set.MapsTo gpath B J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_Ioc hgpath.continuousOn
          (hoffCarrier hBout) ⟨z1, by simp [B, z0, z1], hz1Exterior⟩
      have hrB : r ∈ B := by
        constructor
        · change (0 : ℝ) < r.1
          exact lt_of_le_of_ne r.2.1 (Ne.symm hr0)
        · change r.1 ≤ (1 : ℝ)
          exact r.2.2
      have hrExterior := hBExterior hrB
      change A.intrinsicMap (K.edgePath e r) ∈ J.exteriorRegion at hrExterior
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
      · let B : Set I := Set.Ico z0 z1
        have hBout : ∀ s ∈ B, K.edgePath e s ∉ K.faceCarrier t.1 := by
          intro s hs hsFace
          have hzero := hsFace (K.edgeFirst e) hfirst
          rw [K.edgePath_apply_first] at hzero
          have hslt : s.1 < 1 := by exact_mod_cast hs.2
          linarith
        have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
          have hv := A.vertex_mem_exterior hvertices t (K.edgeFirstUsed e) hfirst
          simpa only [gpath, z0, K.edgePath_zero, K.vertexPoint_edgeFirstUsed] using hv
        have hBExterior : Set.MapsTo gpath B J.exteriorRegion :=
          J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_Ico hgpath.continuousOn
            (hoffCarrier hBout) ⟨z0, by simp [B, z0, z1], hz0Exterior⟩
        have hrB : r ∈ B := by
          constructor
          · change (0 : ℝ) ≤ r.1
            exact r.2.1
          · change r.1 < (1 : ℝ)
            exact lt_of_le_of_ne r.2.2 hr1
        have hrExterior := hBExterior hrB
        change A.intrinsicMap (K.edgePath e r) ∈ J.exteriorRegion at hrExterior
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
        have hv := A.vertex_mem_exterior hvertices t (K.edgeFirstUsed e) hfirst
        simpa only [gpath, z0, K.edgePath_zero, K.vertexPoint_edgeFirstUsed] using hv
      have hAllExterior : Set.MapsTo gpath Set.univ J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_univ hgpath.continuousOn
          (hoffCarrier fun s _ ↦ hAllOutside s) ⟨z0, Set.mem_univ _, hz0Exterior⟩
      have hrExterior := hAllExterior (Set.mem_univ r)
      change A.intrinsicMap (K.edgePath e r) ∈ J.exteriorRegion at hrExterior
      rw [hxPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hxInterior hrExterior

/-- Quantitative control of the close cellwise filling. -/
theorem closeCellwiseMap_dist_le
    {η ρ : ℝ}
    (hsmall : ∀ t : K.Face, ∀ x ∈ K.faceCarrier t.1,
      ∀ y ∈ K.faceCarrier t.1, dist (h x) (h y) < η)
    (hclose : ∀ x ∈ K.oneSkeleton, dist (A.intrinsicMap x) (h x) < ρ)
    (x : K.realization) :
    dist (A.closeCellwiseMap x) (h x) ≤ η + ρ := by
  let t := K.containingFace x
  let F := A.faceFilling t
  let J := A.imagePolygon t
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hcarrierBall : J.carrier ⊆ Metric.closedBall (h x) (η + ρ) := by
    intro y hy
    rw [A.imagePolygon_carrier t] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    let q : StandardFaceBoundary := ⟨p, hp⟩
    let z : K.realization := (K.faceBoundaryLift t q).1
    have hzOne : z ∈ K.oneSkeleton := (K.faceBoundaryLift t q).2
    have hzFace : z ∈ K.faceCarrier t.1 := K.faceBoundaryLift_mem_faceCarrier t q
    have hzClose := hclose z hzOne
    have hxzSmall := hsmall t x hxt z hzFace
    rw [A.faceBoundaryMap_apply t q, Metric.mem_closedBall]
    calc
      dist (A.intrinsicMap z) (h x) ≤
          dist (A.intrinsicMap z) (h z) + dist (h z) (h x) := dist_triangle _ _ _
      _ ≤ ρ + η := (add_lt_add hzClose
        (by simpa [dist_comm] using hxzSmall)).le
      _ = η + ρ := add_comm _ _
  have hmapClosed : A.closeCellwiseMap x ∈ J.closedRegion := by
    rw [A.closeCellwiseMap_eqOn_face t x hxt]
    rw [← FaceFilling.range_intrinsicMap A F]
    exact ⟨⟨x, hxt⟩, rfl⟩
  exact Metric.mem_closedBall.mp
    (J.closedRegion_subset_closedBall_of_carrier_subset hcarrierBall hmapClosed)

/-- Distinct face polygons have disjoint bounded interiors once the global graph avoids all of
them. -/
theorem disjoint_imagePolygon_interiors
    (hside : A.GraphAvoidsInteriors) (t u : K.Face) (htu : t ≠ u) :
    Disjoint (A.imagePolygon t).interiorRegion (A.imagePolygon u).interiorRegion := by
  classical
  have hnotSubset : ¬u.1 ⊆ t.1 := by
    intro hsub
    have heq : u.1 = t.1 := Finset.eq_of_subset_of_card_le hsub (by
      rw [K.faces_card u.1 u.2, K.faces_card t.1 t.2])
    exact htu (Subtype.ext heq.symm)
  obtain ⟨w, hwu, hwnt⟩ := Finset.not_subset.mp hnotSubset
  let v : K.UsedVertex := ⟨w, u.1, u.2, hwu⟩
  let x : K.realization := K.vertexPoint v
  have hxu : x ∈ K.faceCarrier u.1 :=
    (K.vertexPoint_mem_faceCarrier_iff v u.1).mpr hwu
  have hxOne : x ∈ K.oneSkeleton := vertexPoint_mem_oneSkeleton (K := K) v
  have hpU : A.intrinsicMap x ∈ (A.imagePolygon u).carrier :=
    A.intrinsicMap_mem_imagePolygon u hxu hxOne
  have hpNotT : A.intrinsicMap x ∉ (A.imagePolygon t).carrier := by
    intro hpT
    have hxt := A.mem_faceCarrier_of_intrinsicMap_mem_imagePolygon t hxOne hpT
    exact hwnt ((K.vertexPoint_mem_faceCarrier_iff v t.1).mp hxt)
  apply (A.imagePolygon t).disjoint_interiorRegion_of_boundary_avoidance (A.imagePolygon u)
  · exact (hside u).mono_left (A.imagePolygon_carrier_subset_graph t)
  · exact (hside t).mono_left (A.imagePolygon_carrier_subset_graph u)
  · exact ⟨A.intrinsicMap x, hpU, hpNotT⟩

/-- Graph-side compatibility makes the coherent close cellwise filling injective. -/
theorem injective_closeCellwiseMap (hside : A.GraphAvoidsInteriors) :
    Function.Injective A.closeCellwiseMap := by
  intro x y hxy
  let t := K.containingFace x
  let u := K.containingFace y
  let Ft := A.faceFilling t
  let Fu := A.faceFilling u
  let Jt := A.imagePolygon t
  let Ju := A.imagePolygon u
  have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
  have hyu : y ∈ K.faceCarrier u.1 := K.mem_faceCarrier_containingFace y
  have hmapX : A.closeCellwiseMap x = FaceFilling.faceInteriorMap A Ft ⟨x, hxt⟩ :=
    A.closeCellwiseMap_eqOn_face t x hxt
  have hmapY : A.closeCellwiseMap y = FaceFilling.faceInteriorMap A Fu ⟨y, hyu⟩ :=
    A.closeCellwiseMap_eqOn_face u y hyu
  have hlocalEq : FaceFilling.faceInteriorMap A Ft ⟨x, hxt⟩ =
      FaceFilling.faceInteriorMap A Fu ⟨y, hyu⟩ :=
    hmapX.symm.trans (hxy.trans hmapY)
  by_cases htu : t = u
  · have hyt : y ∈ K.faceCarrier t.1 := by rw [htu]; exact hyu
    have hyCompat : FaceFilling.faceInteriorMap A Ft ⟨y, hyt⟩ =
        FaceFilling.faceInteriorMap A Fu ⟨y, hyu⟩ :=
      A.faceFilling_intrinsicMap_eq t u hyt hyu
    have hlocalEq' : FaceFilling.faceInteriorMap A Ft ⟨x, hxt⟩ =
        FaceFilling.faceInteriorMap A Ft ⟨y, hyt⟩ :=
      hlocalEq.trans hyCompat.symm
    exact congrArg Subtype.val
      (FaceFilling.injective_intrinsicMap A Ft hlocalEq')
  let p : Plane := (K.facePlaneHomeomorph t ⟨x, hxt⟩).1
  let q : Plane := (K.facePlaneHomeomorph u ⟨y, hyu⟩).1
  have hpqMap : Ft.map p = Fu.map q := hlocalEq
  by_cases hpInt : p ∈ interior standardFaceRegion
  · have hpx : Ft.map p ∈ Jt.interiorRegion :=
      FaceFilling.mapsTo_interiorRegion A Ft hpInt
    by_cases hqInt : q ∈ interior standardFaceRegion
    · have hqy : Fu.map q ∈ Ju.interiorRegion :=
        FaceFilling.mapsTo_interiorRegion A Fu hqInt
      exact False.elim (Set.disjoint_left.mp
        (A.disjoint_imagePolygon_interiors hside t u htu) hpx
        (by rw [show Ft.map p = Fu.map q from hlocalEq]; exact hqy))
    · have hqFrontier : q ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨(K.facePlaneHomeomorph u ⟨y, hyu⟩).2, hqInt⟩
      have hyOne := K.mem_oneSkeleton_of_faceChart_mem_frontier u hyu hqFrontier
      have hqyGraph : Fu.map q ∈ A.intrinsicMap '' K.oneSkeleton := by
        refine ⟨y, hyOne, ?_⟩
        calc
          A.intrinsicMap y = A.closeCellwiseMap y :=
            (A.closeCellwiseMap_eq_intrinsicMap hyOne).symm
          _ = FaceFilling.faceInteriorMap A Fu ⟨y, hyu⟩ := hmapY
          _ = Fu.map q := rfl
      exact False.elim (Set.disjoint_left.mp (hside t) hqyGraph
        (by rw [← hpqMap]; simpa only [Jt] using hpx))
  · have hpFrontier : p ∈ frontier standardFaceRegion := by
      rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
      exact ⟨(K.facePlaneHomeomorph t ⟨x, hxt⟩).2, hpInt⟩
    have hxOne := K.mem_oneSkeleton_of_faceChart_mem_frontier t hxt hpFrontier
    by_cases hqInt : q ∈ interior standardFaceRegion
    · have hqy : Fu.map q ∈ Ju.interiorRegion :=
        FaceFilling.mapsTo_interiorRegion A Fu hqInt
      have hpxGraph : Ft.map p ∈ A.intrinsicMap '' K.oneSkeleton := by
        refine ⟨x, hxOne, ?_⟩
        calc
          A.intrinsicMap x = A.closeCellwiseMap x :=
            (A.closeCellwiseMap_eq_intrinsicMap hxOne).symm
          _ = FaceFilling.faceInteriorMap A Ft ⟨x, hxt⟩ := hmapX
          _ = Ft.map p := rfl
      exact False.elim (Set.disjoint_left.mp (hside u) hpxGraph
        (by rw [hpqMap]; simpa only [Ju] using hqy))
    · have hqFrontier : q ∈ frontier standardFaceRegion := by
        rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq]
        exact ⟨(K.facePlaneHomeomorph u ⟨y, hyu⟩).2, hqInt⟩
      have hyOne := K.mem_oneSkeleton_of_faceChart_mem_frontier u hyu hqFrontier
      apply A.injOn_intrinsicMap hxOne hyOne
      rw [← A.closeCellwiseMap_eq_intrinsicMap hxOne,
        ← A.closeCellwiseMap_eq_intrinsicMap hyOne]
      exact hxy

theorem closeCellwiseMap_isEmbedding (hvertices : A.VerticesAvoidClosedRegions) :
    _root_.Topology.IsEmbedding A.closeCellwiseMap := by
  apply Topology.IsClosedEmbedding.toIsEmbedding
  apply Continuous.isClosedEmbedding
  · exact A.continuous_closeCellwiseMap
  · exact A.injective_closeCellwiseMap (A.graphAvoidsInteriors_of_verticesAvoid hvertices)

theorem range_closeCellwiseMap :
    Set.range A.closeCellwiseMap = ⋃ t : K.Face, (A.imagePolygon t).closedRegion := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    let t := K.containingFace x
    let F := A.faceFilling t
    have hxt : x ∈ K.faceCarrier t.1 := K.mem_faceCarrier_containingFace x
    apply Set.mem_iUnion.mpr
    refine ⟨t, ?_⟩
    rw [A.closeCellwiseMap_eqOn_face t x hxt,
      ← FaceFilling.range_intrinsicMap A F]
    exact ⟨⟨x, hxt⟩, rfl⟩
  · intro y hy
    obtain ⟨t, hyt⟩ := Set.mem_iUnion.mp hy
    let F := A.faceFilling t
    rw [← FaceFilling.range_intrinsicMap A F] at hyt
    obtain ⟨x, rfl⟩ := hyt
    refine ⟨x.1, ?_⟩
    exact (A.closeCellwiseMap_eqOn_face t x.1 x.2).trans rfl

theorem exists_targetComplex :
    ∃ L : PlaneComplex, L.support = Set.range A.closeCellwiseMap ∧ L.IsPure2 := by
  let J : K.Face → PolygonalCircle := fun t ↦ A.imagePolygon t
  obtain ⟨L, hLsupport, hLpure⟩ := PolygonalFamily.closedRegion_is_polyhedron J
  refine ⟨L, ?_, hLpure⟩
  rw [hLsupport, A.range_closeCellwiseMap]
  rfl

/-- A compatible close cellwise filling presents the intrinsic source as one finite pure plane
complex. -/
theorem exists_retriangulation (hvertices : A.VerticesAvoidClosedRegions) :
    ∃ (L : PlaneComplex) (_hLpure : L.IsPure2) (e : L.support ≃ₜ K.realization),
      ∀ p : L.support, A.closeCellwiseMap (e p) = p.1 := by
  let f := A.closeCellwiseMap
  obtain ⟨L, hLsupport, hLpure⟩ := A.exists_targetComplex
  have hfEmbedding : _root_.Topology.IsEmbedding f := A.closeCellwiseMap_isEmbedding hvertices
  let ef : K.realization ≃ₜ Set.range f := hfEmbedding.toHomeomorph
  let e : L.support ≃ₜ K.realization :=
    (Homeomorph.setCongr hLsupport).trans ef.symm
  refine ⟨L, hLpure, e, ?_⟩
  intro p
  have hpRange : p.1 ∈ Set.range f := by rw [← hLsupport]; exact p.2
  change f (ef.symm ⟨p.1, hpRange⟩) = p.1
  exact congrArg Subtype.val (ef.apply_symm_apply ⟨p.1, hpRange⟩)

end CloseGraphApproximation

/-- Intrinsic-source form of Moise Ch. 6, Thm. 3.  A continuous embedding of a finite intrinsic
two-complex into the plane can be replaced by a finite pure plane triangulation whose coordinate
embedding is uniformly close to the original one. -/
theorem exists_intrinsic_pl_approximation (K : IntrinsicTwoComplex)
    {h : K.realization → Plane} (hcont : Continuous h) (hinj : Function.Injective h)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (L : PlaneComplex) (_hLpure : L.IsPure2) (e : L.support ≃ₜ K.realization),
      ∀ p : L.support, dist p.1 (h (e p)) < ε := by
  let η := ε / 3
  have hη : 0 < η := div_pos hε (by norm_num)
  obtain ⟨R, hsmall⟩ := K.exists_subdivision_image_dist_lt hcont hη
  let H : R.refined.realization → Plane := h ∘ R.homeo
  have hHcont : Continuous H := hcont.comp R.homeo.continuous
  have hHinj : Function.Injective H := hinj.comp R.homeo.injective
  obtain ⟨r, hr, hsep⟩ := R.refined.exists_uniform_vertex_face_separation hHcont hHinj
  obtain ⟨D⟩ := R.refined.exists_vertexDiskControl hHcont hHinj
  obtain ⟨C⟩ := R.refined.exists_centralTubeControl hHcont hHinj D
  let ρ := min r η
  have hρ : 0 < ρ := lt_min hr hη
  obtain ⟨A⟩ := R.refined.exists_closeGraphApproximation
    (hcont := hHcont) (hinj := hHinj) (D := D) (C := C) hρ
  have hcloseR : ∀ x ∈ R.refined.oneSkeleton,
      dist (A.intrinsicMap x) (H x) < r := by
    intro x hx
    exact (A.close x hx).trans_le (min_le_left r η)
  have hvertices : A.VerticesAvoidClosedRegions :=
    A.verticesAvoidClosedRegions_of_close hr hsep hcloseR
  obtain ⟨L, hLpure, e₀, he₀⟩ := A.exists_retriangulation hvertices
  let e : L.support ≃ₜ K.realization := e₀.trans R.homeo
  refine ⟨L, hLpure, e, ?_⟩
  intro p
  have hsmall' : ∀ t : R.refined.Face, ∀ x ∈ R.refined.faceCarrier t.1,
      ∀ y ∈ R.refined.faceCarrier t.1, dist (H x) (H y) < η := by
    intro t x hx y hy
    exact hsmall t.1 t.2 x hx y hy
  have hbound := A.closeCellwiseMap_dist_le hsmall' A.close (e₀ p)
  have hpMap : A.closeCellwiseMap (e₀ p) = p.1 := he₀ p
  have hρle : ρ ≤ η := min_le_right r η
  change dist p.1 (h (e p)) < ε
  rw [← hpMap]
  change dist (A.closeCellwiseMap (e₀ p)) (H (e₀ p)) < ε
  calc
    dist (A.closeCellwiseMap (e₀ p)) (H (e₀ p)) ≤ η + ρ := hbound
    _ ≤ η + η := add_le_add le_rfl hρle
    _ < ε := by dsimp [η]; linarith

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
