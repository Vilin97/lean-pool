/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFinitePLApproximation

/-!
# Side preservation for locally finite face fillings

The metric estimates of `LocallyFinitePLApproximation` put nonincident vertices outside each
replacement polygon.  This file propagates that information along every replacement edge.  The
argument is the same connected-side argument used in Moise Chapter 6: an edge can cross a
polygonal boundary only where the corresponding abstract edge meets the face.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-- The canonical boundary lift belongs to the face whose boundary it parametrizes. -/
theorem faceBoundaryLift_mem_faceInSupport (f : K.Face) (q : StandardFaceBoundary) :
    (K.faceBoundaryLift f q).1 ∈ faceInSupport (K := K) f := by
  exact Set.mem_range_self
    ((K.facePlaneHomeomorph f).symm
      ⟨q.1, standardFaceBoundary_mem_region q⟩)

/-- A replacement graph pointwise finer than the canonical vertex-separation control is
facewise close at the canonical per-face separation radii.  This is the bridge from a
tolerance-parametrized one-skeleton replacement to the side-preservation entry
`FaceBoundariesClose G (faceVertexSeparationRadius G)`. -/
theorem faceBoundariesClose_of_lt_vertexSeparationControl
    (harc : ∀ p : oneSkeletonInSupport (K := K),
      dist (G.graphReplacementMap p) (G.map p.1) < vertexSeparationControl G p.1) :
    FaceBoundariesClose G (faceVertexSeparationRadius G) := by
  intro f q
  have heq : faceOriginalMap G f q.1 = G.map (K.faceBoundaryLift f q).1 := by
    change faceOriginalMap G f
        (⟨q.1, standardFaceBoundary_mem_region q⟩ : standardFaceRegion).1 = _
    rw [faceOriginalMap_apply]
    rfl
  rw [heq]
  exact (harc (K.faceBoundaryLift f q)).trans_le
    (vertexSeparationControl_le (faceBoundaryLift_mem_faceInSupport f q))

/-- Every selected face boundary is part of the single global replacement graph. -/
theorem facePolygonalCircle_carrier_subset_graphReplacement (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).carrier ⊆
      Set.range G.graphReplacementMap := by
  intro y hy
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  exact ⟨K.faceBoundaryLift f q',
    (K.faceBoundaryMap_apply (G := G) f q').symm⟩

/-- If a replacement-graph point lies on one face polygon, its source lies in that face. -/
theorem mem_faceInSupport_of_graphReplacement_mem_facePolygonalCircle
    (f : K.Face) (p : oneSkeletonInSupport (K := K))
    (hp : G.graphReplacementMap p ∈
      (K.facePolygonalCircle (G := G) f).carrier) :
    p.1 ∈ faceInSupport (K := K) f := by
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hp
  obtain ⟨q, hq, hqmap⟩ := hp
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  have heq : G.graphReplacementMap p =
      G.graphReplacementMap (K.faceBoundaryLift f q') := by
    rw [← K.faceBoundaryMap_apply (G := G) f q']
    exact hqmap.symm
  have hpq := G.graphReplacementMap_injective heq
  rw [hpq]
  exact K.faceBoundaryLift_mem_faceInSupport f q'

/-- Include the interval parametrization of an edge in the source one-skeleton. -/
noncomputable def edgePathInOneSkeleton (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    oneSkeletonInSupport (K := K) :=
  ⟨edgePathInSupport (K := K) e r,
    Set.mem_iUnion.mpr ⟨e, by
      rw [← range_edgePathInSupport (K := K) e]
      exact Set.mem_range_self r⟩⟩

theorem continuous_edgePathInOneSkeleton (e : K.Edge) :
    Continuous (edgePathInOneSkeleton (K := K) e) := by
  apply Continuous.subtype_mk
  exact continuous_edgePathInSupport (K := K) e

@[simp] theorem edgePathInOneSkeleton_val (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    (edgePathInOneSkeleton (K := K) e r).1 = edgePathInSupport (K := K) e r := rfl

/-- An edge contained in a face has all its support points in that face. -/
theorem edgeInSupport_subset_faceInSupport (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) :
    edgeInSupport (K := K) e ⊆ faceInSupport (K := K) f := by
  rintro p ⟨q, rfl⟩
  obtain ⟨x, hx⟩ := q.2
  let y := stdSimplex.map
    (fun v : {v // v ∈ e.1} ↦
      (⟨v.1, hef v.2⟩ : {w // w ∈ K.faceVertices f})) x
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change K.faceMap f y = q.1
  exact (K.edgeMap_eq_faceMap e f hef x).symm.trans hx

/-- If the second endpoint of an edge is absent from a face, an edge-path point in that face
must have parameter zero. -/
theorem edgePathInSupport_parameter_eq_zero_of_mem_face
    (f : K.Face) (e : K.Edge) (r : Set.Icc (0 : ℝ) 1)
    (hsecond : K.edgeSecond e ∉ K.faceVertices f)
    (hr : edgePathInSupport (K := K) e r ∈ faceInSupport (K := K) f) :
    r.1 = 0 := by
  obtain ⟨y, hy⟩ := hr
  have hcoords := K.faceMap_eq_iff.mp (congrArg Subtype.val hy).symm
  have hc := congrFun hcoords (K.edgeSecond e)
  rw [K.extendFaceCoordinates_map_edgeVertexToFace e,
    extendFaceCoordinates_of_mem e.1 _ (K.edgeSecond_mem e),
    extendFaceCoordinates_of_notMem (K.faceVertices f) y hsecond,
    K.edgeSimplexPath_apply_second] at hc
  exact hc

/-- If the first endpoint of an edge is absent from a face, an edge-path point in that face must
have parameter one. -/
theorem edgePathInSupport_parameter_eq_one_of_mem_face
    (f : K.Face) (e : K.Edge) (r : Set.Icc (0 : ℝ) 1)
    (hfirst : K.edgeFirst e ∉ K.faceVertices f)
    (hr : edgePathInSupport (K := K) e r ∈ faceInSupport (K := K) f) :
    r.1 = 1 := by
  obtain ⟨y, hy⟩ := hr
  have hcoords := K.faceMap_eq_iff.mp (congrArg Subtype.val hy).symm
  have hc := congrFun hcoords (K.edgeFirst e)
  rw [K.extendFaceCoordinates_map_edgeVertexToFace e,
    extendFaceCoordinates_of_mem e.1 _ (K.edgeFirst_mem e),
    extendFaceCoordinates_of_notMem (K.faceVertices f) y hfirst,
    K.edgeSimplexPath_apply_first] at hc
  linarith

/-- The replacement of an abstract edge contained in a face lies on that face's polygon. -/
theorem graphReplacement_mem_facePolygonalCircle_of_edge_subset
    (f : K.Face) (e : K.Edge) (p : oneSkeletonInSupport (K := K))
    (hp : p.1 ∈ edgeInSupport (K := K) e)
    (hef : e.1 ⊆ K.faceVertices f) :
    G.graphReplacementMap p ∈
      (K.facePolygonalCircle (G := G) f).carrier := by
  obtain ⟨i, hi⟩ := K.exists_faceEdge_eq_of_subset f e hef
  rw [K.facePolygonalCircle_carrier (G := G) f]
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  have hp' : p.1 ∈ edgeInSupport (K := K) (K.faceEdge f i) := by
    simpa only [hi] using hp
  rw [G.graphReplacementMap_eq (K.faceEdge f i) p hp',
    ← G.range_replacementEdgeMap (K.faceEdge f i)]
  exact Set.mem_range_self
    (⟨p.1, hp'⟩ : edgeInSupport (K := K) (K.faceEdge f i))

/-- The simultaneous graph replacement fixes every abstract vertex. -/
theorem graphReplacementMap_vertex (v : K.Vertex) :
    ∃ p : oneSkeletonInSupport (K := K), p.1.1 = K.vertexPoint v ∧
      G.graphReplacementMap p = G.vertexImage v := by
  obtain ⟨f, hvf⟩ := K.vertex_used v
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem f hvf
  let e := K.faceEdge f i
  have hve : v ∈ e.1 := by
    rw [K.faceEdge_val, ← hi]
    simp
  let s : K.support := ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩
  have hse : s ∈ edgeInSupport (K := K) e := by
    rw [edgeInSupport_eq_preimage (K := K)]
    exact (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve
  let p : oneSkeletonInSupport (K := K) :=
    ⟨s, Set.mem_iUnion.mpr ⟨e, hse⟩⟩
  refine ⟨p, rfl, ?_⟩
  rw [G.graphReplacementMap_eq e p hse]
  exact G.replacementEdgeMap_vertex e v hve

/-- A vertex of a face maps to that face's replacement polygon. -/
theorem graphReplacement_vertex_mem_facePolygonalCircle
    (f : K.Face) (v : K.Vertex) (hvf : v ∈ K.faceVertices f) :
    G.vertexImage v ∈ (K.facePolygonalCircle (G := G) f).carrier := by
  obtain ⟨p, hpv, hpmap⟩ := graphReplacementMap_vertex (G := G) v
  rw [← hpmap]
  obtain ⟨i, hi⟩ := K.exists_faceVertex_eq_of_mem f hvf
  let e := K.faceEdge f i
  have hpe : p.1 ∈ edgeInSupport (K := K) e := by
    rw [edgeInSupport_eq_preimage (K := K)]
    change p.1.1 ∈ K.edgeCarrier e
    rw [hpv]
    apply (K.vertexPoint_mem_edgeCarrier_iff v e).mpr
    rw [K.faceEdge_val, ← hi]
    simp
  exact graphReplacement_mem_facePolygonalCircle_of_edge_subset (G := G) f e p hpe
    (K.faceEdge_subset_faceVertices f i)

theorem graphReplacementMap_edgePathInOneSkeleton_zero (e : K.Edge) :
    G.graphReplacementMap
        (edgePathInOneSkeleton (K := K) e ⟨0, by simp⟩) =
      G.vertexImage (K.edgeFirst e) := by
  obtain ⟨p, hp, hmap⟩ := graphReplacementMap_vertex (G := G) (K.edgeFirst e)
  rw [← hmap]
  apply congrArg G.graphReplacementMap
  apply Subtype.ext
  apply Subtype.ext
  exact (K.edgePath_zero e).trans hp.symm

theorem graphReplacementMap_edgePathInOneSkeleton_one (e : K.Edge) :
    G.graphReplacementMap
        (edgePathInOneSkeleton (K := K) e ⟨1, by simp⟩) =
      G.vertexImage (K.edgeSecond e) := by
  obtain ⟨p, hp, hmap⟩ := graphReplacementMap_vertex (G := G) (K.edgeSecond e)
  rw [← hmap]
  apply congrArg G.graphReplacementMap
  apply Subtype.ext
  apply Subtype.ext
  exact (K.edgePath_one e).trans hp.symm

/-- Graph-side compatibility required for coherent cellwise assembly. -/
def FaceFillingsGraphAvoidInteriors (G : K.PlaneGraphRealization) : Prop :=
  ∀ f : K.Face,
    Disjoint (Set.range G.graphReplacementMap)
      (K.facePolygonalCircle (G := G) f).interiorRegion

/-- Facewise closeness and vertex-to-face separation put every nonincident vertex on the
unbounded side of the replacement polygon.  This is the locally finite form of Moise's actual
Chapter 6 argument: bounded Tietze extension fills the close boundary while avoiding the outside
vertex, and no-retraction detects the unbounded side. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_close
    {r : K.Face → ℝ} (hr : ∀ f, 0 < r f)
    (hsep : FaceVertexThickeningsSeparated G r)
    (hclose : FaceBoundariesClose G r) :
    FaceFillingsVerticesAvoidClosedRegions G := by
  intro f v hvf
  let b := K.faceBoundaryMap (G := G) f
  let hface := faceOriginalMap G f
  have hbcont : ContinuousOn b (frontier standardFaceRegion) :=
    K.continuousOn_faceBoundaryMap (G := G) f
  have hhface : ContinuousOn hface standardFaceRegion :=
    continuousOn_faceOriginalMap (G := G) f
  have hbclose : ∀ p ∈ frontier standardFaceRegion,
      dist (b p) (hface p) < r f := by
    intro p hp
    let q : StandardFaceBoundary := ⟨p, hp⟩
    change dist (K.faceBoundaryMap (G := G) f p)
      (faceOriginalMap G f p) < r f
    rw [K.faceBoundaryMap_apply (G := G) f q]
    exact hclose f q
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      standardTrianglePlaneComplex.isCompact_support.isClosed (hr f)
      hbcont hhface hbclose
  have hvAvoid : G.vertexImage v ∉ F '' standardFaceRegion := by
    rintro ⟨p, hp, hFp⟩
    have hvBall : G.vertexImage v ∈
        Metric.closedBall (G.vertexImage v) (r f) :=
      Metric.mem_closedBall_self (hr f).le
    have hFthick : F p ∈
        Metric.cthickening (r f) (G.map '' faceInSupport (K := K) f) := by
      apply Metric.mem_cthickening_of_dist_le (F p) (hface p) (r f)
        (G.map '' faceInSupport (K := K) f)
      · exact faceOriginalMap_mem_face_image (G := G) f ⟨p, hp⟩
      · exact hFclose p hp
    exact Set.disjoint_left.mp (hsep f v hvf) hvBall (hFp ▸ hFthick)
  have hvExterior : G.vertexImage v ∈
      (K.facePolygonalCircle (G := G) f).exteriorRegion := by
    apply (K.facePolygonalCircle (G := G) f).mem_exteriorRegion_of_continuous_extension
      standardTrianglePlaneComplex_isTriangle hbcont
      (K.faceBoundaryMap_injectiveOn (G := G) f)
      (K.faceBoundaryMap_image_polygon (G := G) f)
      hFcont hFeq hvAvoid
  intro hvClosed
  exact Set.disjoint_left.mp
    (K.facePolygonalCircle (G := G) f).disjoint_closedRegion_exteriorRegion
      hvClosed hvExterior

/-- Parametrization-independent form of `faceFillingsVerticesAvoidClosedRegions_of_close`: the
comparison map on the standard region may be ANY continuous map whose values stay within half
the separation radius of the original face image, and which is within half that radius of the
replacement boundary on the frontier.  This absorbs the parameter misalignment between the
replacement arcs' `Path.trans` splits and the original edge trims: an aligned comparison built
from `CentralPolygonalArc.curve_close` can discharge the closeness at the approximation-control
scale, which the crude same-parameter comparison with `faceOriginalMap` cannot. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_comparison
    {r : K.Face → ℝ} (hr : ∀ f, 0 < r f)
    (hsep : FaceVertexThickeningsSeparated G r)
    (comp : K.Face → Plane → Plane)
    (hcompCont : ∀ f, ContinuousOn (comp f) standardFaceRegion)
    (hcompMem : ∀ (f : K.Face), ∀ p ∈ standardFaceRegion,
      comp f p ∈ Metric.cthickening (r f / 2) (G.map '' faceInSupport (K := K) f))
    (hclose : ∀ (f : K.Face) (q : StandardFaceBoundary),
      dist (G.graphReplacementMap (K.faceBoundaryLift f q)) (comp f q.1) < r f / 2) :
    FaceFillingsVerticesAvoidClosedRegions G := by
  intro f v hvf
  let b := K.faceBoundaryMap (G := G) f
  have hbcont : ContinuousOn b (frontier standardFaceRegion) :=
    K.continuousOn_faceBoundaryMap (G := G) f
  have hbclose : ∀ p ∈ frontier standardFaceRegion,
      dist (b p) (comp f p) < r f / 2 := by
    intro p hp
    let q : StandardFaceBoundary := ⟨p, hp⟩
    change dist (K.faceBoundaryMap (G := G) f p) (comp f p) < r f / 2
    rw [K.faceBoundaryMap_apply (G := G) f q]
    exact hclose f q
  obtain ⟨F, hFcont, hFeq, hFclose⟩ :=
    exists_continuous_extension_of_close_on_frontier
      standardTrianglePlaneComplex.isCompact_support.isClosed (half_pos (hr f))
      hbcont (hcompCont f) hbclose
  have hvAvoid : G.vertexImage v ∉ F '' standardFaceRegion := by
    rintro ⟨p, hp, hFp⟩
    have hvBall : G.vertexImage v ∈
        Metric.closedBall (G.vertexImage v) (r f) :=
      Metric.mem_closedBall_self (hr f).le
    have hFhalf : F p ∈ Metric.cthickening (r f / 2)
        (Metric.cthickening (r f / 2) (G.map '' faceInSupport (K := K) f)) :=
      Metric.mem_cthickening_of_dist_le (F p) (comp f p) (r f / 2) _
        (hcompMem f p hp) (hFclose p hp)
    have hFthick : F p ∈
        Metric.cthickening (r f) (G.map '' faceInSupport (K := K) f) := by
      have hmem := Metric.cthickening_cthickening_subset
        (half_pos (hr f)).le (half_pos (hr f)).le
        (G.map '' faceInSupport (K := K) f) hFhalf
      rwa [add_halves] at hmem
    exact Set.disjoint_left.mp (hsep f v hvf) hvBall (hFp ▸ hFthick)
  have hvExterior : G.vertexImage v ∈
      (K.facePolygonalCircle (G := G) f).exteriorRegion := by
    apply (K.facePolygonalCircle (G := G) f).mem_exteriorRegion_of_continuous_extension
      standardTrianglePlaneComplex_isTriangle hbcont
      (K.faceBoundaryMap_injectiveOn (G := G) f)
      (K.faceBoundaryMap_image_polygon (G := G) f)
      hFcont hFeq hvAvoid
  intro hvClosed
  exact Set.disjoint_left.mp
    (K.facePolygonalCircle (G := G) f).disjoint_closedRegion_exteriorRegion
      hvClosed hvExterior

/-- A nonincident vertex outside the polygonal closed disk lies in its unbounded component. -/
theorem graphReplacement_vertex_mem_exterior
    (hvertices : FaceFillingsVerticesAvoidClosedRegions G)
    (f : K.Face) (v : K.Vertex) (hvf : v ∉ K.faceVertices f) :
    G.vertexImage v ∈
      (K.facePolygonalCircle (G := G) f).exteriorRegion := by
  let J := K.facePolygonalCircle (G := G) f
  have hnotClosed := hvertices f v hvf
  have hnotInterior : G.vertexImage v ∉ J.interiorRegion := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inl hv
  have hnotCarrier : G.vertexImage v ∉ J.carrier := by
    intro hv
    apply hnotClosed
    rw [J.closedRegion_eq_union]
    exact Or.inr hv
  have hoff : G.vertexImage v ∈ J.carrierᶜ := hnotCarrier
  rw [← J.interior_union_exterior] at hoff
  exact hoff.resolve_left hnotInterior

/-- Moise's vertex-side condition propagates along every edge: the complete simultaneous
replacement graph avoids the bounded interior selected for each face. -/
theorem faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (hvertices : FaceFillingsVerticesAvoidClosedRegions G) :
    FaceFillingsGraphAvoidInteriors G := by
  intro f
  let J := K.facePolygonalCircle (G := G) f
  have hinteriorCarrier : Disjoint J.interiorRegion J.carrier := by
    rw [← J.interior_closedRegion, ← J.frontier_closedRegion]
    exact disjoint_interior_frontier
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩ hpInterior
  obtain ⟨e, hpe⟩ := Set.mem_iUnion.mp p.2
  by_cases hef : e.1 ⊆ K.faceVertices f
  · have hpCarrier := graphReplacement_mem_facePolygonalCircle_of_edge_subset
      (G := G) f e p hpe hef
    exact Set.disjoint_left.mp hinteriorCarrier hpInterior hpCarrier
  let I := Set.Icc (0 : ℝ) 1
  let z0 : I := ⟨0, by simp [I]⟩
  let z1 : I := ⟨1, by simp [I]⟩
  let gpath : I → Plane := fun r ↦
    G.graphReplacementMap (edgePathInOneSkeleton (K := K) e r)
  have hgpath : Continuous gpath := by
    exact G.continuous_graphReplacementMap.comp
      (continuous_edgePathInOneSkeleton (K := K) e)
  have hoffCarrier {A : Set I}
      (houtside : ∀ r ∈ A,
        edgePathInSupport (K := K) e r ∉ faceInSupport (K := K) f) :
      Set.MapsTo gpath A J.carrierᶜ := by
    intro r hr hcarrier
    exact houtside r hr
      (mem_faceInSupport_of_graphReplacement_mem_facePolygonalCircle
        (G := G) f (edgePathInOneSkeleton (K := K) e r) hcarrier)
  let r : I := (G.edgePathInSupportHomeomorph e).symm ⟨p.1, hpe⟩
  have hrPath : edgePathInSupport (K := K) e r = p.1 := by
    exact congrArg Subtype.val
      ((G.edgePathInSupportHomeomorph e).apply_symm_apply ⟨p.1, hpe⟩)
  have hpPath : edgePathInOneSkeleton (K := K) e r = p := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val hrPath
  have hmapPath : gpath r = G.graphReplacementMap p := congrArg G.graphReplacementMap hpPath
  by_cases hfirst : K.edgeFirst e ∈ K.faceVertices f
  · have hsecond : K.edgeSecond e ∉ K.faceVertices f := by
      intro hsecond
      apply hef
      rw [K.edge_eq_pair e]
      exact Finset.insert_subset_iff.mpr
        ⟨hfirst, Finset.singleton_subset_iff.mpr hsecond⟩
    by_cases hr0 : r.1 = 0
    · have hrz : r = z0 := Subtype.ext hr0
      have hpCarrier : G.graphReplacementMap p ∈ J.carrier := by
        rw [← hmapPath, hrz]
        simpa only [gpath, z0, J,
          graphReplacementMap_edgePathInOneSkeleton_zero] using
            graphReplacement_vertex_mem_facePolygonalCircle
              (G := G) f (K.edgeFirst e) hfirst
      exact Set.disjoint_left.mp hinteriorCarrier hpInterior hpCarrier
    · let A : Set I := Set.Ioc z0 z1
      have hAoutside : ∀ s ∈ A,
          edgePathInSupport (K := K) e s ∉ faceInSupport (K := K) f := by
        intro s hs hsFace
        have hs0 := edgePathInSupport_parameter_eq_zero_of_mem_face
          f e s hsecond hsFace
        exact (ne_of_gt (show (0 : ℝ) < s.1 by exact_mod_cast hs.1)) hs0
      have hz1Exterior : gpath z1 ∈ J.exteriorRegion := by
        simpa only [gpath, z1, J,
          graphReplacementMap_edgePathInOneSkeleton_one] using
          graphReplacement_vertex_mem_exterior (G := G) hvertices f
            (K.edgeSecond e) hsecond
      have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_Ioc
          hgpath.continuousOn (hoffCarrier hAoutside)
          ⟨z1, by simp [A, z0, z1], hz1Exterior⟩
      have hrA : r ∈ A := by
        constructor
        · change (0 : ℝ) < r.1
          exact lt_of_le_of_ne r.2.1 (Ne.symm hr0)
        · exact r.2.2
      have hrExterior := hAExterior hrA
      rw [hmapPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hpInterior hrExterior
  · by_cases hsecond : K.edgeSecond e ∈ K.faceVertices f
    · by_cases hr1 : r.1 = 1
      · have hrz : r = z1 := Subtype.ext hr1
        have hpCarrier : G.graphReplacementMap p ∈ J.carrier := by
          rw [← hmapPath, hrz]
          simpa only [gpath, z1, J,
            graphReplacementMap_edgePathInOneSkeleton_one] using
              graphReplacement_vertex_mem_facePolygonalCircle
                (G := G) f (K.edgeSecond e) hsecond
        exact Set.disjoint_left.mp hinteriorCarrier hpInterior hpCarrier
      · let A : Set I := Set.Ico z0 z1
        have hAoutside : ∀ s ∈ A,
            edgePathInSupport (K := K) e s ∉ faceInSupport (K := K) f := by
          intro s hs hsFace
          have hs1 := edgePathInSupport_parameter_eq_one_of_mem_face
            f e s hfirst hsFace
          exact (ne_of_lt (show s.1 < (1 : ℝ) by exact_mod_cast hs.2)) hs1
        have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
          simpa only [gpath, z0, J,
            graphReplacementMap_edgePathInOneSkeleton_zero] using
            graphReplacement_vertex_mem_exterior (G := G) hvertices f
              (K.edgeFirst e) hfirst
        have hAExterior : Set.MapsTo gpath A J.exteriorRegion :=
          J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_Ico
            hgpath.continuousOn (hoffCarrier hAoutside)
            ⟨z0, by simp [A, z0, z1], hz0Exterior⟩
        have hrA : r ∈ A := by
          constructor
          · exact r.2.1
          · change r.1 < (1 : ℝ)
            exact lt_of_le_of_ne r.2.2 hr1
        have hrExterior := hAExterior hrA
        rw [hmapPath] at hrExterior
        exact Set.disjoint_left.mp J.disjoint_interior_exterior hpInterior hrExterior
    · have hAllOutside : ∀ s : I,
          edgePathInSupport (K := K) e s ∉ faceInSupport (K := K) f := by
        intro s hsFace
        have hs0 := edgePathInSupport_parameter_eq_zero_of_mem_face
          f e s hsecond hsFace
        have hs1 := edgePathInSupport_parameter_eq_one_of_mem_face
          f e s hfirst hsFace
        linarith
      have hz0Exterior : gpath z0 ∈ J.exteriorRegion := by
        simpa only [gpath, z0, J,
          graphReplacementMap_edgePathInOneSkeleton_zero] using
          graphReplacement_vertex_mem_exterior (G := G) hvertices f
            (K.edgeFirst e) hfirst
      have hAllExterior : Set.MapsTo gpath Set.univ J.exteriorRegion :=
        J.mapsTo_exteriorRegion_of_isPreconnected isPreconnected_univ
          hgpath.continuousOn (hoffCarrier fun s _ ↦ hAllOutside s)
          ⟨z0, Set.mem_univ _, hz0Exterior⟩
      have hrExterior := hAllExterior (Set.mem_univ r)
      rw [hmapPath] at hrExterior
      exact Set.disjoint_left.mp J.disjoint_interior_exterior hpInterior hrExterior

/-- Once the replacement graph stays out of every selected bounded component, distinct filled
face interiors are disjoint.  A vertex of the second face not belonging to the first supplies the
strict side witness required by polygonal Jordan separation. -/
theorem disjoint_facePolygonalCircle_interiors
    (hfaces : Function.Injective K.faceVertices)
    (hside : FaceFillingsGraphAvoidInteriors G)
    (f g : K.Face) (hfg : f ≠ g) :
    Disjoint
      (K.facePolygonalCircle (G := G) f).interiorRegion
      (K.facePolygonalCircle (G := G) g).interiorRegion := by
  classical
  have hnotSubset : ¬K.faceVertices g ⊆ K.faceVertices f := by
    intro hsub
    have heq : K.faceVertices g = K.faceVertices f :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [K.faceVertices_card g, K.faceVertices_card f])
    exact hfg (hfaces heq.symm)
  obtain ⟨w, hwg, hwnf⟩ := Finset.not_subset.mp hnotSubset
  have hwCarrierG : G.vertexImage w ∈
      (K.facePolygonalCircle (G := G) g).carrier :=
    graphReplacement_vertex_mem_facePolygonalCircle (G := G) g w hwg
  have hwNotCarrierF : G.vertexImage w ∉
      (K.facePolygonalCircle (G := G) f).carrier := by
    intro hwCarrierF
    obtain ⟨p, hpw, hpmap⟩ := graphReplacementMap_vertex (G := G) w
    have hpFace : p.1 ∈ faceInSupport (K := K) f :=
      mem_faceInSupport_of_graphReplacement_mem_facePolygonalCircle
        (G := G) f p (by simpa only [hpmap] using hwCarrierF)
    rw [K.faceInSupport_eq_preimage] at hpFace
    change p.1.1 ∈ K.faceCarrier f at hpFace
    have hwFace : K.vertexPoint w ∈ K.faceCarrier f := by
      rw [hpw] at hpFace
      exact hpFace
    exact hwnf ((K.vertexPoint_mem_faceCarrier_iff f w).mp hwFace)
  apply (K.facePolygonalCircle (G := G) f).disjoint_interiorRegion_of_boundary_avoidance
    (K.facePolygonalCircle (G := G) g)
  · exact (hside g).mono_left
      (K.facePolygonalCircle_carrier_subset_graphReplacement (G := G) f)
  · exact (hside f).mono_left
      (K.facePolygonalCircle_carrier_subset_graphReplacement (G := G) g)
  · exact ⟨G.vertexImage w, hwCarrierG, hwNotCarrierF⟩

/-- The quantitative Chapter 6 hypotheses, together with local finiteness of the selected closed
polygonal disks, produce the complete compatibility package needed for cellwise assembly. -/
theorem cellwiseCompatibility_of_control
    (hfaces : Function.Injective K.faceVertices)
    {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hsep : SeparatesVerticesFromFaces G phi)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  have hvertices := faceFillingsVerticesAvoidClosedRegions_of_control
    (G := G) hcontrol hsep
  have hside := faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (G := G) hvertices
  exact
    { faceVertices_injective := hfaces
      graphAvoidsInteriors := hside
      interiorsDisjoint := disjoint_facePolygonalCircle_interiors
        (G := G) hfaces hside
      closedRegions_mem_region := hregion
      locallyFiniteClosedRegions := hloc }

/-- Moise's original side-control interface: facewise graph closeness below the canonical
vertex-to-face separation radius gives the compatibility package for all Schoenflies fillings.
Unlike `cellwiseCompatibility_of_control`, this formulation does not force one pointwise
tolerance to serve every face incident to a source point. -/
theorem cellwiseCompatibility_of_facewise_close
    (hfaces : Function.Injective K.faceVertices)
    (hclose : FaceBoundariesClose G (faceVertexSeparationRadius G))
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  have hvertices := faceFillingsVerticesAvoidClosedRegions_of_close
    (G := G) (faceVertexSeparationRadius_pos (G := G))
      (faceVertexSeparationRadius_separates (G := G)) hclose
  have hside := faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (G := G) hvertices
  exact
    { faceVertices_injective := hfaces
      graphAvoidsInteriors := hside
      interiorsDisjoint := disjoint_facePolygonalCircle_interiors
        (G := G) hfaces hside
      closedRegions_mem_region := hregion
      locallyFiniteClosedRegions := hloc }

/-- The compatibility package from a parametrization-independent comparison map at the
canonical separation radii.  This is the entry matched to the locally finite replacement arcs:
their `curve_close` tracking is stated against the trimmed original curve, not against the
`Path.trans` parameter, so only a reparametrized comparison can be discharged at the
approximation-control scale. -/
theorem cellwiseCompatibility_of_comparison
    (hfaces : Function.Injective K.faceVertices)
    (comp : K.Face → Plane → Plane)
    (hcompCont : ∀ f, ContinuousOn (comp f) standardFaceRegion)
    (hcompMem : ∀ (f : K.Face), ∀ p ∈ standardFaceRegion,
      comp f p ∈ Metric.cthickening (faceVertexSeparationRadius G f / 2)
        (G.map '' faceInSupport (K := K) f))
    (hclose : ∀ (f : K.Face) (q : StandardFaceBoundary),
      dist (G.graphReplacementMap (K.faceBoundaryLift f q)) (comp f q.1) <
        faceVertexSeparationRadius G f / 2)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  have hvertices := faceFillingsVerticesAvoidClosedRegions_of_comparison
    (G := G) (faceVertexSeparationRadius_pos (G := G))
      (faceVertexSeparationRadius_separates (G := G)) comp hcompCont hcompMem hclose
  have hside := faceFillingsGraphAvoidInteriors_of_verticesAvoid
    (G := G) hvertices
  exact
    { faceVertices_injective := hfaces
      graphAvoidsInteriors := hside
      interiorsDisjoint := disjoint_facePolygonalCircle_interiors
        (G := G) hfaces hside
      closedRegions_mem_region := hregion
      locallyFiniteClosedRegions := hloc }

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
