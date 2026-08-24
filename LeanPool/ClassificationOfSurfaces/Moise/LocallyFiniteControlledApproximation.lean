/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.HalfPlanePolygon
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteSidePreservation

/-!
# Controlled locally finite PL replacement

This file packages the completed cellwise part of Moise Chapter 6, Theorem 3.  The graph-level
construction supplies quantitative face control and separation.  Polygonal Schoenflies then
fills every face, and local finiteness glues the fillings into a homeomorphism of supports.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] [T2Space S]
variable {K : LocallyFiniteTriangleComplex S}

/-- The closed metric controls used for a replacement are contained in the permitted open
region. -/
def PlaneGraphRealization.ControlsStayInRegion (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  ∀ p, Metric.closedBall (G.map p) (phi p) ⊆ G.region

/-- A global bound and a frontier-relative bound sufficient to control a locally finite
family of polygonal face fillings. -/
def PlaneGraphRealization.UniformFrontierControl (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  (∀ p, phi p ≤ 1) ∧
    ∀ (_ : G.regionᶜ.Nonempty) (p : K.support),
      phi p ≤ Metric.infDist (G.map p) G.regionᶜ / 4

omit [T2Space S] in
/-- Frontier control keeps each selected polygonal disk inside the permitted open region. -/
theorem closedRegions_mem_region_of_uniformFrontierControl
    (G : K.PlaneGraphRealization) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi) (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region := by
  by_cases hcomp : G.regionᶜ.Nonempty
  · obtain ⟨z, hz⟩ := K.faceCarrier_nonempty f
    obtain ⟨x, rfl⟩ := hz
    let p : K.support := faceToSupport (K := K) f x
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self x
    have hball := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp
    intro q hq
    have hdist : dist (G.map p) q ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hball hq
    have hinfPos : 0 < Metric.infDist (G.map p) G.regionᶜ := by
      exact (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
        (by simpa only [Set.mem_compl_iff, not_not] using G.map_mem_region p)
    have hlt : dist (G.map p) q < Metric.infDist (G.map p) G.regionᶜ := by
      calc
        dist (G.map p) q ≤ phi p := hdist
        _ ≤ Metric.infDist (G.map p) G.regionᶜ / 4 := hfrontier.2 hcomp p
        _ < Metric.infDist (G.map p) G.regionᶜ := by linarith
    have hnot := Metric.notMem_of_dist_lt_infDist hlt
    simpa only [Set.mem_compl_iff, not_not] using hnot
  · have hregion : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      exact hcomp ⟨q, hq⟩
    rw [hregion]
    exact Set.subset_univ _

omit [T2Space S] in
/-- The filled polygonal disks of a uniformly frontier-controlled replacement are locally
finite in the open perturbation region.  The proof confines any disk meeting a small ball to
an original face meeting a fixed compact ball, then uses relative closed-embedding transport. -/
theorem locallyFinite_closedRegions_of_uniformFrontierControl
    (G : K.PlaneGraphRealization) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi) :
    LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion} := by
  intro x
  by_cases hcomp : G.regionᶜ.Nonempty
  · let d := Metric.infDist x.1 G.regionᶜ
    have hd : 0 < d := by
      apply (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
      show x.1 ∉ G.regionᶜ
      simpa only [Set.mem_compl_iff, not_not] using x.2
    let U : Set G.region := {q | q.1 ∈ Metric.ball x.1 (d / 8)}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (div_pos hd (by norm_num))), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 (d / 2)
    have hCV : C ⊆ G.region := by
      intro q hq
      by_contra hqRegion
      have hinf := Metric.infDist_le_dist_of_mem (x := x.1)
        (show q ∈ G.regionᶜ from hqRegion)
      have hdist : dist x.1 q ≤ d / 2 := by
        simpa only [C, Metric.mem_closedBall, dist_comm] using hq
      dsimp only [d] at hd hinf hdist
      linarith
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_faceImagesInRegion.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro f hf
    obtain ⟨z, hzClosed, hzU⟩ := hf
    obtain ⟨w, hw⟩ := K.faceCarrier_nonempty f
    obtain ⟨y, rfl⟩ := hw
    let p : K.support := faceToSupport (K := K) f y
    let c : G.region := ⟨G.map p, G.map_mem_region p⟩
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self y
    have hzBall := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp hzClosed
    have hcenterZ : dist (G.map p) z.1 ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hzBall
    have hzX : dist z.1 x.1 < d / 8 := Metric.mem_ball.mp hzU
    have hinf : Metric.infDist (G.map p) G.regionᶜ ≤
        d + dist (G.map p) x.1 :=
      Metric.infDist_le_infDist_add_dist
    have hmain : dist (G.map p) x.1 <
        (d + dist (G.map p) x.1) / 4 + d / 8 := calc
      dist (G.map p) x.1 ≤ dist (G.map p) z.1 + dist z.1 x.1 :=
        dist_triangle _ _ _
      _ < phi p + d / 8 := add_lt_add_of_le_of_lt hcenterZ hzX
      _ ≤ (d + dist (G.map p) x.1) / 4 + d / 8 := by
        gcongr
        exact (hfrontier.2 hcomp p).trans
          (div_le_div_of_nonneg_right hinf (by norm_num))
    have hpCenter : dist (G.map p) x.1 ≤ d / 2 := by linarith
    refine ⟨c, ?_, ?_⟩
    · exact ⟨p, hp, rfl⟩
    · exact hpCenter
  · have hregion : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      exact hcomp ⟨q, hq⟩
    let U : Set G.region := {q | q.1 ∈ Metric.ball x.1 1}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (by norm_num)), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 2
    have hCV : C ⊆ G.region := by rw [hregion]; exact Set.subset_univ _
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_faceImagesInRegion.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro f hf
    obtain ⟨z, hzClosed, hzU⟩ := hf
    obtain ⟨w, hw⟩ := K.faceCarrier_nonempty f
    obtain ⟨y, rfl⟩ := hw
    let p : K.support := faceToSupport (K := K) f y
    let c : G.region := ⟨G.map p, G.map_mem_region p⟩
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self y
    have hzBall := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp hzClosed
    have hcenterZ : dist (G.map p) z.1 ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hzBall
    have hzX : dist z.1 x.1 < 1 := Metric.mem_ball.mp hzU
    have hpCenter : dist (G.map p) x.1 ≤ 2 := by
      apply le_of_lt
      calc
        dist (G.map p) x.1 ≤ dist (G.map p) z.1 + dist z.1 x.1 :=
          dist_triangle _ _ _
        _ < phi p + 1 := add_lt_add_of_le_of_lt hcenterZ hzX
        _ ≤ 2 := by linarith [hfrontier.1 p]
    refine ⟨c, ?_, ?_⟩
    · exact ⟨p, hp, rfl⟩
    · exact hpCenter

omit [T2Space S] in
/-- Convex target regions are preserved by the simultaneous polygonal replacement of the
one-skeleton.  The construction chooses each central broken line in the convex hull of its
original embedded edge. -/
theorem range_graphReplacementMap_subset_of_convex
    (G : K.PlaneGraphRealization) {C : Set Plane} (hC : Convex ℝ C)
    (hmap : Set.range G.map ⊆ C) :
    Set.range G.graphReplacementMap ⊆ C := by
  rw [G.range_graphReplacementMap]
  intro y hy
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hy
  apply convexHull_min _ hC <|
    (G.replacementArc e).completeCarrier_subset_edgeConvexHull hye
  rintro z ⟨p, -, rfl⟩
  exact hmap (Set.mem_range_self p)

omit [T2Space S] in
/-- A source realization in the model half-plane has a replacement graph in that half-plane. -/
theorem range_graphReplacementMap_subset_halfPlane
    (G : K.PlaneGraphRealization) (hmap : Set.range G.map ⊆ HalfPlaneSet) :
    Set.range G.graphReplacementMap ⊆ HalfPlaneSet :=
  range_graphReplacementMap_subset_of_convex G convex_halfPlaneSet hmap

omit [T2Space S] in
/-- A zero-normal point of a complete replacement arc is supported by zero-normal points of the
old embedded edge.  This is the exact supporting-face statement behind boundary preservation;
mere half-plane containment would only give one implication. -/
theorem PlaneGraphRealization.CentralPolygonalArc.mem_convexHull_edgeImage_coordZero
    (G : K.PlaneGraphRealization) {e : K.Edge}
    (A : G.CentralPolygonalArc e)
    (hmap : G.edgeImage e ⊆ HalfPlaneSet)
    {x : Plane} (hx : x ∈ A.completeCarrier) (hxZero : x 0 = 0) :
    x ∈ convexHull ℝ (G.edgeImage e ∩ {p | p 0 = 0}) := by
  have hnonneg : ∀ p ∈ G.edgeImage e, 0 ≤ cartesianX p := by
    intro p hp
    exact hmap hp
  change x ∈ convexHull ℝ (G.edgeImage e ∩ {p | cartesianX p = 0})
  rw [← convexHull_inter_affine_zero_of_nonneg_set
    (G.edgeImage e) cartesianX hnonneg]
  exact ⟨A.completeCarrier_subset_edgeConvexHull hx, hxZero⟩

omit [T2Space S] in
/-- On the source one-skeleton, the assembled cellwise replacement is exactly the previously
constructed global graph replacement. -/
theorem polygonalReplacementMap_eq_graphReplacementMap
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (p : oneSkeletonInSupport (K := K)) :
    (K.polygonalReplacementMap H p.1).1.1 = G.graphReplacementMap p := by
  let e : K.Edge := containingEdge (K := K) p
  let f : K.Face := K.edgeFace e
  have hpe : p.1 ∈ edgeInSupport (K := K) e :=
    mem_edgeInSupport_containingEdge (K := K) p
  have hef : e.1 ⊆ K.faceVertices f := K.edge_subset_faceVertices e
  have hpf : p.1 ∈ faceInSupport (K := K) f :=
    edgeInSupport_subset_faceInSupport (K := K) f e hef hpe
  obtain ⟨x, hx⟩ := hpf
  have hpPolygon :
      G.graphReplacementMap p ∈
        (K.facePolygonalCircle (G := G) f).carrier :=
    graphReplacement_mem_facePolygonalCircle_of_edge_subset
      (G := G) f e p hpe hef
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hpPolygon
  obtain ⟨z, hzFrontier, hzMap⟩ := hpPolygon
  let zBoundary : StandardFaceBoundary := ⟨z, hzFrontier⟩
  have hgraph :
      G.graphReplacementMap p =
        G.graphReplacementMap (K.faceBoundaryLift f zBoundary) := by
    rw [← K.faceBoundaryMap_apply (G := G) f zBoundary]
    exact hzMap.symm
  have hpLift : p = K.faceBoundaryLift f zBoundary :=
    G.graphReplacementMap_injective hgraph
  let zFace : K.ClosedFace f :=
    (K.facePlaneHomeomorph f).symm
      ⟨z, standardFaceBoundary_mem_region zBoundary⟩
  have hsource : x = zFace := by
    apply K.faceMap_injective f
    have hzSupport :
        faceToSupport (K := K) f zFace =
          (K.faceBoundaryLift f zBoundary).1 := rfl
    exact congrArg Subtype.val
      (hx.trans ((congrArg Subtype.val hpLift).trans hzSupport.symm))
  have hglobal :=
    K.polygonalReplacementMap_faceToSupport H f x
  rw [hx] at hglobal
  have hplane := congrArg (fun q => q.1.1) hglobal
  have hplane' :
      (K.polygonalReplacementMap H p.1).1.1 =
        (K.facePLFilling (G := G) f).faceMap x := by
    exact hplane
  rw [hplane', hsource]
  change
    (K.facePLFilling (G := G) f).map
        (K.facePlaneHomeomorph f zFace).1 =
      G.graphReplacementMap p
  have hzFace : (K.facePlaneHomeomorph f zFace).1 = z := by
    change
      (K.facePlaneHomeomorph f
        ((K.facePlaneHomeomorph f).symm
          ⟨z, standardFaceBoundary_mem_region zBoundary⟩)).1 = z
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]
  rw [hzFace]
  rw [(K.facePLFilling (G := G) f).eqOn_boundary hzFrontier]
  exact hzMap

/-- The source zero-normal locus already lies in the source one-skeleton. -/
def PlaneGraphRealization.SourceCoordZeroCarriedByOneSkeleton
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ p : K.support, G.map p 0 = 0 →
    p ∈ oneSkeletonInSupport (K := K)

/-- On every source triangle, the supporting-line locus is an exposed face with at most two
vertices.  This is the intrinsic condition which excludes a boundary chord: the zero locus in
a triangle is either empty, a vertex, or an entire edge. -/
def PlaneGraphRealization.FacewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ f : K.Face, ∃ b : Finset K.Vertex,
    b ⊆ K.faceVertices f ∧ b.card ≤ 2 ∧
      ∀ x : K.ClosedFace f,
        G.map (faceToSupport (K := K) f x) 0 = 0 ↔
          ∀ v : {v // v ∈ K.faceVertices f}, v.1 ∉ b → x v = 0

omit [T2Space S] in
/-- A facewise exposed zero locus is necessarily carried by the source one-skeleton. -/
theorem sourceCoordZeroCarriedByOneSkeleton_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) (hface : G.FacewiseCoordZeroExposed) :
    G.SourceCoordZeroCarriedByOneSkeleton := by
  classical
  intro p hpZero
  let f : K.Face := K.supportFace p
  let x : K.ClosedFace f := K.supportFacePoint p
  obtain ⟨b, hbf, hbcard, hb⟩ := hface f
  have hfacePoint :
      faceToSupport (K := K) f x = p := by
    apply Subtype.ext
    exact K.faceMap_supportFacePoint p
  have hxSupported : ∀ v : {v // v ∈ K.faceVertices f},
      v.1 ∉ b → x v = 0 := by
    apply (hb x).mp
    rw [hfacePoint]
    exact hpZero
  have htwo : 2 ≤ (K.faceVertices f).card := by
    rw [K.faceVertices_card f]
    omega
  obtain ⟨e, hbe, hef, hecard⟩ :=
    Finset.exists_subsuperset_card_eq hbf hbcard htwo
  let E : K.Edge := ⟨e, hecard, f, hef⟩
  have hxE : ∀ v : {v // v ∈ K.faceVertices f},
      v.1 ∉ E.1 → x v = 0 := by
    intro v hv
    exact hxSupported v fun hvb ↦ hv (hbe hvb)
  have hpEdge : p.1 ∈ K.edgeCarrier E := by
    rw [← congrArg Subtype.val hfacePoint]
    exact K.faceMap_mem_edgeCarrier_of_supportedOnEdge f E hef x hxE
  apply Set.mem_iUnion.mpr
  refine ⟨E, ?_⟩
  rw [edgeInSupport_eq_preimage (K := K)]
  exact hpEdge

/-- The graph replacement preserves the zero-normal locus pointwise on its source graph. -/
def PlaneGraphRealization.GraphReplacementPreservesCoordZero
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ p : oneSkeletonInSupport (K := K),
    G.graphReplacementMap p 0 = 0 ↔ G.map p.1 0 = 0

/-- The exact edgewise alternatives needed at a supporting boundary line.  On each old edge,
the zero-normal locus is either the whole image, one incident vertex, or empty.  In particular,
this rules out an interior edge whose two endpoints lie on the model boundary while its interior
does not: an arbitrary convex-hull polygonalization could otherwise create a spurious boundary
segment. -/
def PlaneGraphRealization.EdgeCoordZeroTrichotomy
    (G : K.PlaneGraphRealization) : Prop :=
  ∀ e : K.Edge,
    (∀ x ∈ G.edgeImage e, x 0 = 0) ∨
      (∃ v : K.Vertex, v ∈ e.1 ∧
        G.edgeImage e ∩ {x | x 0 = 0} = {G.vertexImage v}) ∨
      G.edgeImage e ∩ {x | x 0 = 0} = ∅

omit [T2Space S] in
/-- Including an edge simplex in an incident face does not change its endpoint
coordinates. -/
private theorem edgeSimplexInFace_apply
    (f : K.Face) (e : K.Edge) (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1}) (w : {v // v ∈ e.1}) :
    K.edgeSimplexInFace f e hef z ⟨w.1, hef w.2⟩ = z w := by
  have hcoords := congrFun (extendFaceCoordinates_map_subset hef z) w.1
  rw [extendFaceCoordinates_of_mem (K.faceVertices f)
      (stdSimplex.map (fun v : {v // v ∈ e.1} ↦
        ⟨v.1, hef v.2⟩) z) (hef w.2),
    extendFaceCoordinates_of_mem e.1 z w.2] at hcoords
  exact hcoords

omit [T2Space S] in
/-- Support on a selected set of face vertices can be checked before including an edge
simplex into its incident face. -/
private theorem edgeSimplexInFace_supportedOn_iff
    (f : K.Face) (e : K.Edge) (hef : e.1 ⊆ K.faceVertices f)
    (b : Finset K.Vertex) (z : stdSimplex ℝ {v // v ∈ e.1}) :
    (∀ v : {v // v ∈ K.faceVertices f}, v.1 ∉ b →
        K.edgeSimplexInFace f e hef z v = 0) ↔
      ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 := by
  constructor
  · intro h w hwb
    have hw := h ⟨w.1, hef w.2⟩ hwb
    simpa only [edgeSimplexInFace_apply] using hw
  · intro h v hvb
    by_cases hve : v.1 ∈ e.1
    · let w : {w // w ∈ e.1} := ⟨v.1, hve⟩
      have hw := h w hvb
      have happly := edgeSimplexInFace_apply (K := K) f e hef z w
      change K.edgeSimplexInFace f e hef z v = 0
      rw [show v = ⟨w.1, hef w.2⟩ by apply Subtype.ext; rfl,
        happly]
      exact hw
    · exact K.edgeSimplexInFace_supported f e hef z v hve

omit [T2Space S] in
/-- A facewise exposed zero locus gives the edgewise full/singleton/empty alternatives. -/
theorem edgeCoordZeroTrichotomy_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) (hface : G.FacewiseCoordZeroExposed) :
    G.EdgeCoordZeroTrichotomy := by
  classical
  intro e
  let f : K.Face := K.edgeFace e
  have hef : e.1 ⊆ K.faceVertices f := K.edge_subset_faceVertices e
  obtain ⟨b, -, -, hb⟩ := hface f
  let a : K.Vertex := K.edgeFirst e
  let d : K.Vertex := K.edgeSecond e
  have hae : a ∈ e.1 := K.edgeFirst_mem e
  have hde : d ∈ e.1 := K.edgeSecond_mem e
  have had : a ≠ d := K.edgeFirst_ne_edgeSecond e
  have hendpoints (w : {v // v ∈ e.1}) : w.1 = a ∨ w.1 = d := by
    have hw : w.1 ∈
        ({K.edgeFirst e, K.edgeSecond e} : Finset K.Vertex) := by
      rw [← K.edge_eq_pair e]
      exact w.2
    simpa only [a, d, Finset.mem_insert, Finset.mem_singleton] using hw
  have hzero (p : K.support) (z : stdSimplex ℝ {v // v ∈ e.1})
      (hz : K.edgeMap e z = p.1) :
      G.map p 0 = 0 ↔
        ∀ w : {w // w ∈ e.1}, w.1 ∉ b →
          z w = 0 := by
    let x : K.ClosedFace f := K.edgeSimplexInFace f e hef z
    have hpx : faceToSupport (K := K) f x = p := by
      apply Subtype.ext
      exact (K.faceMap_edgeSimplexInFace f e hef z).trans hz
    calc
      G.map p 0 = 0 ↔
          G.map (faceToSupport (K := K) f x) 0 = 0 := by rw [hpx]
      _ ↔ ∀ v : {v // v ∈ K.faceVertices f}, v.1 ∉ b → x v = 0 :=
        hb x
      _ ↔ ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
        edgeSimplexInFace_supportedOn_iff (K := K) f e hef b z
  by_cases hab : a ∈ b
  · by_cases hdb : d ∈ b
    · left
      rintro y ⟨p, hp, rfl⟩
      obtain ⟨z, hz⟩ := hp
      apply (hzero p z hz).mpr
      intro w hwb
      rcases hendpoints w with hwa | hwd
      · exact absurd (hwa ▸ hab) hwb
      · exact absurd (hwd ▸ hdb) hwb
    · right
      left
      refine ⟨a, hae, ?_⟩
      ext y
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hpZero⟩
        let z : stdSimplex ℝ {v // v ∈ e.1} := Classical.choose hp
        have hz : K.edgeMap e z = p.1 := Classical.choose_spec hp
        have hzSupport :
            ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
          (hzero p z hz).mp hpZero
        let wa : {v // v ∈ e.1} := ⟨a, hae⟩
        let wd : {v // v ∈ e.1} := ⟨d, hde⟩
        have hzd : z wd = 0 := hzSupport wd hdb
        have hza : z wa = 1 := by
          calc
            z wa = z wa + z wd := by rw [hzd, add_zero]
            _ = ∑ w, z w := by
              rw [show (Finset.univ : Finset {v // v ∈ e.1}) = {wa, wd} by
                ext w
                simp only [Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_iff]
                rcases hendpoints w with hw | hw
                · exact Or.inl (Subtype.ext hw)
                · exact Or.inr (Subtype.ext hw)]
              simp [show wa ≠ wd by
                intro h; exact had (congrArg Subtype.val h)]
            _ = 1 := z.2.2
        have hzVertex : z = stdSimplex.vertex wa := by
          apply stdSimplex.ext
          funext w
          rcases hendpoints w with hw | hw
          · rw [show w = wa by apply Subtype.ext; exact hw]
            simp [hza]
          · rw [show w = wd by apply Subtype.ext; exact hw, hzd]
            simp [show wd ≠ wa by
              intro h; exact had (congrArg Subtype.val h).symm]
        have hpSource :
            p = ⟨K.vertexPoint a, K.vertexPoint_mem_support a⟩ := by
          apply Subtype.ext
          rw [← hz, hzVertex,
            K.edgeMap_vertex_eq_vertexPoint]
        rw [hpSource]
        exact Set.mem_singleton _
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        have hvImage : G.vertexImage a ∈ G.edgeImage e :=
          (G.vertexImage_mem_edgeImage_iff a e).mpr hae
        refine ⟨hvImage, ?_⟩
        let p : K.support :=
          ⟨K.vertexPoint a, K.vertexPoint_mem_support a⟩
        let wa : {v // v ∈ e.1} := ⟨a, hae⟩
        change G.map p 0 = 0
        have hzedge :
            K.edgeMap e (stdSimplex.vertex wa) = p.1 := by
          exact K.edgeMap_vertex_eq_vertexPoint e wa
        apply (hzero p (stdSimplex.vertex wa) hzedge).mpr
        intro w hwb
        have hwa : w ≠ wa := by
          intro hw
          apply hwb
          rw [hw]
          exact hab
        simp [stdSimplex.vertex, hwa]
  · by_cases hdb : d ∈ b
    · right
      left
      refine ⟨d, hde, ?_⟩
      ext y
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hpZero⟩
        let z : stdSimplex ℝ {v // v ∈ e.1} := Classical.choose hp
        have hz : K.edgeMap e z = p.1 := Classical.choose_spec hp
        have hzSupport :
            ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
          (hzero p z hz).mp hpZero
        let wa : {v // v ∈ e.1} := ⟨a, hae⟩
        let wd : {v // v ∈ e.1} := ⟨d, hde⟩
        have hza : z wa = 0 := hzSupport wa hab
        have hzd : z wd = 1 := by
          calc
            z wd = z wa + z wd := by rw [hza, zero_add]
            _ = ∑ w, z w := by
              rw [show (Finset.univ : Finset {v // v ∈ e.1}) = {wa, wd} by
                ext w
                simp only [Finset.mem_univ, Finset.mem_insert,
                  Finset.mem_singleton, true_iff]
                rcases hendpoints w with hw | hw
                · exact Or.inl (Subtype.ext hw)
                · exact Or.inr (Subtype.ext hw)]
              simp [show wa ≠ wd by
                intro h; exact had (congrArg Subtype.val h)]
            _ = 1 := z.2.2
        have hzVertex : z = stdSimplex.vertex wd := by
          apply stdSimplex.ext
          funext w
          rcases hendpoints w with hw | hw
          · rw [show w = wa by apply Subtype.ext; exact hw, hza]
            simp [show wa ≠ wd by
              intro h; exact had (congrArg Subtype.val h)]
          · rw [show w = wd by apply Subtype.ext; exact hw]
            simp [hzd]
        have hpSource :
            p = ⟨K.vertexPoint d, K.vertexPoint_mem_support d⟩ := by
          apply Subtype.ext
          rw [← hz, hzVertex,
            K.edgeMap_vertex_eq_vertexPoint]
        rw [hpSource]
        exact Set.mem_singleton _
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        have hvImage : G.vertexImage d ∈ G.edgeImage e :=
          (G.vertexImage_mem_edgeImage_iff d e).mpr hde
        refine ⟨hvImage, ?_⟩
        let p : K.support :=
          ⟨K.vertexPoint d, K.vertexPoint_mem_support d⟩
        let wd : {v // v ∈ e.1} := ⟨d, hde⟩
        change G.map p 0 = 0
        have hzedge :
            K.edgeMap e (stdSimplex.vertex wd) = p.1 := by
          exact K.edgeMap_vertex_eq_vertexPoint e wd
        apply (hzero p (stdSimplex.vertex wd) hzedge).mpr
        intro w hwb
        have hwd : w ≠ wd := by
          intro hw
          apply hwb
          rw [hw]
          exact hdb
        simp [stdSimplex.vertex, hwd]
    · right
      right
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨⟨p, hp, rfl⟩, hpZero⟩
      let z : stdSimplex ℝ {v // v ∈ e.1} := Classical.choose hp
      have hz : K.edgeMap e z = p.1 := Classical.choose_spec hp
      have hzSupport :
          ∀ w : {w // w ∈ e.1}, w.1 ∉ b → z w = 0 :=
        (hzero p z hz).mp hpZero
      have hzeroAll : ∀ w, z w = 0 := by
        intro w
        rcases hendpoints w with hw | hw
        · exact hzSupport w (hw ▸ hab)
        · exact hzSupport w (hw ▸ hdb)
      have : (∑ w, z w) = 0 := by simp [hzeroAll]
      have hone : (∑ w, z w) = 1 := z.2.2
      exact one_ne_zero (hone.symm.trans this)

omit [T2Space S] in
/-- The edgewise zero-locus trichotomy makes the simultaneous graph replacement preserve the
supporting boundary line exactly.  The forward direction uses the supporting-face theorem for
the replacement convex hull; the reverse direction uses vertex fixing in the singleton case. -/
theorem graphReplacementPreservesCoordZero_of_edgeCoordZeroTrichotomy
    (G : K.PlaneGraphRealization)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hedges : G.EdgeCoordZeroTrichotomy) :
    G.GraphReplacementPreservesCoordZero := by
  intro p
  let e : K.Edge := containingEdge (K := K) p
  have hpe : p.1 ∈ edgeInSupport (K := K) e :=
    mem_edgeInSupport_containingEdge (K := K) p
  have hpCarrier : p.1.1 ∈ K.edgeCarrier e := by
    change p.1 ∈ Subtype.val ⁻¹' K.edgeCarrier e
    rw [← edgeInSupport_eq_preimage (K := K) e]
    exact hpe
  have hpImage : G.map p.1 ∈ G.edgeImage e :=
    ⟨p.1, hpCarrier, rfl⟩
  have hedgeHalf : G.edgeImage e ⊆ HalfPlaneSet := by
    rintro x ⟨q, -, rfl⟩
    exact hhalf (Set.mem_range_self q)
  rw [G.graphReplacementMap_eq e p hpe]
  rcases hedges e with hfull | hsingle | hempty
  · constructor
    · intro _
      exact hfull (G.map p.1) hpImage
    · intro _
      have hyCarrier :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            (G.replacementArc e).completeCarrier := by
        rw [← G.range_replacementEdgeMap e]
        exact Set.mem_range_self _
      have hyHull :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            convexHull ℝ (G.edgeImage e) :=
        (G.replacementArc e).completeCarrier_subset_edgeConvexHull hyCarrier
      have hyZero :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            {x | cartesianX x = 0} := by
        apply convexHull_min (𝕜 := ℝ)
        · intro x hx
          exact hfull x hx
        · exact (convex_singleton (0 : ℝ)).affine_preimage cartesianX
        · exact hyHull
      exact hyZero
  · obtain ⟨v, hve, hzeroSet⟩ := hsingle
    let pv : edgeInSupport (K := K) e :=
      ⟨⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩,
        by
          rw [edgeInSupport_eq_preimage (K := K)]
          exact (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve⟩
    have hvZero : G.vertexImage v 0 = 0 := by
      have hvImage : G.vertexImage v ∈ G.edgeImage e :=
        (G.vertexImage_mem_edgeImage_iff v e).mpr hve
      have hvMem :
          G.vertexImage v ∈ G.edgeImage e ∩ {x | x 0 = 0} := by
        rw [hzeroSet]
        exact Set.mem_singleton _
      exact hvMem.2
    constructor
    · intro hyZero
      have hyCarrier :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            (G.replacementArc e).completeCarrier := by
        rw [← G.range_replacementEdgeMap e]
        exact Set.mem_range_self _
      have hyHull :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            convexHull ℝ (G.edgeImage e ∩ {x | x 0 = 0}) :=
        (G.replacementArc e).mem_convexHull_edgeImage_coordZero G
          hedgeHalf hyCarrier hyZero
      have hyVertex :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ = G.vertexImage v := by
        rw [hzeroSet, convexHull_singleton] at hyHull
        exact hyHull
      have hpv : (⟨p.1, hpe⟩ : edgeInSupport (K := K) e) = pv := by
        apply G.replacementEdgeMap_injective e
        rw [hyVertex, G.replacementEdgeMap_vertex e v hve]
      have hpSupport :
          p.1 = (⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ : K.support) :=
        congrArg (fun q : edgeInSupport (K := K) e ↦ q.1) hpv
      rw [hpSupport]
      exact hvZero
    · intro hpZero
      have hpZeroMem :
          G.map p.1 ∈ G.edgeImage e ∩ {x | x 0 = 0} :=
        ⟨hpImage, hpZero⟩
      have hpImageEq : G.map p.1 = G.vertexImage v := by
        rw [hzeroSet] at hpZeroMem
        exact hpZeroMem
      have hpSupport :
          p.1 = (⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ : K.support) :=
        G.isEmbedding.injective hpImageEq
      have hpv : (⟨p.1, hpe⟩ : edgeInSupport (K := K) e) = pv := by
        apply Subtype.ext
        exact hpSupport
      rw [hpv, G.replacementEdgeMap_vertex e v hve]
      exact hvZero
  · constructor
    · intro hyZero
      have hyCarrier :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            (G.replacementArc e).completeCarrier := by
        rw [← G.range_replacementEdgeMap e]
        exact Set.mem_range_self _
      have hyHull :
          G.replacementEdgeMap e ⟨p.1, hpe⟩ ∈
            convexHull ℝ (G.edgeImage e ∩ {x | x 0 = 0}) :=
        (G.replacementArc e).mem_convexHull_edgeImage_coordZero G
          hedgeHalf hyCarrier hyZero
      rw [hempty, convexHull_empty] at hyHull
      exact hyHull.elim
    · intro hpZero
      have hpZeroMem :
          G.map p.1 ∈ G.edgeImage e ∩ {x | x 0 = 0} :=
        ⟨hpImage, hpZero⟩
      rw [hempty] at hpZeroMem
      exact hpZeroMem.elim

omit [T2Space S] in
/-- The facewise exposed-face invariant is the single source-side hypothesis needed for exact
zero-coordinate preservation by the simultaneous graph replacement. -/
theorem graphReplacementPreservesCoordZero_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hface : G.FacewiseCoordZeroExposed) :
    G.GraphReplacementPreservesCoordZero :=
  graphReplacementPreservesCoordZero_of_edgeCoordZeroTrichotomy G hhalf
    (edgeCoordZeroTrichotomy_of_facewiseCoordZeroExposed G hface)

/-- Once exact zero-coordinate preservation is known on the replacement graph, the polygonal
Schoenflies fillings preserve it on every filled face.  No filled-face interior can reach the
supporting line, so the two-dimensional statement reduces completely to the one-skeleton. -/
theorem polygonalReplacementHomeomorph_coordZero_iff
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hsource : G.SourceCoordZeroCarriedByOneSkeleton)
    (hgraph : G.GraphReplacementPreservesCoordZero)
    (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1.1 0 = 0 ↔
      G.map p 0 = 0 := by
  constructor
  · intro hpZero
    let f : K.Face := K.supportFace p
    let J : PolygonalCircle := K.facePolygonalCircle (G := G) f
    have hcarrierHalf : J.carrier ⊆ HalfPlaneSet := by
      exact (K.facePolygonalCircle_carrier_subset_graphReplacement
        (G := G) f).trans
          (range_graphReplacementMap_subset_halfPlane G hhalf)
    have hpClosed :
        (K.polygonalReplacementHomeomorph H p).1.1 ∈ J.closedRegion := by
      change
        (K.facePLFilling (G := G) (K.supportFace p)).faceMap
            (K.supportFacePoint p) ∈ J.closedRegion
      rw [show J =
        K.facePolygonalCircle (G := G) (K.supportFace p) by rfl,
        ← (K.facePLFilling (G := G) (K.supportFace p)).range_faceMap]
      exact Set.mem_range_self _
    have hpCarrier :
        (K.polygonalReplacementHomeomorph H p).1.1 ∈ J.carrier :=
      J.mem_carrier_of_mem_closedRegion_coordZero hcarrierHalf hpClosed hpZero
    obtain ⟨q, hq⟩ :=
      K.facePolygonalCircle_carrier_subset_graphReplacement
        (G := G) f hpCarrier
    have hqMap :
        (K.polygonalReplacementHomeomorph H q.1).1.1 =
          G.graphReplacementMap q :=
      polygonalReplacementMap_eq_graphReplacementMap G H q
    have hpqTarget :
        K.polygonalReplacementHomeomorph H p =
          K.polygonalReplacementHomeomorph H q.1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hq.symm.trans hqMap.symm
    have hpq : p = q.1 :=
      (K.polygonalReplacementHomeomorph H).injective hpqTarget
    rw [hpq]
    exact hgraph q |>.mp (by rw [← hqMap, ← hpq]; exact hpZero)
  · intro hpZero
    let q : oneSkeletonInSupport (K := K) :=
      ⟨p, hsource p hpZero⟩
    have hqZero : G.graphReplacementMap q 0 = 0 :=
      (hgraph q).mpr hpZero
    rw [show p = q.1 by rfl]
    have hqMap :=
      polygonalReplacementMap_eq_graphReplacementMap G H q
    change
      (K.polygonalReplacementHomeomorph H q.1).1.1 =
        G.graphReplacementMap q at hqMap
    rw [hqMap]
    exact hqZero

/-- Exact preservation on filled faces, stated directly from the facewise exposed-face
invariant. -/
theorem polygonalReplacementHomeomorph_coordZero_iff_of_facewiseCoordZeroExposed
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hhalf : Set.range G.map ⊆ HalfPlaneSet)
    (hface : G.FacewiseCoordZeroExposed) (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1.1 0 = 0 ↔
      G.map p 0 = 0 :=
  polygonalReplacementHomeomorph_coordZero_iff G H hhalf
    (sourceCoordZeroCarriedByOneSkeleton_of_facewiseCoordZeroExposed G hface)
    (graphReplacementPreservesCoordZero_of_facewiseCoordZeroExposed G hhalf hface) p

omit [T2Space S] in
/-- A controlled compatible cellwise replacement lands in the permitted perturbation region. -/
theorem polygonalReplacementMap_mem_region (G : K.PlaneGraphRealization)
    (H : K.CellwiseCompatibility G) {phi : K.support → ℝ}
    (_ : FaceBoundariesControlled G phi)
    (_ : G.ControlsStayInRegion phi) (p : K.support) :
    (K.polygonalReplacementMap H p).1.1 ∈ G.region :=
  (K.polygonalReplacementMap H p).1.2

/-- The full locally finite Chapter 6 output from its quantitative graph hypotheses. -/
theorem exists_controlled_polygonalReplacement (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hsep : SeparatesVerticesFromFaces G phi)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    ∃ H : K.CellwiseCompatibility G,
      (∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p) := by
  let H := cellwiseCompatibility_of_control (G := G) hfaces hcontrol hsep hregion hloc
  exact ⟨H, fun p ↦ polygonalReplacementMap_dist_le H hcontrol p⟩

/-- The complete locally finite Chapter 6 output in Moise's facewise side-control form.
Uniform frontier control supplies target containment and local finiteness automatically. -/
theorem exists_controlled_polygonalReplacement_of_facewise_close
    (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi)
    (hclose : FaceBoundariesClose G (faceVertexSeparationRadius G)) :
    ∃ H : K.CellwiseCompatibility G,
      ∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p := by
  let H := cellwiseCompatibility_of_facewise_close (G := G) hfaces hclose
    (closedRegions_mem_region_of_uniformFrontierControl G hcontrol hfrontier)
    (locallyFinite_closedRegions_of_uniformFrontierControl G hcontrol hfrontier)
  exact ⟨H, fun p ↦ polygonalReplacementMap_dist_le H hcontrol p⟩

/-- The Chapter 6 cellwise approximation from the exact edge-mesh condition supplied by an
internal edge subdivision.  No independent side hypothesis remains: the incident-face minimum
turns edgewise diameter control into the required facewise closeness. -/
theorem exists_controlled_polygonalReplacement_of_edgeMesh
    (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi)
    (hmesh : ∀ e : K.Edge,
      2 * Metric.diam (G.edgeImage e) < edgeFaceSeparationRadius G e) :
    ∃ H : K.CellwiseCompatibility G,
      ∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p := by
  exact exists_controlled_polygonalReplacement_of_facewise_close G hfaces hcontrol hfrontier
    (faceBoundariesClose_of_edgeFaceSeparation_control (G := G) hmesh)

omit [T2Space S] in
/-- If the replacement graph lies in the closed right half-plane, every selected polygonal face
disk lies there too. -/
theorem facePolygonalCircle_closedRegion_subset_halfPlane
    (G : K.PlaneGraphRealization)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet)
    (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ HalfPlaneSet := by
  apply (K.facePolygonalCircle (G := G) f).closedRegion_subset_halfPlane
  exact (K.facePolygonalCircle_carrier_subset_graphReplacement (G := G) f).trans hgraph

omit [T2Space S] in
/-- Consequently the entire assembled locally finite replacement complex stays in the closed
right half-plane. -/
theorem polygonalReplacementComplex_support_subset_halfPlane
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet) :
    Subtype.val '' (K.polygonalReplacementComplex H).support ⊆ HalfPlaneSet := by
  rintro p ⟨q, hq, rfl⟩
  have hpSupport : q ∈ (K.polygonalReplacementComplex H).support := hq
  obtain ⟨f, hpf⟩ := Set.mem_iUnion.mp hpSupport
  rw [K.polygonalReplacementComplex_faceCarrier H f] at hpf
  exact facePolygonalCircle_closedRegion_subset_halfPlane G hgraph f hpf

/-- Pointwise half-plane preservation for the assembled replacement homeomorphism. -/
theorem polygonalReplacementHomeomorph_mem_halfPlane
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet)
    (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1.1 ∈ HalfPlaneSet :=
  polygonalReplacementComplex_support_subset_halfPlane G H hgraph
    ⟨(K.polygonalReplacementHomeomorph H p).1,
      (K.polygonalReplacementHomeomorph H p).2, rfl⟩

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
