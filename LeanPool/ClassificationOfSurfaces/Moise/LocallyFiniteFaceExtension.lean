/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteFaceModel
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceExtension
import LeanPool.ClassificationOfSurfaces.Moise.PLApproximation

/-!
# Coherent polygonal boundary maps for locally finite faces

The globally defined locally finite graph replacement is restricted to each standard triangular
frontier.  Since a shared abstract edge is represented by the same source-support points, the
resulting boundary maps agree literally on overlaps.  This is the compatibility needed before
applying polygonal Schoenflies face by face.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-- The inverse standard-face chart takes cyclic side `i` into the corresponding native side. -/
theorem facePlaneHomeomorph_symm_mem_faceSide (f : K.Face) (i : ZMod 3)
    (p : StandardFaceBoundary)
    (hp : p.1 ∈ standardTriangleCircle.edgeSegment i) :
    (K.facePlaneHomeomorph f).symm
        ⟨p.1, standardFaceBoundary_mem_region p⟩ ∈ K.faceSide f i := by
  rw [← K.facePlaneHomeomorph_image_edge f i] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have heq : (K.facePlaneHomeomorph f).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩ = x := by
    apply (K.facePlaneHomeomorph f).injective
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]
    exact Subtype.ext hxp.symm
  rwa [heq]

/-- The source-support point named by a standard face-boundary point. -/
noncomputable def faceBoundarySupportPoint (f : K.Face)
    (p : StandardFaceBoundary) : K.support :=
  faceToSupport (K := K) f
    ((K.facePlaneHomeomorph f).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩)

theorem faceBoundarySupportPoint_mem_edge (f : K.Face) (i : ZMod 3)
    (p : StandardFaceBoundary)
    (hp : p.1 ∈ standardTriangleCircle.edgeSegment i) :
    K.faceBoundarySupportPoint f p ∈ edgeInSupport (K := K) (K.faceEdge f i) := by
  rw [edgeInSupport_eq_preimage (K := K)]
  exact K.faceMap_mem_edgeCarrier_of_mem_faceSide f i _
    (K.facePlaneHomeomorph_symm_mem_faceSide f i p hp)

theorem faceBoundarySupportPoint_mem_oneSkeleton (f : K.Face)
    (p : StandardFaceBoundary) :
    K.faceBoundarySupportPoint f p ∈ oneSkeletonInSupport (K := K) := by
  have hpCarrier : p.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using p.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  exact Set.mem_iUnion.mpr
    ⟨K.faceEdge f i, K.faceBoundarySupportPoint_mem_edge f i p hi⟩

/-- The canonical lift of a standard triangular frontier to the source one-skeleton. -/
noncomputable def faceBoundaryLift (f : K.Face) :
    StandardFaceBoundary → oneSkeletonInSupport (K := K) :=
  fun p ↦ ⟨K.faceBoundarySupportPoint f p,
    K.faceBoundarySupportPoint_mem_oneSkeleton f p⟩

theorem continuous_faceBoundarySupportPoint (f : K.Face) :
    Continuous (K.faceBoundarySupportPoint f) := by
  apply Continuous.subtype_mk
  exact (K.faceMap_continuous f).comp
    ((K.facePlaneHomeomorph f).symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))

theorem continuous_faceBoundaryLift (f : K.Face) :
    Continuous (K.faceBoundaryLift f) := by
  apply Continuous.subtype_mk
  exact K.continuous_faceBoundarySupportPoint f

theorem injective_faceBoundaryLift (f : K.Face) :
    Function.Injective (K.faceBoundaryLift f) := by
  intro p q hpq
  have hmap : K.faceMap f
      ((K.facePlaneHomeomorph f).symm
        ⟨p.1, standardFaceBoundary_mem_region p⟩) =
      K.faceMap f
        ((K.facePlaneHomeomorph f).symm
          ⟨q.1, standardFaceBoundary_mem_region q⟩) :=
    congrArg (fun z : oneSkeletonInSupport (K := K) ↦ (z.1 : K.support).1) hpq
  have hface := K.faceMap_injective f hmap
  have hstandard := (K.facePlaneHomeomorph f).symm.injective hface
  apply Subtype.ext
  exact congrArg (fun z : standardFaceRegion ↦ z.1) hstandard

/-- The global graph replacement expressed on one standard face frontier. -/
noncomputable def faceBoundaryMap (f : K.Face) (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ frontier standardFaceRegion then
    G.graphReplacementMap (K.faceBoundaryLift f ⟨p, hp⟩)
  else 0

@[simp] theorem faceBoundaryMap_apply (f : K.Face) (p : StandardFaceBoundary) :
    K.faceBoundaryMap (G := G) f p.1 =
      G.graphReplacementMap (K.faceBoundaryLift f p) := by
  simp [faceBoundaryMap, p.2]

theorem continuousOn_faceBoundaryMap (f : K.Face) :
    ContinuousOn (K.faceBoundaryMap (G := G) f)
      (frontier standardFaceRegion) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert G.continuous_graphReplacementMap.comp (K.continuous_faceBoundaryLift f) using 1
  funext p
  exact K.faceBoundaryMap_apply f p

theorem faceBoundaryMap_injectiveOn (f : K.Face) :
    Set.InjOn (K.faceBoundaryMap (G := G) f)
      (frontier standardFaceRegion) := by
  intro p hp q hq hpq
  let p' : StandardFaceBoundary := ⟨p, hp⟩
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  have hgraph : G.graphReplacementMap (K.faceBoundaryLift f p') =
      G.graphReplacementMap (K.faceBoundaryLift f q') := by
    rw [← K.faceBoundaryMap_apply f p', ← K.faceBoundaryMap_apply f q']
    exact hpq
  exact congrArg Subtype.val
    (K.injective_faceBoundaryLift f (G.graphReplacementMap_injective hgraph))

/-- The globally oriented affine parameter on a standard side lies on the face frontier. -/
theorem faceEdgeSourcePoint_mem_frontier (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint f i r.1 ∈ frontier standardFaceRegion := by
  have hpEdge : K.faceEdgeSourcePoint f i r.1 ∈
      standardTriangleCircle.edgeSegment i := by
    rw [← IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i]
    exact K.faceEdgeSourcePoint_mem_standardEdge f i r.2
  have hpCarrier : K.faceEdgeSourcePoint f i r.1 ∈
      standardTriangleCircle.carrier :=
    Set.mem_iUnion.mpr ⟨i, hpEdge⟩
  rw [standardTriangleCircle_carrier] at hpCarrier
  simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier

/-- On a standard face side, the canonical boundary lift is literally the global canonical
source path of the corresponding abstract edge. -/
theorem faceBoundarySupportPoint_sourcePoint (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    K.faceBoundarySupportPoint f
        ⟨K.faceEdgeSourcePoint f i r.1,
          K.faceEdgeSourcePoint_mem_frontier f i r⟩ =
      edgePathInSupport (K := K) (K.faceEdge f i) r := by
  apply Subtype.ext
  change K.faceMap f
      ((K.facePlaneHomeomorph f).symm
        ⟨K.faceEdgeSourcePoint f i r.1,
          standardFaceBoundary_mem_region
            ⟨K.faceEdgeSourcePoint f i r.1,
              K.faceEdgeSourcePoint_mem_frontier f i r⟩⟩) =
    K.edgePath (K.faceEdge f i) r
  have hinv :
      (K.facePlaneHomeomorph f).symm
          ⟨K.faceEdgeSourcePoint f i r.1,
            standardFaceBoundary_mem_region
              ⟨K.faceEdgeSourcePoint f i r.1,
                K.faceEdgeSourcePoint_mem_frontier f i r⟩⟩ =
        K.edgeSimplexInFace f (K.faceEdge f i)
          (K.faceEdge_subset_faceVertices f i)
          (K.edgeSimplexPath (K.faceEdge f i) r) := by
    apply (K.facePlaneHomeomorph f).injective
    rw [(K.facePlaneHomeomorph f).apply_symm_apply]
    apply Subtype.ext
    exact K.facePlaneHomeomorph_edgeSimplexPath f i r |>.symm
  rw [hinv, K.faceMap_edgeSimplexInFace]
  rfl

/-- On every oriented source side, the face boundary map is the complete polygonal replacement
path with the identical unit-interval parameter. -/
theorem faceBoundaryMap_sourcePoint (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r.1) =
      (G.replacementArc (K.faceEdge f i)).completePath r := by
  let p : StandardFaceBoundary :=
    ⟨K.faceEdgeSourcePoint f i r.1,
      K.faceEdgeSourcePoint_mem_frontier f i r⟩
  have hpEdge : p.1 ∈ standardTriangleCircle.edgeSegment i := by
    rw [← IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i]
    exact K.faceEdgeSourcePoint_mem_standardEdge f i r.2
  change K.faceBoundaryMap (G := G) f p.1 = _
  rw [K.faceBoundaryMap_apply (G := G) f p]
  rw [G.graphReplacementMap_eq (K.faceEdge f i) (K.faceBoundaryLift f p)
    (K.faceBoundarySupportPoint_mem_edge f i p hpEdge)]
  have hlift : (K.faceBoundaryLift f p).1 =
      edgePathInSupport (K := K) (K.faceEdge f i) r := by
    exact K.faceBoundarySupportPoint_sourcePoint f i r
  convert replacementEdgeMap_edgePath G (K.faceEdge f i) r using 1
  congr 1
  apply Subtype.ext
  exact hlift

/-- The canonical face boundary map has exactly the assembled three-edge carrier as image. -/
theorem faceBoundaryMap_image_frontier (f : K.Face) :
    K.faceBoundaryMap (G := G) f '' frontier standardFaceRegion =
      K.faceReplacementCarrier (G := G) f := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    have hpCarrier : p ∈ standardTriangleCircle.carrier := by
      rw [standardTriangleCircle_carrier]
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    let q : StandardFaceBoundary := ⟨p, hp⟩
    rw [K.faceBoundaryMap_apply f q,
      G.graphReplacementMap_eq (K.faceEdge f i) (K.faceBoundaryLift f q)
        (K.faceBoundarySupportPoint_mem_edge f i q hi),
      ← G.range_replacementEdgeMap (K.faceEdge f i)]
    exact Set.mem_range_self _
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [← G.range_replacementEdgeMap (K.faceEdge f i)] at hi
    obtain ⟨q, rfl⟩ := hi
    have hqEdge : q.1.1 ∈ K.edgeCarrier (K.faceEdge f i) := by
      have hq : q.1 ∈ Subtype.val ⁻¹' K.edgeCarrier (K.faceEdge f i) := by
        rw [← edgeInSupport_eq_preimage (K := K) (K.faceEdge f i)]
        exact q.2
      exact hq
    obtain ⟨z, hz⟩ := hqEdge
    let x : K.ClosedFace f := K.edgeSimplexInFace f (K.faceEdge f i)
      (K.faceEdge_subset_faceVertices f i) z
    let p : Plane := (K.facePlaneHomeomorph f x).1
    have hxSide : x ∈ K.faceSide f i := by
      intro v hv
      exact K.edgeSimplexInFace_supported f (K.faceEdge f i)
        (K.faceEdge_subset_faceVertices f i) z v hv
    have hpSide : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← K.facePlaneHomeomorph_image_edge f i]
      exact ⟨x, hxSide, rfl⟩
    have hpFrontier : p ∈ frontier standardFaceRegion := by
      have hpCarrier : p ∈ standardTriangleCircle.carrier :=
        Set.mem_iUnion.mpr ⟨i, hpSide⟩
      rw [standardTriangleCircle_carrier] at hpCarrier
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hpCarrier
    refine ⟨p, hpFrontier, ?_⟩
    let p' : StandardFaceBoundary := ⟨p, hpFrontier⟩
    have hlift : (K.faceBoundaryLift f p').1 = q.1 := by
      apply Subtype.ext
      change K.faceMap f
          ((K.facePlaneHomeomorph f).symm
            ⟨p, standardFaceBoundary_mem_region p'⟩) = q.1.1
      have hinv : (K.facePlaneHomeomorph f).symm
          ⟨p, standardFaceBoundary_mem_region p'⟩ = x := by
        apply (K.facePlaneHomeomorph f).injective
        rw [(K.facePlaneHomeomorph f).apply_symm_apply]
      rw [hinv, K.faceMap_edgeSimplexInFace, hz]
    rw [K.faceBoundaryMap_apply f p',
      G.graphReplacementMap_eq (K.faceEdge f i) (K.faceBoundaryLift f p')
        (K.faceBoundarySupportPoint_mem_edge f i p' hpSide)]
    congr 1
    apply Subtype.ext
    exact hlift

theorem faceBoundaryMap_image_polygon (f : K.Face) :
    K.faceBoundaryMap (G := G) f '' frontier standardFaceRegion =
      (K.facePolygonalCircle (G := G) f).carrier := by
  rw [K.faceBoundaryMap_image_frontier f, K.facePolygonalCircle_carrier f]

/-! ## A finite source subdivision carrying all boundary breakpoints -/

/-- All source breakpoints required on the three replacement sides of one face. -/
abbrev FaceBreakpoint (f : K.Face) :=
  Σ i : ZMod 3, EdgeBreakpoint (G.replacementArc (K.faceEdge f i))

/-- Place one replacement-edge breakpoint on its globally oriented standard side. -/
noncomputable def faceBreakpointPoint (f : K.Face)
    (b : FaceBreakpoint (K := K) (G := G) f) : Plane :=
  K.faceEdgeSourcePoint f b.1
    (edgeBreakpointParameter (G.replacementArc (K.faceEdge f b.1)) b.2)

theorem faceBreakpointPoint_mem_standardEdge (f : K.Face)
    (b : FaceBreakpoint (K := K) (G := G) f) :
    K.faceBreakpointPoint (G := G) f b ∈
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge b.1) := by
  apply K.faceEdgeSourcePoint_mem_standardEdge
  exact edgeBreakpointParameter_mem
    (G.replacementArc (K.faceEdge f b.1)) b.2

theorem faceBreakpointPoint_mem_standardOneSkeleton (f : K.Face)
    (b : FaceBreakpoint (K := K) (G := G) f) :
    K.faceBreakpointPoint (G := G) f b ∈
      standardTrianglePlaneComplex.oneSkeleton.support := by
  apply standardTrianglePlaneComplex.oneSkeleton.cellCarrier_subset_support
    (standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
      ⟨IntrinsicTwoComplex.faceStandardEdge_mem_simplexes b.1,
        (IntrinsicTwoComplex.faceStandardEdge_card b.1).le⟩)
  simpa only [PlaneComplex.oneSkeleton_cellCarrier] using
    K.faceBreakpointPoint_mem_standardEdge (G := G) f b

/-- The common finite subdivision of the standard triangular boundary carrying every spoke
join and every vertex of the three finite middle polygonal models. -/
noncomputable def faceBoundarySubdivision (f : K.Face) : PlaneComplex :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision
    (K.faceBreakpointPoint (G := G) f)

theorem faceBoundarySubdivision_subdivides (f : K.Face) :
    (K.faceBoundarySubdivision (G := G) f).Subdivides
      standardTrianglePlaneComplex.oneSkeleton :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_subdivides
    (K.faceBreakpointPoint (G := G) f)
    standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph

theorem faceBoundarySubdivision_support (f : K.Face) :
    (K.faceBoundarySubdivision (G := G) f).support =
      frontier standardFaceRegion := by
  rw [faceBoundarySubdivision,
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_support_eq
      (K.faceBreakpointPoint (G := G) f)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph,
    IntrinsicTwoComplex.standardTriangle_oneSkeleton_support,
    standardTriangleCircle_carrier]
  simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

/-- The first globally oriented standard corner, typed as a vertex of the standard boundary
graph. -/
noncomputable def faceEdgeFirstBoundaryVertex (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeFirstIndex f i

/-- The second globally oriented standard corner, typed as a vertex of the standard boundary
graph. -/
noncomputable def faceEdgeSecondBoundaryVertex (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeSecondIndex f i

@[simp] theorem faceEdgeFirstBoundaryVertex_position (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position
        (K.faceEdgeFirstBoundaryVertex f i) =
      standardTriangleVertex (K.faceEdgeFirstIndex f i) := rfl

@[simp] theorem faceEdgeSecondBoundaryVertex_position (f : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position
        (K.faceEdgeSecondBoundaryVertex f i) =
      standardTriangleVertex (K.faceEdgeSecondIndex f i) := rfl

theorem standardFaceEdgeFace_val_eq_boundaryEndpoints (f : K.Face) (i : ZMod 3) :
    (IntrinsicTwoComplex.standardFaceEdgeFace i).1 =
      {K.faceEdgeFirstBoundaryVertex f i,
        K.faceEdgeSecondBoundaryVertex f i} := by
  change IntrinsicTwoComplex.faceStandardEdge i =
    {K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i}
  exact K.faceStandardEdge_eq_endpointIndices f i

/-- The arbitrary finite graph enumeration of a standard side either follows or reverses the
global edge orientation. -/
theorem standardFaceEdge_endpoint_order (f : K.Face) (i : ZMod 3) :
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex f i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex f i) ∨
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex f i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex f i) := by
  let T := standardTrianglePlaneComplex.oneSkeleton
  let j := IntrinsicTwoComplex.standardFaceEdgeIndex i
  have hfirst : T.edgeFirst j ∈ (T.edgeAt j).1 := by
    rw [T.edgeAt_eq]
    simp
  have hsecond : T.edgeSecond j ∈ (T.edgeAt j).1 := by
    rw [T.edgeAt_eq]
    simp
  have hedge : (T.edgeAt j).1 =
      (IntrinsicTwoComplex.standardFaceEdgeFace i).1 :=
    congrArg Subtype.val (IntrinsicTwoComplex.standardFaceEdgeAt_eq i)
  rw [hedge, K.standardFaceEdgeFace_val_eq_boundaryEndpoints f i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (T.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (T.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim

theorem standardFaceEdgeParameter_sourcePoint_of_forward (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint f i r) = r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position f i,
    ← K.faceEdgeSecondBoundaryVertex_position f i,
    ← horient.1, ← horient.2,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_sourcePoint_of_reverse (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint f i r) = 1 - r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position f i,
    ← K.faceEdgeSecondBoundaryVertex_position f i,
    ← horient.2, ← horient.1, ← AffineMap.lineMap_apply_one_sub,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
    (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i) p =
      K.faceEdgeParameterAffine f i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_forward f i horient,
    K.faceEdgeParameterAffine_sourcePoint]

theorem standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
    (f : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex f i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex f i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter
        (IntrinsicTwoComplex.standardFaceEdgeIndex i) p =
      1 - K.faceEdgeParameterAffine f i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_reverse f i horient,
    K.faceEdgeParameterAffine_sourcePoint]

/-- Every face of the marked boundary subdivision lies on one side of every marked parameter,
measured in the finite graph enumeration coordinate. -/
theorem faceBoundarySubdivision_parameter_side_standard
    (f : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (G.replacementArc (K.faceEdge f i)))
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes) :
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) p ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (G := G) f ⟨i, b⟩)) ∨
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (G := G) f ⟨i, b⟩) ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter
          (IntrinsicTwoComplex.standardFaceEdgeIndex i) p) := by
  let T := standardTrianglePlaneComplex.oneSkeleton
  let point := K.faceBreakpointPoint (G := G) f
  let j := IntrinsicTwoComplex.standardFaceEdgeIndex i
  have hbCarrier : point ⟨i, b⟩ ∈ T.cellCarrier (T.edgeAt j).1 := by
    rw [show (T.edgeAt j).1 = IntrinsicTwoComplex.faceStandardEdge i from
      congrArg Subtype.val (IntrinsicTwoComplex.standardFaceEdgeAt_eq i)]
    rw [standardTrianglePlaneComplex.oneSkeleton_cellCarrier]
    exact K.faceBreakpointPoint_mem_standardEdge (G := G) f ⟨i, b⟩
  have hpoint : point ⟨i, b⟩ =
      AffineMap.lineMap (T.position (T.edgeFirst j)) (T.position (T.edgeSecond j))
        (T.edgeParameter j (point ⟨i, b⟩)) :=
    (T.lineMap_edgeParameter_eq j hbCarrier).symm
  have huArrangement :=
    ((T.markedEdgeArrangement point).mem_subordinateTo_simplexes_iff T).mp hu |>.1
  have hside := T.markedFaceCarrier_parameter_side point
    (⟨i, b⟩ : FaceBreakpoint (K := K) (G := G) f)
    j (T.edgeParameter j (point ⟨i, b⟩)) hpoint huArrangement
  simpa only [faceBoundarySubdivision, PlaneComplex.markedEdgeSubdivision,
    PlaneComplex.markedEdgeArrangement] using
    (((T.markedEdgeChain point).arrangementMesh.toPlaneComplex
      |>.subordinateTo_cellCarrier T u).symm ▸ hside)

/-- On a subdivision face contained in one standard side, the marked-side test is the globally
oriented edge-parameter test, independently of the graph enumeration orientation. -/
theorem faceBoundarySubdivision_parameter_side
    (f : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (G.replacementArc (K.faceEdge f i)))
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes)
    (hui : (K.faceBoundarySubdivision (G := G) f).cellCarrier u ⊆
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i)) :
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      K.faceEdgeParameterAffine f i p ≤
        edgeBreakpointParameter (G.replacementArc (K.faceEdge f i)) b) ∨
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      edgeBreakpointParameter (G.replacementArc (K.faceEdge f i)) b ≤
        K.faceEdgeParameterAffine f i p) := by
  have hside := K.faceBoundarySubdivision_parameter_side_standard
    (G := G) f i b hu
  have hmark : K.faceBreakpointPoint (G := G) f ⟨i, b⟩ =
      K.faceEdgeSourcePoint f i
        (edgeBreakpointParameter (G.replacementArc (K.faceEdge f i)) b) := rfl
  rcases K.standardFaceEdge_endpoint_order f i with hforward | hreverse
  · have hmarkEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
      f i hforward (K.faceBreakpointPoint_mem_standardEdge (G := G) f ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        f i hforward (hui hp)
      have hpSide := hle p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        f i hforward (hui hp)
      have hpSide := hge p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
  · have hmarkEq :=
      K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        f i hreverse (K.faceBreakpointPoint_mem_standardEdge (G := G) f ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        f i hreverse (hui hp)
      have h := hle p hp
      rw [hpEq, hmark, hmarkEq] at h
      linarith
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        f i hreverse (hui hp)
      have h := hge p hp
      rw [hpEq, hmark, hmarkEq] at h
      linarith

/-- The two spoke joins split each subdivision face on a selected standard side into the left,
middle, or right parameter range. -/
theorem faceBoundarySubdivision_piece
    (f : K.Face) (i : ZMod 3)
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes)
    (hui : (K.faceBoundarySubdivision (G := G) f).cellCarrier u ⊆
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i)) :
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      K.faceEdgeParameterAffine f i p ≤ (1 / 2 : ℝ)) ∨
    ((∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p) ∧
      (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
        K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ))) ∨
    (∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine f i p) := by
  have hhalf := K.faceBoundarySubdivision_parameter_side
    (G := G) f i none hu hui
  have hthree := K.faceBoundarySubdivision_parameter_side
    (G := G) f i (some none) hu hui
  change (∀ p ∈ _, K.faceEdgeParameterAffine f i p ≤ (1 / 2 : ℝ)) ∨
      (∀ p ∈ _, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p) at hhalf
  change (∀ p ∈ _, K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ)) ∨
      (∀ p ∈ _, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine f i p) at hthree
  rcases hhalf with hleHalf | hgeHalf
  · exact Or.inl hleHalf
  · rcases hthree with hleThree | hgeThree
    · exact Or.inr (Or.inl ⟨hgeHalf, hleThree⟩)
    · exact Or.inr (Or.inr hgeThree)

/-! ## Affine formulas on subdivision pieces -/

/-- The affine map from a standard face side into the source axis of the finite middle
polygonal model. -/
noncomputable def faceMiddleSourceAffine (f : K.Face) (i : ZMod 3) :
    Plane →ᵃ[ℝ] Plane :=
  let A := G.replacementArc (K.faceEdge f i)
  (AffineMap.lineMap
    (planePoint (A.parameterization.length *
      (A.exitData.left + (A.exitData.right - A.exitData.left) * (-2))) 0)
    (planePoint (A.parameterization.length *
      (A.exitData.left + (A.exitData.right - A.exitData.left) * 2)) 0)).comp
    (K.faceEdgeParameterAffine f i)

@[simp] theorem faceMiddleSourceAffine_apply (f : K.Face) (i : ZMod 3)
    (p : Plane) :
    K.faceMiddleSourceAffine (G := G) f i p =
      planePoint ((G.replacementArc (K.faceEdge f i)).parameterization.length *
        ((G.replacementArc (K.faceEdge f i)).exitData.left +
          ((G.replacementArc (K.faceEdge f i)).exitData.right -
            (G.replacementArc (K.faceEdge f i)).exitData.left) *
          (4 * K.faceEdgeParameterAffine f i p - 2))) 0 := by
  let A := G.replacementArc (K.faceEdge f i)
  change (AffineMap.lineMap
      (planePoint (A.parameterization.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) * (-2))) 0)
      (planePoint (A.parameterization.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) * 2)) 0))
        (K.faceEdgeParameterAffine f i p) = _
  ext j
  fin_cases j <;>
    simp [AffineMap.lineMap_apply_module, planePoint]; ring

/-- The boundary map is affine on every subset of a standard side contained in the first
spoke range. -/
theorem faceBoundaryMap_affineOn_left
    (f : K.Face) (i : ZMod 3) {E : Set Plane}
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i))
    (hle : ∀ p ∈ E, K.faceEdgeParameterAffine f i p ≤ (1 / 2 : ℝ)) :
    IsAffineOn (K.faceBoundaryMap (G := G) f) E := by
  let A := G.replacementArc (K.faceEdge f i)
  let scalar : Plane →ᵃ[ℝ] ℝ := (2 : ℝ) • K.faceEdgeParameterAffine f i
  let g : Plane →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap (G.vertexImage (K.edgeFirst (K.faceEdge f i)))
      A.leftEndpoint).comp scalar
  refine ⟨g, ?_⟩
  intro p hp
  have hpSide := hside hp
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hpSide
  obtain ⟨r, hr, rfl⟩ := hpSide
  let q : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have hq : r ≤ (1 / 2 : ℝ) := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hle (K.faceEdgeSourcePoint f i r) hp
  rw [show K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r) =
      A.completePath q from K.faceBoundaryMap_sourcePoint (G := G) f i q,
    LocallyFiniteTriangleComplex.CentralPolygonalArc.completePath_eq_left A q hq]
  simp [g, scalar, q, AffineMap.comp_apply]

/-- The boundary map is affine on every subset of a standard side contained in the final
spoke range. -/
theorem faceBoundaryMap_affineOn_right
    (f : K.Face) (i : ZMod 3) {E : Set Plane}
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i))
    (hge : ∀ p ∈ E, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine f i p) :
    IsAffineOn (K.faceBoundaryMap (G := G) f) E := by
  let A := G.replacementArc (K.faceEdge f i)
  let scalar : Plane →ᵃ[ℝ] ℝ :=
    (4 : ℝ) • K.faceEdgeParameterAffine f i - AffineMap.const ℝ Plane 3
  let g : Plane →ᵃ[ℝ] Plane :=
    (AffineMap.lineMap A.rightEndpoint
      (G.vertexImage (K.edgeSecond (K.faceEdge f i)))).comp scalar
  refine ⟨g, ?_⟩
  intro p hp
  have hpSide := hside hp
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hpSide
  obtain ⟨r, hr, rfl⟩ := hpSide
  let q : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have hq : (3 / 4 : ℝ) ≤ r := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hge (K.faceEdgeSourcePoint f i r) hp
  rw [show K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r) =
      A.completePath q from K.faceBoundaryMap_sourcePoint (G := G) f i q,
    LocallyFiniteTriangleComplex.CentralPolygonalArc.completePath_eq_right A q hq]
  simp [g, scalar, q, AffineMap.comp_apply]

/-- A middle side piece is affine once its affine source image lies in one simplex of the
finite polygonal segment model. -/
theorem faceBoundaryMap_affineOn_middle
    (f : K.Face) (i : ZMod 3) {E : Set Plane}
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier
      (IntrinsicTwoComplex.faceStandardEdge i))
    (hmid0 : ∀ p ∈ E, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p)
    (hmid1 : ∀ p ∈ E, K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ))
    (hsource : ∃ s ∈
        (G.replacementArc (K.faceEdge f i)).parameterization.source.simplexes,
      Set.MapsTo (K.faceMiddleSourceAffine (G := G) f i) E
        ((G.replacementArc (K.faceEdge f i)).parameterization.source.cellCarrier s)) :
    IsAffineOn (K.faceBoundaryMap (G := G) f) E := by
  let A := G.replacementArc (K.faceEdge f i)
  obtain ⟨s, hs, hmaps⟩ := hsource
  obtain ⟨q, hq⟩ := A.parameterization.map_affineOn s hs
  refine ⟨q.comp (K.faceMiddleSourceAffine (G := G) f i), ?_⟩
  intro p hp
  have hpSide := hside hp
  rw [← K.faceEdgeSourcePoint_image_Icc f i] at hpSide
  obtain ⟨r, hr, rfl⟩ := hpSide
  let t : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have ht0 : (1 / 2 : ℝ) ≤ r := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hmid0 (K.faceEdgeSourcePoint f i r) hp
  have ht1 : r ≤ (3 / 4 : ℝ) := by
    simpa only [K.faceEdgeParameterAffine_sourcePoint] using
      hmid1 (K.faceEdgeSourcePoint f i r) hp
  rw [show K.faceBoundaryMap (G := G) f (K.faceEdgeSourcePoint f i r) =
      A.completePath t from K.faceBoundaryMap_sourcePoint (G := G) f i t,
    LocallyFiniteTriangleComplex.CentralPolygonalArc.completePath_eq_middle A t ht0 ht1]
  simpa only [AffineMap.comp_apply, K.faceMiddleSourceAffine_apply,
    K.faceEdgeParameterAffine_sourcePoint] using hq (hmaps hp)

/-- The marked middle-model vertices ensure that a two-vertex subdivision face maps into one
simplex of the finite segment model. -/
theorem faceBoundarySubdivision_middleSource
    (f : K.Face) (i : ZMod 3)
    {u : Finset (K.faceBoundarySubdivision (G := G) f).Vertex}
    (hu : u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes)
    (hui : (K.faceBoundarySubdivision (G := G) f).cellCarrier u ⊆
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i))
    (hcard : u.card = 2)
    (hmid0 : ∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine f i p)
    (hmid1 : ∀ p ∈ (K.faceBoundarySubdivision (G := G) f).cellCarrier u,
      K.faceEdgeParameterAffine f i p ≤ (3 / 4 : ℝ)) :
    ∃ s ∈ (G.replacementArc (K.faceEdge f i)).parameterization.source.simplexes,
      Set.MapsTo (K.faceMiddleSourceAffine (G := G) f i)
        ((K.faceBoundarySubdivision (G := G) f).cellCarrier u)
        ((G.replacementArc (K.faceEdge f i)).parameterization.source.cellCarrier s) := by
  let R := K.faceBoundarySubdivision (G := G) f
  let A := G.replacementArc (K.faceEdge f i)
  let n : ℝ := A.parameterization.length
  let z : Plane → ℝ := fun p ↦ n *
    (A.exitData.left + (A.exitData.right - A.exitData.left) *
      (4 * K.faceEdgeParameterAffine f i p - 2))
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast A.resolvedWalk_length_pos
  have hdelta : 0 ≤ A.exitData.right - A.exitData.left :=
    sub_nonneg.mpr A.exitData.left_lt_right.le
  have hmono {p q : Plane}
      (hpq : K.faceEdgeParameterAffine f i p ≤
        K.faceEdgeParameterAffine f i q) : z p ≤ z q := by
    change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine f i p - 2)) ≤
      n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine f i q - 2))
    apply mul_le_mul_of_nonneg_left _ hn.le
    have hr : 4 * K.faceEdgeParameterAffine f i p - 2 ≤
        4 * K.faceEdgeParameterAffine f i q - 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hr hdelta
    linarith
  have hzBounds {p : Plane} (hp : p ∈ R.cellCarrier u) :
      z p ∈ Set.Icc 0 n := by
    have ht0 := hmid0 p hp
    have ht1 := hmid1 p hp
    have hr0 : 0 ≤ 4 * K.faceEdgeParameterAffine f i p - 2 := by linarith
    have hr1 : 4 * K.faceEdgeParameterAffine f i p - 2 ≤ 1 := by linarith
    constructor
    · exact mul_nonneg hn.le
        (add_nonneg A.exitData.left_nonneg (mul_nonneg hdelta hr0))
    · calc
        z p ≤ n * 1 := by
          apply mul_le_mul_of_nonneg_left _ hn.le
          have hmul := mul_le_mul_of_nonneg_left hr1 hdelta
          linarith [A.exitData.right_le_one]
        _ = n := mul_one n
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
  have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
    subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
  have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
    subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
  let a := min (z (R.position p)) (z (R.position q))
  let b := max (z (R.position p)) (z (R.position q))
  have hab : a ≤ b := min_le_max
  have ha : 0 ≤ a := le_min (hzBounds hp).1 (hzBounds hq).1
  have hb : b ≤ n := max_le (hzBounds hp).2 (hzBounds hq).2
  have havoid : ∀ v : A.parameterization.source.Vertex,
      A.parameterization.source.position v 0 ≤ a ∨
        b ≤ A.parameterization.source.position v 0 := by
    intro v
    let c := A.parameterization.source.position v 0
    by_cases hv0 : c / n < A.exitData.left
    · left
      have hcn : c < n * A.exitData.left := by
        rw [div_lt_iff₀ hn] at hv0
        simpa [mul_comm] using hv0
      have hpLower : n * A.exitData.left ≤ z (R.position p) := by
        change n * A.exitData.left ≤ n *
          (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position p) - 2))
        have hr := hmid0 (R.position p) hp
        have hnonneg : 0 ≤ (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position p) - 2) :=
          mul_nonneg hdelta (by linarith)
        apply mul_le_mul_of_nonneg_left _ hn.le
        linarith
      have hqLower : n * A.exitData.left ≤ z (R.position q) := by
        change n * A.exitData.left ≤ n *
          (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position q) - 2))
        have hr := hmid0 (R.position q) hq
        have hnonneg : 0 ≤ (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position q) - 2) :=
          mul_nonneg hdelta (by linarith)
        apply mul_le_mul_of_nonneg_left _ hn.le
        linarith
      exact hcn.le.trans (le_min hpLower hqLower)
    · have hv0' : A.exitData.left ≤ c / n := le_of_not_gt hv0
      by_cases hv1 : c / n ≤ A.exitData.right
      · have hbreak := K.faceBoundarySubdivision_parameter_side
          (G := G) f i (some (some v)) hu hui
        have hvalue := edgeMiddleSourceScalar_breakpoint A v hv0' hv1
        have hparamBreak : K.faceEdgeParameterAffine f i
            (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) =
              edgeBreakpointParameter A (some (some v)) := by
          change K.faceEdgeParameterAffine f i
            (K.faceEdgeSourcePoint f i
              (edgeBreakpointParameter A (some (some v)))) = _
          rw [K.faceEdgeParameterAffine_sourcePoint]
        have hbreakValue : z
            (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) = c := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i
              (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) - 2)) = c
          rw [hparamBreak]
          simpa only [n, c, edgeBreakpointParameter] using hvalue
        rcases hbreak with hle | hge
        · right
          apply max_le
          · calc
              z (R.position p) ≤ z
                  (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) :=
                hmono (by rw [hparamBreak]; exact hle _ hp)
              _ = c := hbreakValue
          · calc
              z (R.position q) ≤ z
                  (K.faceBreakpointPoint (G := G) f ⟨i, some (some v)⟩) :=
                hmono (by rw [hparamBreak]; exact hle _ hq)
              _ = c := hbreakValue
        · left
          apply le_min
          · calc
              c = z (K.faceBreakpointPoint (G := G) f
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position p) :=
                hmono (by rw [hparamBreak]; exact hge _ hp)
          · calc
              c = z (K.faceBreakpointPoint (G := G) f
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position q) :=
                hmono (by rw [hparamBreak]; exact hge _ hq)
      · right
        have hcn : n * A.exitData.right < c := by
          have hc : A.exitData.right < c / n := lt_of_not_ge hv1
          rw [lt_div_iff₀ hn] at hc
          simpa [mul_comm] using hc
        have hpUpper : z (R.position p) ≤ n * A.exitData.right := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position p) - 2)) ≤
              n * A.exitData.right
          have hr := hmid1 (R.position p) hp
          have hmul := mul_le_mul_of_nonneg_left
            (show 4 * K.faceEdgeParameterAffine f i (R.position p) - 2 ≤ 1 by
              linarith) hdelta
          apply mul_le_mul_of_nonneg_left _ hn.le
          linarith
        have hqUpper : z (R.position q) ≤ n * A.exitData.right := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine f i (R.position q) - 2)) ≤
              n * A.exitData.right
          have hr := hmid1 (R.position q) hq
          have hmul := mul_le_mul_of_nonneg_left
            (show 4 * K.faceEdgeParameterAffine f i (R.position q) - 2 ≤ 1 by
              linarith) hdelta
          apply mul_le_mul_of_nonneg_left _ hn.le
          linarith
        exact (max_le hpUpper hqUpper).trans hcn.le
  obtain ⟨s, hs, hssegment⟩ :=
    PlaneComplex.exists_face_containing_axis_segment_of_no_vertex
      A.parameterization.source hn.le hab ha hb A.parameterization.source_support
        A.parameterization.source_card_le_two havoid
  let sourceAffine : Plane →ᵃ[ℝ] Plane :=
    K.faceMiddleSourceAffine (G := G) f i
  have hsourceApply (x : Plane) : sourceAffine x = planePoint (z x) 0 := by
    simpa only [sourceAffine, z] using
      K.faceMiddleSourceAffine_apply (G := G) f i x
  have hsourceImage :
      sourceAffine '' R.cellCarrier ({p, q} : Finset R.Vertex) =
        segment ℝ (planePoint a 0) (planePoint b 0) := by
    rw [PlaneComplex.cellCarrier]
    have himage : R.position '' (({p, q} : Finset R.Vertex) : Set R.Vertex) =
        {R.position p, R.position q} := by
      ext x
      simp [eq_comm]
    rw [himage, convexHull_pair, image_segment]
    rw [hsourceApply, hsourceApply]
    rcases le_total (z (R.position p)) (z (R.position q)) with hpzq | hqzp
    · simp [a, b, min_eq_left hpzq, max_eq_right hpzq]
    · rw [segment_symm]
      simp [a, b, min_eq_right hqzp, max_eq_left hqzp]
  refine ⟨s, hs, ?_⟩
  intro x hx
  apply hssegment
  rw [← hsourceImage]
  exact ⟨x, hx, rfl⟩

/-- The canonical face boundary map is affine on every simplex of its finite marked
subdivision. -/
theorem faceBoundaryMap_affineOn_subdivision (f : K.Face) :
    ∀ u ∈ (K.faceBoundarySubdivision (G := G) f).simplexes,
      IsAffineOn (K.faceBoundaryMap (G := G) f)
        ((K.faceBoundarySubdivision (G := G) f).cellCarrier u) := by
  let R := K.faceBoundarySubdivision (G := G) f
  let T := standardTrianglePlaneComplex.oneSkeleton
  intro u hu
  have hsub : R.Subdivides T := K.faceBoundarySubdivision_subdivides (G := G) f
  obtain ⟨s, hs, hus⟩ := hsub.2 u hu
  have hscard : s.card ≤ 2 :=
    standardTrianglePlaneComplex.oneSkeleton_isGraph s hs
  have hucard : u.card ≤ 2 :=
    PlaneComplex.card_le_two_of_cellCarrier_subset_face hu hs hscard hus
  have hupos : 0 < u.card := Finset.card_pos.mpr (R.nonempty_of_mem u hu)
  have huCases : u.card = 1 ∨ u.card = 2 := by omega
  rcases huCases with huone | hutwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp huone
    let g : Plane →ᵃ[ℝ] Plane := AffineMap.const ℝ Plane
      (K.faceBoundaryMap (G := G) f (R.position v))
    refine ⟨g, ?_⟩
    intro p hp
    have hpEq : p = R.position v := by
      simpa [PlaneComplex.cellCarrier] using hp
    subst p
    rfl
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hutwo
    have hspos : 0 < s.card := Finset.card_pos.mpr (T.nonempty_of_mem s hs)
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
      have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
      have hpEq : R.position p = T.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hp
      have hqEq : R.position q = T.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hq
      exact (hpq (R.position_injective (hpEq.trans hqEq.symm))).elim
    · obtain ⟨i, hsi⟩ :=
        IntrinsicTwoComplex.exists_faceStandardEdge_of_standardBoundaryEdge hstwo
      have hui : R.cellCarrier ({p, q} : Finset R.Vertex) ⊆
          standardTrianglePlaneComplex.cellCarrier
            (IntrinsicTwoComplex.faceStandardEdge i) := by
        intro x hx
        have hx' := hus hx
        rw [hsi, IntrinsicTwoComplex.standardFaceEdgeFace_cellCarrier] at hx'
        exact hx'
      rcases K.faceBoundarySubdivision_piece (G := G) f i hu hui with
          hleft | hmiddle | hright
      · exact K.faceBoundaryMap_affineOn_left (G := G) f i hui hleft
      · apply K.faceBoundaryMap_affineOn_middle (G := G) f i
          hui hmiddle.1 hmiddle.2
        exact K.faceBoundarySubdivision_middleSource (G := G) f i hu hui
          (by simp [hpq]) hmiddle.1 hmiddle.2
      · exact K.faceBoundaryMap_affineOn_right (G := G) f i hui hright

/-- The coherent standard-triangle boundary map is genuinely PL on the polygonal frontier. -/
theorem faceBoundaryMap_isPLOnSet (f : K.Face) :
    IsPLOnSet (frontier standardFaceRegion)
      (K.faceBoundaryMap (G := G) f) := by
  let T := standardTrianglePlaneComplex.oneSkeleton
  let R := K.faceBoundarySubdivision (G := G) f
  refine ⟨T, ?_, R, K.faceBoundarySubdivision_subdivides (G := G) f,
    K.faceBoundaryMap_affineOn_subdivision (G := G) f⟩
  calc
    T.support = standardTriangleCircle.carrier :=
      IntrinsicTwoComplex.standardTriangle_oneSkeleton_support
    _ = frontier standardFaceRegion := by
      rw [standardTriangleCircle_carrier]
      simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
