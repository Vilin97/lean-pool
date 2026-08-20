/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceBoundary
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceModel

/-!
# Relative polygonal boundary maps for intrinsic faces

The simultaneous intrinsic graph replacement is defined once on the global one-skeleton.  This
file restricts that one map to each closed face, in standard triangle coordinates.  Consequently
two neighboring face extensions will have literally the same boundary values on their shared
edge.  The construction below is topological; the finite conforming subdivision which certifies
that it is PL is kept as a separate obligation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- The closed standard triangle used as the source model for every intrinsic face. -/
abbrev standardFaceRegion : Set Plane := standardTrianglePlaneComplex.support

/-- Its polygonal frontier, as a subtype. -/
abbrev StandardFaceBoundary :=
  {p : Plane // p ∈ frontier standardFaceRegion}

theorem standardFaceBoundary_mem_region (p : StandardFaceBoundary) :
    p.1 ∈ standardFaceRegion :=
  standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset p.2

/-- A point on a standard cyclic side lifts to the corresponding intrinsic edge. -/
theorem facePlaneHomeomorph_symm_mem_edge (t : K.Face) (i : ZMod 3)
    {p : Plane} (hp : p ∈ standardTriangleCircle.edgeSegment i) :
    ((K.facePlaneHomeomorph t).symm
      ⟨p, standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset
        (by
          have hp' : p ∈ standardTriangleCircle.carrier :=
            Set.mem_iUnion.mpr ⟨i, hp⟩
          rw [standardTriangleCircle_carrier] at hp'
          simpa only [standardTrianglePlaneComplex_support] using hp')⟩).1 ∈
      K.faceCarrier (K.faceEdge t i).1 := by
  rw [← K.facePlaneHomeomorph_image_edge t i] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have hpFrontier : p ∈ frontier standardTrianglePlaneComplex.support := by
    have hp' : p ∈ standardTriangleCircle.carrier :=
      Set.mem_iUnion.mpr ⟨i, by simpa only [hxp] using
        (show (K.facePlaneHomeomorph t x).1 ∈
          standardTriangleCircle.edgeSegment i from
          (Set.ext_iff.mp (K.facePlaneHomeomorph_image_edge t i)
            (K.facePlaneHomeomorph t x).1).mp ⟨x, hx, rfl⟩)⟩
    rw [standardTriangleCircle_carrier] at hp'
    simpa only [standardTrianglePlaneComplex_support] using hp'
  have heq : (K.facePlaneHomeomorph t).symm
      ⟨p, standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset
        hpFrontier⟩ = x := by
    apply (K.facePlaneHomeomorph t).injective
    simp only [Homeomorph.apply_symm_apply]
    exact Subtype.ext hxp.symm
  rw [heq]
  exact hx

/-- The inverse standard-face chart sends the standard frontier into the global intrinsic
one-skeleton. -/
theorem facePlaneHomeomorph_symm_mem_oneSkeleton (t : K.Face)
    (p : StandardFaceBoundary) :
    ((K.facePlaneHomeomorph t).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩).1 ∈ K.oneSkeleton := by
  have hpCarrier : p.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using p.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  exact ⟨K.faceEdge t i, K.facePlaneHomeomorph_symm_mem_edge t i hi⟩

/-- The canonical lift of the standard triangular frontier to the global intrinsic
one-skeleton. -/
noncomputable def faceBoundaryLift (t : K.Face) :
    StandardFaceBoundary → K.oneSkeleton :=
  fun p => ⟨((K.facePlaneHomeomorph t).symm
    ⟨p.1, standardFaceBoundary_mem_region p⟩).1,
      K.facePlaneHomeomorph_symm_mem_oneSkeleton t p⟩

theorem continuous_faceBoundaryLift (t : K.Face) :
    Continuous (K.faceBoundaryLift t) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    ((K.facePlaneHomeomorph t).symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))

theorem injective_faceBoundaryLift (t : K.Face) :
    Function.Injective (K.faceBoundaryLift t) := by
  intro p q hpq
  have hval : ((K.facePlaneHomeomorph t).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩).1 =
      ((K.facePlaneHomeomorph t).symm
        ⟨q.1, standardFaceBoundary_mem_region q⟩).1 :=
    congrArg (fun z : K.oneSkeleton => (z.1 : K.realization)) hpq
  have hclosed : (K.facePlaneHomeomorph t).symm
      ⟨p.1, standardFaceBoundary_mem_region p⟩ =
      (K.facePlaneHomeomorph t).symm
        ⟨q.1, standardFaceBoundary_mem_region q⟩ := by
    exact Subtype.ext hval
  have hsource := (K.facePlaneHomeomorph t).symm.injective hclosed
  exact Subtype.ext
    (congrArg (fun z : standardTrianglePlaneComplex.support => (z.1 : Plane)) hsource)

/-- The global graph replacement, expressed on the standard frontier of one intrinsic face.
Outside that frontier the value is deliberately irrelevant. -/
noncomputable def faceBoundaryMap (t : K.Face) (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ frontier standardFaceRegion then
    K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t ⟨p, hp⟩).1
  else 0

@[simp] theorem faceBoundaryMap_apply (t : K.Face) (p : StandardFaceBoundary) :
    K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p.1 =
      K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t p).1 := by
  simp [faceBoundaryMap, p.2]

/-- The canonical face boundary map is continuous on the standard frontier. -/
theorem continuousOn_faceBoundaryMap (t : K.Face) :
    ContinuousOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      (frontier standardFaceRegion) := by
  rw [continuousOn_iff_continuous_restrict]
  have hg : Continuous (fun x : K.oneSkeleton =>
      K.graphReplacementMap hcont hinj D C x.1) :=
    continuousOn_iff_continuous_restrict.mp
      (K.continuousOn_graphReplacementMap_oneSkeleton hcont hinj D C)
  convert hg.comp (K.continuous_faceBoundaryLift t) using 1
  funext p
  exact K.faceBoundaryMap_apply t p

/-- The canonical face boundary map is injective on the standard frontier. -/
theorem faceBoundaryMap_injectiveOn (t : K.Face) :
    Set.InjOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      (frontier standardFaceRegion) := by
  intro p hp q hq hpq
  let p' : StandardFaceBoundary := ⟨p, hp⟩
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  have hpq' :
      K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t p').1 =
        K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q').1 := by
    rw [← K.faceBoundaryMap_apply t p', ← K.faceBoundaryMap_apply t q']
    exact hpq
  have hgraph : K.faceBoundaryLift t p' = K.faceBoundaryLift t q' := by
    apply Subtype.ext
    apply K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C
      (K.faceBoundaryLift t p').2 (K.faceBoundaryLift t q').2
    exact hpq'
  exact congrArg Subtype.val (K.injective_faceBoundaryLift t hgraph)

private theorem faceEdgeCarrier_subset_faceCarrier (t : K.Face) (i : ZMod 3) :
    K.faceCarrier (K.faceEdge t i).1 ⊆ K.faceCarrier t.1 := by
  intro x hx v hvt
  apply hx v
  intro hve
  rw [K.faceEdge_val] at hve
  simp only [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with rfl | rfl
  · exact hvt (K.faceVertex_mem t i)
  · exact hvt (K.faceVertex_mem t (i + 1))

/-- The canonical boundary parameterization has exactly the polygon assembled from the three
global replacement edges as its image. -/
theorem faceBoundaryMap_image_frontier (t : K.Face) :
    K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ''
        frontier standardFaceRegion =
      K.faceReplacementCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    have hpCarrier : p ∈ standardTriangleCircle.carrier := by
      rw [standardTriangleCircle_carrier]
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← K.graphReplacementMap_image_faceCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)
      (e := K.faceEdge t i)]
    refine ⟨(K.faceBoundaryLift t ⟨p, hp⟩).1, ?_, ?_⟩
    · exact K.facePlaneHomeomorph_symm_mem_edge t i hi
    · exact (K.faceBoundaryMap_apply t ⟨p, hp⟩).symm
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [← K.graphReplacementMap_image_faceCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)
      (e := K.faceEdge t i)] at hi
    obtain ⟨x, hx, hxy⟩ := hi
    let x' : K.ClosedFace t := ⟨x, K.faceEdgeCarrier_subset_faceCarrier t i hx⟩
    let p : Plane := (K.facePlaneHomeomorph t x').1
    have hpSide : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← K.facePlaneHomeomorph_image_edge t i]
      exact ⟨x', hx, rfl⟩
    have hpFrontier : p ∈ frontier standardFaceRegion := by
      have hp' : p ∈ standardTriangleCircle.carrier :=
        Set.mem_iUnion.mpr ⟨i, hpSide⟩
      rw [standardTriangleCircle_carrier] at hp'
      simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using hp'
    refine ⟨p, hpFrontier, ?_⟩
    rw [K.faceBoundaryMap_apply t ⟨p, hpFrontier⟩]
    have hlift : (K.faceBoundaryLift t ⟨p, hpFrontier⟩).1 = x := by
      change ((K.facePlaneHomeomorph t).symm
        ⟨p, standardFaceBoundary_mem_region ⟨p, hpFrontier⟩⟩).1 = x
      have heq : (K.facePlaneHomeomorph t).symm
          ⟨p, standardFaceBoundary_mem_region ⟨p, hpFrontier⟩⟩ = x' := by
        apply (K.facePlaneHomeomorph t).injective
        simp only [Homeomorph.apply_symm_apply]
        rfl
      exact congrArg Subtype.val heq
    rw [hlift, hxy]

/-- The same exact image statement, expressed using the extracted polygonal circle. -/
theorem faceBoundaryMap_image_polygon (t : K.Face) :
    K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ''
        frontier standardFaceRegion =
      (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
  rw [K.faceBoundaryMap_image_frontier t, K.facePolygonalCircle_carrier t]

/-! ## A finite source subdivision carrying all boundary breakpoints -/

theorem faceStandardEdge_card (i : ZMod 3) : (faceStandardEdge i).card = 2 := by
  rw [faceStandardEdge]
  apply Finset.card_pair
  exact (ZMod.finEquiv 3).symm.injective.ne
    ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)

/-- A cyclic side of the standard triangle, regarded as an edge of its one-skeleton. -/
noncomputable def standardFaceEdgeFace (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.EdgeFace :=
  ⟨faceStandardEdge i, Finset.mem_filter.mpr ⟨
    standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
      ⟨faceStandardEdge_mem_simplexes i, (faceStandardEdge_card i).le⟩,
    faceStandardEdge_card i⟩⟩

/-- The finite graph enumeration index of a cyclic standard side. -/
noncomputable def standardFaceEdgeIndex (i : ZMod 3) :
    Fin (Fintype.card standardTrianglePlaneComplex.oneSkeleton.EdgeFace) :=
  Classical.choose
    (standardTrianglePlaneComplex.oneSkeleton.exists_edgeAt (standardFaceEdgeFace i))

theorem standardFaceEdgeAt_eq (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.edgeAt (standardFaceEdgeIndex i) =
      standardFaceEdgeFace i :=
  Classical.choose_spec
    (standardTrianglePlaneComplex.oneSkeleton.exists_edgeAt (standardFaceEdgeFace i))

/-- All breakpoints needed on all three sides of one intrinsic face. -/
abbrev FaceBreakpoint (t : K.Face) :=
  Σ i : ZMod 3,
    EdgeBreakpoint (K.replacementArc hcont hinj D C (K.faceEdge t i))

/-- A replacement-edge breakpoint placed on the corresponding oriented standard side. -/
noncomputable def faceBreakpointPoint (t : K.Face)
    (b : FaceBreakpoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) : Plane :=
  K.faceEdgeSourcePoint t b.1
    (edgeBreakpointParameter
      (K.replacementArc hcont hinj D C (K.faceEdge t b.1)) b.2)

theorem faceBreakpointPoint_mem_standardEdge (t : K.Face)
    (b : FaceBreakpoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t b ∈
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge b.1) := by
  apply K.faceEdgeSourcePoint_mem_standardEdge
  exact edgeBreakpointParameter_mem
    (K.replacementArc hcont hinj D C (K.faceEdge t b.1)) b.2

theorem faceBreakpointPoint_mem_standardOneSkeleton
    (t : K.Face)
    (b : FaceBreakpoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) :
    K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t b ∈
      standardTrianglePlaneComplex.oneSkeleton.support := by
  apply standardTrianglePlaneComplex.oneSkeleton.cellCarrier_subset_support
    (standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
      ⟨faceStandardEdge_mem_simplexes b.1, (faceStandardEdge_card b.1).le⟩)
  simpa only [PlaneComplex.oneSkeleton_cellCarrier] using
    K.faceBreakpointPoint_mem_standardEdge t b

/-- The common finite standard-boundary subdivision carrying the spoke joins and every vertex
of every middle polygonal model. -/
noncomputable def faceBoundarySubdivision (t : K.Face) : PlaneComplex :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision
    (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)

theorem faceBoundarySubdivision_subdivides (t : K.Face) :
    (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Subdivides
      standardTrianglePlaneComplex.oneSkeleton :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_subdivides
    (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph

theorem faceBoundarySubdivision_support (t : K.Face) :
    (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).support =
      frontier standardFaceRegion := by
  rw [faceBoundarySubdivision,
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_support_eq
      (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph,
    standardTriangle_oneSkeleton_support, standardTriangleCircle_carrier]
  simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

/-- A standard `Fin 3` corner, typed as a vertex of the opaque one-skeleton object. -/
noncomputable def standardBoundaryVertex (j : Fin 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact j

/-- Every two-vertex simplex of the standard boundary graph is one of its three cyclic sides. -/
theorem exists_faceStandardEdge_of_standardBoundaryEdge
    {s : Finset standardTrianglePlaneComplex.oneSkeleton.Vertex}
    (hcard : s.card = 2) :
    ∃ i : ZMod 3, s = (standardFaceEdgeFace i).1 := by
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hcard
  have hsurj (x : standardTrianglePlaneComplex.oneSkeleton.Vertex) :
      ∃ j : Fin 3, x = standardBoundaryVertex j := by
    change ∃ j : Fin 3, x = j
    exact ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := hsurj v
  obtain ⟨b, hb⟩ := hsurj w
  subst v
  subst w
  fin_cases a <;> fin_cases b
  · exact (hvw rfl).elim
  · refine ⟨0, ?_⟩
    change ({0, 1} : Finset (Fin 3)) = faceStandardEdge 0
    decide
  · refine ⟨2, ?_⟩
    change ({0, 2} : Finset (Fin 3)) = faceStandardEdge 2
    decide
  · refine ⟨0, ?_⟩
    change ({1, 0} : Finset (Fin 3)) = faceStandardEdge 0
    decide
  · exact (hvw rfl).elim
  · refine ⟨1, ?_⟩
    change ({1, 2} : Finset (Fin 3)) = faceStandardEdge 1
    decide
  · refine ⟨2, ?_⟩
    change ({2, 0} : Finset (Fin 3)) = faceStandardEdge 2
    decide
  · refine ⟨1, ?_⟩
    change ({2, 1} : Finset (Fin 3)) = faceStandardEdge 1
    decide
  · exact (hvw rfl).elim

theorem standardFaceEdgeFace_cellCarrier (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.cellCarrier (standardFaceEdgeFace i).1 =
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rfl

/-- The first oriented standard corner, typed as a vertex of the opaque one-skeleton object. -/
noncomputable def faceEdgeFirstBoundaryVertex (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeFirstIndex t i

/-- The second oriented standard corner, typed as a vertex of the opaque one-skeleton object. -/
noncomputable def faceEdgeSecondBoundaryVertex (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.Vertex := by
  change Fin 3
  exact K.faceEdgeSecondIndex t i

@[simp] theorem faceEdgeFirstBoundaryVertex_position (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position (K.faceEdgeFirstBoundaryVertex t i) =
      standardTriangleVertex (K.faceEdgeFirstIndex t i) := rfl

@[simp] theorem faceEdgeSecondBoundaryVertex_position (t : K.Face) (i : ZMod 3) :
    standardTrianglePlaneComplex.oneSkeleton.position (K.faceEdgeSecondBoundaryVertex t i) =
      standardTriangleVertex (K.faceEdgeSecondIndex t i) := rfl

theorem standardFaceEdgeFace_val_eq_boundaryEndpoints (t : K.Face) (i : ZMod 3) :
    (standardFaceEdgeFace i).1 =
      {K.faceEdgeFirstBoundaryVertex t i, K.faceEdgeSecondBoundaryVertex t i} := by
  change faceStandardEdge i =
    {K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i}
  exact K.faceStandardEdge_eq_endpointIndices t i

/-- The arbitrary graph enumeration of a standard side either follows or reverses the global
intrinsic edge orientation. -/
theorem standardFaceEdge_endpoint_order (t : K.Face) (i : ZMod 3) :
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex t i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex t i) ∨
    (standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
        K.faceEdgeSecondBoundaryVertex t i ∧
      standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
        K.faceEdgeFirstBoundaryVertex t i) := by
  let S := standardTrianglePlaneComplex.oneSkeleton
  let j := standardFaceEdgeIndex i
  have hfirst : S.edgeFirst j ∈ (S.edgeAt j).1 := by
    rw [S.edgeAt_eq]
    simp
  have hsecond : S.edgeSecond j ∈ (S.edgeAt j).1 := by
    rw [S.edgeAt_eq]
    simp
  have hedge : (S.edgeAt j).1 = (standardFaceEdgeFace i).1 :=
    congrArg Subtype.val (standardFaceEdgeAt_eq i)
  rw [hedge, K.standardFaceEdgeFace_val_eq_boundaryEndpoints t i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (S.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (S.edgeFirst_ne_edgeSecond j (hfirst.trans hsecond.symm)).elim

/-- The intrinsic edge parameter, pulled back as an ambient affine coordinate on the standard
face plane. -/
noncomputable def faceEdgeParameterAffine (t : K.Face) (i : ZMod 3) :
    Plane →ᵃ[ℝ] ℝ :=
  (K.edgeCoordinateAffine (K.faceEdge t i)).comp (K.facePlaneInverseAffine t)

@[simp] theorem faceEdgeParameterAffine_apply (t : K.Face) (i : ZMod 3) (p : Plane) :
    K.faceEdgeParameterAffine t i p =
      K.facePlaneInverseAffine t p (K.edgeSecond (K.faceEdge t i)) := rfl

theorem faceEdgeParameterAffine_sourcePoint
    (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.faceEdgeParameterAffine t i (K.faceEdgeSourcePoint t i r) = r := by
  exact K.facePlaneInverseAffine_faceEdgeSourcePoint_apply_second t i r

theorem standardFaceEdgeParameter_sourcePoint_of_forward (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint t i r) = r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position t i,
    ← K.faceEdgeSecondBoundaryVertex_position t i,
    ← horient.1, ← horient.2,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_sourcePoint_of_reverse (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i) (r : ℝ) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
        (K.faceEdgeSourcePoint t i r) = 1 - r := by
  rw [faceEdgeSourcePoint]
  rw [← K.faceEdgeFirstBoundaryVertex_position t i,
    ← K.faceEdgeSecondBoundaryVertex_position t i,
    ← horient.2, ← horient.1, ← AffineMap.lineMap_apply_one_sub,
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter_lineMap]

theorem standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
    (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p =
      K.faceEdgeParameterAffine t i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc t i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_forward t i horient,
    K.faceEdgeParameterAffine_sourcePoint]

theorem standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
    (t : K.Face) (i : ZMod 3)
    (horient :
      standardTrianglePlaneComplex.oneSkeleton.edgeFirst (standardFaceEdgeIndex i) =
          K.faceEdgeSecondBoundaryVertex t i ∧
        standardTrianglePlaneComplex.oneSkeleton.edgeSecond (standardFaceEdgeIndex i) =
          K.faceEdgeFirstBoundaryVertex t i)
    {p : Plane} (hp : p ∈ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p =
      1 - K.faceEdgeParameterAffine t i p := by
  rw [← K.faceEdgeSourcePoint_image_Icc t i] at hp
  obtain ⟨r, -, rfl⟩ := hp
  rw [K.standardFaceEdgeParameter_sourcePoint_of_reverse t i horient,
    K.faceEdgeParameterAffine_sourcePoint]

/-- Every face of the marked boundary subdivision lies on one side of every marked parameter,
in the standard graph enumeration coordinate. -/
theorem faceBoundarySubdivision_parameter_side_standard
    (t : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (K.replacementArc hcont hinj D C (K.faceEdge t i)))
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes) :
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            ⟨i, b⟩)) ∨
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i)
          (K.faceBreakpointPoint (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
            ⟨i, b⟩) ≤
        standardTrianglePlaneComplex.oneSkeleton.edgeParameter (standardFaceEdgeIndex i) p) := by
  let S := standardTrianglePlaneComplex.oneSkeleton
  let point := K.faceBreakpointPoint
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let j := standardFaceEdgeIndex i
  have hbCarrier : point ⟨i, b⟩ ∈ S.cellCarrier (S.edgeAt j).1 := by
    rw [show (S.edgeAt j).1 = faceStandardEdge i from
      congrArg Subtype.val (standardFaceEdgeAt_eq i)]
    rw [standardTrianglePlaneComplex.oneSkeleton_cellCarrier]
    exact K.faceBreakpointPoint_mem_standardEdge t ⟨i, b⟩
  have hpoint : point ⟨i, b⟩ =
      AffineMap.lineMap (S.position (S.edgeFirst j)) (S.position (S.edgeSecond j))
        (S.edgeParameter j (point ⟨i, b⟩)) :=
    (S.lineMap_edgeParameter_eq j hbCarrier).symm
  have huArrangement :=
    ((S.markedEdgeArrangement point).mem_subordinateTo_simplexes_iff S).mp hu |>.1
  have hside := S.markedFaceCarrier_parameter_side point
    (⟨i, b⟩ : FaceBreakpoint
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    j (S.edgeParameter j (point ⟨i, b⟩)) hpoint huArrangement
  simpa only [faceBoundarySubdivision, PlaneComplex.markedEdgeSubdivision,
    PlaneComplex.markedEdgeArrangement] using
    (((S.markedEdgeChain point).arrangementMesh.toPlaneComplex
      |>.subordinateTo_cellCarrier S u).symm ▸ hside)

/-- On a subdivision face contained in one standard side, the same side test is exactly the
intrinsic edge parameter test, independent of orientation. -/
theorem faceBoundarySubdivision_parameter_side
    (t : K.Face) (i : ZMod 3)
    (b : EdgeBreakpoint (K.replacementArc hcont hinj D C (K.faceEdge t i)))
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes)
    (hui :
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D)
        (C := C) t).cellCarrier u ⊆
        standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ edgeBreakpointParameter
        (K.replacementArc hcont hinj D C (K.faceEdge t i)) b) ∨
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      edgeBreakpointParameter (K.replacementArc hcont hinj D C (K.faceEdge t i)) b ≤
        K.faceEdgeParameterAffine t i p) := by
  have hside := K.faceBoundarySubdivision_parameter_side_standard t i b hu
  have hmark : K.faceBreakpointPoint
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t ⟨i, b⟩ =
      K.faceEdgeSourcePoint t i
        (edgeBreakpointParameter (K.replacementArc hcont hinj D C (K.faceEdge t i)) b) := rfl
  rcases K.standardFaceEdge_endpoint_order t i with hforward | hreverse
  · have hmarkEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
      t i hforward (K.faceBreakpointPoint_mem_standardEdge t ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        t i hforward (hui hp)
      have hpSide := hle p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_faceEdgeParameter_of_forward
        t i hforward (hui hp)
      have hpSide := hge p hp
      rw [hpEq, hmark, hmarkEq] at hpSide
      exact hpSide
  · have hmarkEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
      t i hreverse (K.faceBreakpointPoint_mem_standardEdge t ⟨i, b⟩)
    rw [hmark, K.faceEdgeParameterAffine_sourcePoint] at hmarkEq
    rcases hside with hle | hge
    · right
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        t i hreverse (hui hp)
      have := hle p hp
      rw [hpEq, hmark, hmarkEq] at this
      linarith
    · left
      intro p hp
      have hpEq := K.standardFaceEdgeParameter_eq_one_sub_faceEdgeParameter_of_reverse
        t i hreverse (hui hp)
      have := hge p hp
      rw [hpEq, hmark, hmarkEq] at this
      linarith

/-- The two spoke joins split every subdivision face on a selected standard side into the
left, middle, or right parameter range. -/
theorem faceBoundarySubdivision_piece
    (t : K.Face) (i : ZMod 3)
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes)
    (hui :
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D)
        (C := C) t).cellCarrier u ⊆
        standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i)) :
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ (1 / 2 : ℝ)) ∨
    ((∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p) ∧
      (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ))) ∨
    (∀ p ∈
        (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
          |>.cellCarrier u,
      (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine t i p) := by
  have hhalf := K.faceBoundarySubdivision_parameter_side t i none hu hui
  have hthree := K.faceBoundarySubdivision_parameter_side t i (some none) hu hui
  change (∀ p ∈ _, K.faceEdgeParameterAffine t i p ≤ (1 / 2 : ℝ)) ∨
      (∀ p ∈ _, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p) at hhalf
  change (∀ p ∈ _, K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ)) ∨
      (∀ p ∈ _, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine t i p) at hthree
  rcases hhalf with hleHalf | hgeHalf
  · exact Or.inl hleHalf
  · rcases hthree with hleThree | hgeThree
    · exact Or.inr (Or.inl ⟨hgeHalf, hleThree⟩)
    · exact Or.inr (Or.inr hgeThree)

/-- Pull an intrinsic affine certificate back through the affine inverse face chart. -/
theorem faceBoundaryMap_affineOn_of_lift
    (t : K.Face) {E : Set Plane} {X : Set K.realization}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hlift : ∀ (p : Plane) (hp : p ∈ E),
      (K.faceBoundaryLift t ⟨p, hfrontier hp⟩).1 ∈ X)
    (haffine : K.IsAffineOnSet
      (K.graphReplacementMap hcont hinj D C) X) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  obtain ⟨a, ha⟩ := haffine
  refine ⟨a.comp (K.facePlaneInverseAffine t), ?_⟩
  intro p hp
  let q : StandardFaceBoundary := ⟨p, hfrontier hp⟩
  have hcoords : (K.faceBoundaryLift t q).1.1 = K.facePlaneInverseAffine t p := by
    exact K.facePlaneHomeomorph_symm_val t
      ⟨p, standardFaceBoundary_mem_region q⟩
  rw [show K.faceBoundaryMap
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t p =
        K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q).1 by
      exact K.faceBoundaryMap_apply t q]
  change K.graphReplacementMap hcont hinj D C (K.faceBoundaryLift t q).1 =
    a (K.facePlaneInverseAffine t p)
  rw [ha (K.faceBoundaryLift t q).1 (hlift p hp), hcoords]

/-- On a left spoke piece of a standard side, the canonical face boundary map is affine. -/
theorem faceBoundaryMap_affineOn_left
    (t : K.Face) (i : ZMod 3) {E : Set Plane}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hle : ∀ p ∈ E, K.faceEdgeParameterAffine t i p ≤ (1 / 2 : ℝ)) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  let e := K.faceEdge t i
  let X : Set K.realization :=
    {x | x ∈ K.faceCarrier e.1 ∧ x.1 (K.edgeSecond e) ≤ (1 / 2 : ℝ)}
  apply K.faceBoundaryMap_affineOn_of_lift t hfrontier (X := X)
  · intro p hp
    let q : StandardFaceBoundary := ⟨p, hfrontier hp⟩
    have hpEdge : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← standard_cellCarrier_faceStandardEdge i]
      exact hside hp
    have hmem := K.facePlaneHomeomorph_symm_mem_edge t i hpEdge
    have hcoords : (K.faceBoundaryLift t q).1.1 = K.facePlaneInverseAffine t p :=
      K.facePlaneHomeomorph_symm_val t ⟨p, standardFaceBoundary_mem_region q⟩
    refine ⟨hmem, ?_⟩
    change (K.faceBoundaryLift t q).1.1 (K.edgeSecond e) ≤ (1 / 2 : ℝ)
    rw [hcoords]
    exact hle p hp
  · apply K.graphReplacementMap_affineOn_left
    · exact fun _ hx => hx.1
    · exact fun _ hx => hx.2

/-- On a right spoke piece of a standard side, the canonical face boundary map is affine. -/
theorem faceBoundaryMap_affineOn_right
    (t : K.Face) (i : ZMod 3) {E : Set Plane}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hge : ∀ p ∈ E, (3 / 4 : ℝ) ≤ K.faceEdgeParameterAffine t i p) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  let e := K.faceEdge t i
  let X : Set K.realization :=
    {x | x ∈ K.faceCarrier e.1 ∧ (3 / 4 : ℝ) ≤ x.1 (K.edgeSecond e)}
  apply K.faceBoundaryMap_affineOn_of_lift t hfrontier (X := X)
  · intro p hp
    let q : StandardFaceBoundary := ⟨p, hfrontier hp⟩
    have hpEdge : p ∈ standardTriangleCircle.edgeSegment i := by
      rw [← standard_cellCarrier_faceStandardEdge i]
      exact hside hp
    have hmem := K.facePlaneHomeomorph_symm_mem_edge t i hpEdge
    have hcoords : (K.faceBoundaryLift t q).1.1 = K.facePlaneInverseAffine t p :=
      K.facePlaneHomeomorph_symm_val t ⟨p, standardFaceBoundary_mem_region q⟩
    refine ⟨hmem, ?_⟩
    change (3 / 4 : ℝ) ≤ (K.faceBoundaryLift t q).1.1 (K.edgeSecond e)
    rw [hcoords]
    exact hge p hp
  · apply K.graphReplacementMap_affineOn_right
    · exact fun _ hx => hx.1
    · exact fun _ hx => hx.2

/-- On a middle piece, affinity follows once its pulled-back source image lies in one face of
the finite polygonal segment model. -/
theorem faceBoundaryMap_affineOn_middle
    (t : K.Face) (i : ZMod 3) {E : Set Plane}
    (hfrontier : E ⊆ frontier standardFaceRegion)
    (hside : E ⊆ standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hmid0 : ∀ p ∈ E, (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p)
    (hmid1 : ∀ p ∈ E, K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ))
    (hsource : ∃ s ∈
        (K.replacementArc hcont hinj D C (K.faceEdge t i)).parameterization.source.simplexes,
      Set.MapsTo (fun p : Plane =>
        edgeMiddleSourceMap (K.replacementArc hcont hinj D C (K.faceEdge t i))
          (K.facePlaneInverseAffine t p)) E
        ((K.replacementArc hcont hinj D C (K.faceEdge t i))
          |>.parameterization.source.cellCarrier s)) :
    IsAffineOn
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) E := by
  let e := K.faceEdge t i
  let A := K.replacementArc hcont hinj D C e
  let lift : {p : Plane // p ∈ E} → K.realization := fun p =>
    (K.faceBoundaryLift t ⟨p.1, hfrontier p.2⟩).1
  let X : Set K.realization := Set.range lift
  apply K.faceBoundaryMap_affineOn_of_lift t hfrontier (X := X)
  · intro p hp
    exact ⟨⟨p, hp⟩, rfl⟩
  · apply K.graphReplacementMap_affineOn_middle
    · rintro x ⟨p, rfl⟩
      have hpEdge : p.1 ∈ standardTriangleCircle.edgeSegment i := by
        rw [← standard_cellCarrier_faceStandardEdge i]
        exact hside p.2
      exact K.facePlaneHomeomorph_symm_mem_edge t i hpEdge
    · rintro x ⟨p, rfl⟩
      have hcoords : (lift p).1 = K.facePlaneInverseAffine t p.1 := by
        exact K.facePlaneHomeomorph_symm_val t
          ⟨p.1, standardFaceBoundary_mem_region ⟨p.1, hfrontier p.2⟩⟩
      change (1 / 2 : ℝ) ≤ (lift p).1 (K.edgeSecond e)
      rw [hcoords]
      exact hmid0 p.1 p.2
    · rintro x ⟨p, rfl⟩
      have hcoords : (lift p).1 = K.facePlaneInverseAffine t p.1 := by
        exact K.facePlaneHomeomorph_symm_val t
          ⟨p.1, standardFaceBoundary_mem_region ⟨p.1, hfrontier p.2⟩⟩
      change (lift p).1 (K.edgeSecond e) ≤ (3 / 4 : ℝ)
      rw [hcoords]
      exact hmid1 p.1 p.2
    · obtain ⟨s, hs, hmaps⟩ := hsource
      refine ⟨s, hs, ?_⟩
      rintro x ⟨p, rfl⟩
      have hcoords : (lift p).1 = K.facePlaneInverseAffine t p.1 := by
        exact K.facePlaneHomeomorph_symm_val t
          ⟨p.1, standardFaceBoundary_mem_region ⟨p.1, hfrontier p.2⟩⟩
      change edgeMiddleSourceMap A (lift p).1 ∈ A.parameterization.source.cellCarrier s
      rw [hcoords]
      exact hmaps p.2

/-- The marked middle-model vertices ensure that the pulled-back image of a two-vertex
subdivision face is contained in one face of the finite segment model. -/
theorem faceBoundarySubdivision_middleSource
    (t : K.Face) (i : ZMod 3)
    {u : Finset
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).Vertex}
    (hu : u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes)
    (hui :
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D)
        (C := C) t).cellCarrier u ⊆
        standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i))
    (hcard : u.card = 2)
    (hmid0 : ∀ p ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
        |>.cellCarrier u,
      (1 / 2 : ℝ) ≤ K.faceEdgeParameterAffine t i p)
    (hmid1 : ∀ p ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
        |>.cellCarrier u,
      K.faceEdgeParameterAffine t i p ≤ (3 / 4 : ℝ)) :
    ∃ s ∈
        (K.replacementArc hcont hinj D C (K.faceEdge t i)).parameterization.source.simplexes,
      Set.MapsTo (fun p : Plane =>
        edgeMiddleSourceMap (K.replacementArc hcont hinj D C (K.faceEdge t i))
          (K.facePlaneInverseAffine t p))
        ((K.faceBoundarySubdivision
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).cellCarrier u)
        ((K.replacementArc hcont hinj D C (K.faceEdge t i))
          |>.parameterization.source.cellCarrier s) := by
  let R := K.faceBoundarySubdivision
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let A := K.replacementArc hcont hinj D C (K.faceEdge t i)
  let n : ℝ := A.data.resolvedWalk.length
  let z : Plane → ℝ := fun p => n *
    (A.exitData.left + (A.exitData.right - A.exitData.left) *
      (4 * K.faceEdgeParameterAffine t i p - 2))
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast A.resolvedWalk_length_pos
  have hdelta : 0 ≤ A.exitData.right - A.exitData.left :=
    sub_nonneg.mpr A.exitData.left_lt_right.le
  have hmono {p q : Plane}
      (hpq : K.faceEdgeParameterAffine t i p ≤ K.faceEdgeParameterAffine t i q) :
      z p ≤ z q := by
    change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i p - 2)) ≤
      n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i q - 2))
    apply mul_le_mul_of_nonneg_left _ hn.le
    have hr : 4 * K.faceEdgeParameterAffine t i p - 2 ≤
        4 * K.faceEdgeParameterAffine t i q - 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hr hdelta
    linarith
  have hzBounds {p : Plane} (hp : p ∈ R.cellCarrier u) : z p ∈ Set.Icc 0 n := by
    have ht0 := hmid0 p hp
    have ht1 := hmid1 p hp
    have hr0 : 0 ≤ 4 * K.faceEdgeParameterAffine t i p - 2 := by linarith
    have hr1 : 4 * K.faceEdgeParameterAffine t i p - 2 ≤ 1 := by linarith
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
  have zLower {r : Plane} (hr : r ∈ R.cellCarrier ({p, q} : Finset R.Vertex)) :
      n * A.exitData.left ≤ z r := by
    change n * A.exitData.left ≤ n *
      (A.exitData.left + (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i r - 2))
    have hnonneg : 0 ≤ (A.exitData.right - A.exitData.left) *
        (4 * K.faceEdgeParameterAffine t i r - 2) :=
      mul_nonneg hdelta (by linarith [hmid0 r hr])
    apply mul_le_mul_of_nonneg_left _ hn.le
    linarith
  have zUpper {r : Plane} (hr : r ∈ R.cellCarrier ({p, q} : Finset R.Vertex)) :
      z r ≤ n * A.exitData.right := by
    change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
      (4 * K.faceEdgeParameterAffine t i r - 2)) ≤ n * A.exitData.right
    have hmul := mul_le_mul_of_nonneg_left
      (show 4 * K.faceEdgeParameterAffine t i r - 2 ≤ 1 by linarith [hmid1 r hr]) hdelta
    apply mul_le_mul_of_nonneg_left _ hn.le
    linarith
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
      exact hcn.le.trans (le_min (zLower hp) (zLower hq))
    · have hv0' : A.exitData.left ≤ c / n := le_of_not_gt hv0
      by_cases hv1 : c / n ≤ A.exitData.right
      · have hbreak := K.faceBoundarySubdivision_parameter_side t i
          (some (some v)) hu hui
        have hvalue := edgeMiddleSourceScalar_breakpoint A v hv0' hv1
        have hparamBreak : K.faceEdgeParameterAffine t i
            (K.faceBreakpointPoint
              (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                ⟨i, some (some v)⟩) =
              edgeBreakpointParameter A (some (some v)) := by
          change K.faceEdgeParameterAffine t i
            (K.faceEdgeSourcePoint t i (edgeBreakpointParameter A (some (some v)))) = _
          rw [K.faceEdgeParameterAffine_sourcePoint]
        have hbreakValue : z (K.faceBreakpointPoint
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
              ⟨i, some (some v)⟩) = c := by
          change n * (A.exitData.left + (A.exitData.right - A.exitData.left) *
            (4 * K.faceEdgeParameterAffine t i
              (K.faceBreakpointPoint
                (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                  ⟨i, some (some v)⟩) - 2)) = c
          rw [hparamBreak]
          simpa only [n, c, edgeBreakpointParameter] using hvalue
        rcases hbreak with hle | hge
        · right
          apply max_le
          · calc
              z (R.position p) ≤ z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hmono (by
                      rw [hparamBreak]
                      exact hle _ hp)
              _ = c := hbreakValue
          · calc
              z (R.position q) ≤ z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hmono (by
                      rw [hparamBreak]
                      exact hle _ hq)
              _ = c := hbreakValue
        · left
          apply le_min
          · calc
              c = z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position p) := hmono (by
                rw [hparamBreak]
                exact hge _ hp)
          · calc
              c = z (K.faceBreakpointPoint
                  (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
                    ⟨i, some (some v)⟩) := hbreakValue.symm
              _ ≤ z (R.position q) := hmono (by
                rw [hparamBreak]
                exact hge _ hq)
      · right
        have hcn : n * A.exitData.right < c := by
          have hc : A.exitData.right < c / n := lt_of_not_ge hv1
          rw [lt_div_iff₀ hn] at hc
          simpa [mul_comm] using hc
        exact (max_le (zUpper hp) (zUpper hq)).trans hcn.le
  obtain ⟨s, hs, hssegment⟩ := PlaneComplex.exists_face_containing_axis_segment_of_no_vertex
    A.parameterization.source hn.le hab ha hb A.parameterization.source_support
      A.parameterization.source_card_le_two havoid
  let sourceAffine : Plane →ᵃ[ℝ] Plane :=
    (edgeMiddleSourceMap A).comp (K.facePlaneInverseAffine t)
  have hsourceApply (x : Plane) : sourceAffine x = planePoint (z x) 0 := by
    simp only [sourceAffine, AffineMap.comp_apply, edgeMiddleSourceMap_apply]
    rfl
  have hsourceImage : sourceAffine '' R.cellCarrier ({p, q} : Finset R.Vertex) =
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

/-- The canonical face boundary map is affine on every face of its common finite marked
subdivision. -/
theorem faceBoundaryMap_affineOn_subdivision (t : K.Face) :
    ∀ u ∈
      (K.faceBoundarySubdivision (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).simplexes,
      IsAffineOn
        (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
        ((K.faceBoundarySubdivision
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).cellCarrier u) := by
  let R := K.faceBoundarySubdivision
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  let S := standardTrianglePlaneComplex.oneSkeleton
  intro u hu
  have hsub : R.Subdivides S := K.faceBoundarySubdivision_subdivides t
  obtain ⟨s, hs, hus⟩ := hsub.2 u hu
  have hscard : s.card ≤ 2 := standardTrianglePlaneComplex.oneSkeleton_isGraph s hs
  have hucard : u.card ≤ 2 :=
    PlaneComplex.card_le_two_of_cellCarrier_subset_face hu hs hscard hus
  have hupos : 0 < u.card := Finset.card_pos.mpr (R.nonempty_of_mem u hu)
  have huCases : u.card = 1 ∨ u.card = 2 := by omega
  rcases huCases with huone | hutwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp huone
    let g : Plane →ᵃ[ℝ] Plane := AffineMap.const ℝ Plane
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
        (R.position v))
    refine ⟨g, ?_⟩
    intro p hp
    have hp' := hus hp
    have hpEq : p = R.position v := by
      simpa [PlaneComplex.cellCarrier] using hp
    subst p
    rfl
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hutwo
    have hspos : 0 < s.card := Finset.card_pos.mpr (S.nonempty_of_mem s hs)
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hp : R.position p ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨p, by simp, rfl⟩
      have hq : R.position q ∈ R.cellCarrier ({p, q} : Finset R.Vertex) :=
        subset_convexHull ℝ _ ⟨q, by simp, rfl⟩
      have hpEq : R.position p = S.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hp
      have hqEq : R.position q = S.position v := by
        simpa [PlaneComplex.cellCarrier] using hus hq
      exact (hpq (R.position_injective (hpEq.trans hqEq.symm))).elim
    · obtain ⟨i, hsi⟩ := exists_faceStandardEdge_of_standardBoundaryEdge hstwo
      have hui : R.cellCarrier ({p, q} : Finset R.Vertex) ⊆
          standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
        intro x hx
        have hx' := hus hx
        rw [hsi, standardFaceEdgeFace_cellCarrier] at hx'
        exact hx'
      have hfrontier : R.cellCarrier ({p, q} : Finset R.Vertex) ⊆
          frontier standardFaceRegion := by
        intro x hx
        have hxSupport := R.cellCarrier_subset_support hu hx
        rw [K.faceBoundarySubdivision_support t] at hxSupport
        exact hxSupport
      rcases K.faceBoundarySubdivision_piece t i hu hui with hleft | hmiddle | hright
      · exact K.faceBoundaryMap_affineOn_left t i hfrontier hui hleft
      · apply K.faceBoundaryMap_affineOn_middle t i hfrontier hui hmiddle.1 hmiddle.2
        exact K.faceBoundarySubdivision_middleSource t i hu hui
          (by simp [hpq]) hmiddle.1 hmiddle.2
      · exact K.faceBoundaryMap_affineOn_right t i hfrontier hui hright

/-- The canonical standard-triangle boundary map is genuinely PL on the polygonal frontier. -/
theorem faceBoundaryMap_isPLOnSet (t : K.Face) :
    IsPLOnSet (frontier standardFaceRegion)
      (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) := by
  let S := standardTrianglePlaneComplex.oneSkeleton
  let R := K.faceBoundarySubdivision
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  refine ⟨S, ?_, R, K.faceBoundarySubdivision_subdivides t,
    K.faceBoundaryMap_affineOn_subdivision t⟩
  calc
    S.support = standardTriangleCircle.carrier := standardTriangle_oneSkeleton_support
    _ = frontier standardFaceRegion := by
      rw [standardTriangleCircle_carrier]
      simp only [standardFaceRegion, standardTrianglePlaneComplex_support]

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
