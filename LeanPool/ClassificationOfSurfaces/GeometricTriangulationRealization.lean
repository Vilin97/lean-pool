/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicTriangulation
import LeanPool.ClassificationOfSurfaces.StrongVertexStar
import LeanPool.ClassificationOfSurfaces.TriangleCell

/-!
# Faithful polygonal realization of a geometric triangulation

The local map in this file identifies each three-sided polygon cell with the corresponding
barycentric face.  Its side formula uses the cyclic face order exactly, so adjacent face maps
agree under the signed occurrence pairing.
-/

open Set Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

private theorem orientedEdge_eq_or_eq_flip_of_edge_eq
    {d e : OrientedEdge T.Edge} (h : d.edge = e.edge) :
    d = e ∨ d = e.flip := by
  cases d <;> cases e <;> simp_all [OrientedEdge.edge, OrientedEdge.flip]

/-- A three-sided polygon cell is canonically identified with one closed barycentric face. -/
noncomputable def faceCellHomeomorph (f : T.Triangle) :
    PolygonCell 3 ≃ₜ T.toIntrinsic.ClosedFace f :=
  TriangleCell.cellHomeomorph.trans
    (T.toIntrinsic.facePlaneHomeomorph f).symm

@[simp]
theorem faceVertexEmbedding_eq_cyclic (f : T.Triangle) (i : Fin 3) :
    T.toIntrinsic.faceVertexEmbedding f i =
      T.toIntrinsic.faceVertex f (ZMod.finEquiv 3 i) := by
  rw [← T.toIntrinsic.faceVertexEmbedding_cyclic]
  simp

/-- On cyclic side `i`, the face-cell map is the affine barycentric path from face vertex `i`
to face vertex `i+1`. -/
theorem faceCellHomeomorph_side (f : T.Triangle) (i : Fin 3)
    (r : unitInterval) :
    ((T.faceCellHomeomorph f) (PolygonCell.side i r)).1.1 =
      AffineMap.lineMap (k := ℝ)
        (Pi.single (T.toIntrinsic.faceVertexEmbedding f i) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ)
        (Pi.single (T.toIntrinsic.faceVertexEmbedding f (finRotate 3 i)) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ) r := by
  rw [faceCellHomeomorph, Homeomorph.trans_apply,
    TriangleCell.cellHomeomorph_side,
    T.toIntrinsic.facePlaneHomeomorph_symm_val]
  change T.toIntrinsic.facePlaneInverseAffine f
      (AffineMap.lineMap (Moise.standardTriangleVertex i)
        (Moise.standardTriangleVertex (finRotate 3 i)) (r : ℝ)) = _
  rw [AffineMap.apply_lineMap,
    T.toIntrinsic.facePlaneInverseAffine_standardVertex f i,
    T.toIntrinsic.facePlaneInverseAffine_standardVertex f (finRotate 3 i)]

/-- Recover the geometric triangle represented by an enumerated cyclic face. -/
noncomputable abbrev cyclicFace (f : T.toFiniteCyclicPresentation.Face) : T.Triangle :=
  T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm f

@[simp]
theorem cyclicFace_finiteCyclicFaceEquiv (f : T.Triangle) :
    T.cyclicFace
      (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f) = f :=
  T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm_apply_apply f

@[simp]
theorem finiteCyclicFaceEquiv_cyclicFace
    (f : T.toFiniteCyclicPresentation.Face) :
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv (T.cyclicFace f) = f :=
  T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.apply_symm_apply f

/-- Every polygon appearing in the cyclic presentation of a triangulation has three marked
sides. -/
theorem cyclicBoundaryLength (f : T.toFiniteCyclicPresentation.Face) :
    (T.toFiniteCyclicPresentation.boundary f).length = 3 := by
  rw [← T.finiteCyclicFaceEquiv_cyclicFace f]
  exact (T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_boundary_faceEquiv_length
    (T.cyclicFace f)).trans
      (T.triangleBoundary_length (T.cyclicFace f))

/-- The enumerated polygon for `f`, including its stored side-count type, is homeomorphic to the
corresponding closed geometric face. -/
noncomputable abbrev polygonFaceHomeomorph
    (f : T.toFiniteCyclicPresentation.Face) :
    PolygonCell (T.toFiniteCyclicPresentation.boundary f).length ≃ₜ
      T.toIntrinsic.ClosedFace (T.cyclicFace f) :=
  (PolygonCell.castHomeomorph (T.cyclicBoundaryLength f)).trans
    (T.faceCellHomeomorph (T.cyclicFace f))

/-- The facewise map on the disjoint union of cyclic polygon cells. -/
noncomputable def polygonalPreMap :
    T.toFiniteCyclicPresentation.PolygonalPreRealization → T.realization :=
  fun x => (T.polygonFaceHomeomorph x.1 x.2).1

theorem continuous_polygonalPreMap : Continuous T.polygonalPreMap := by
  apply continuous_sigma
  intro f
  exact continuous_subtype_val.comp (T.polygonFaceHomeomorph f).continuous

/-- The original oriented geometric edge stored at an enumerated boundary occurrence. -/
noncomputable abbrev cyclicOrientedEdge
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence) :
    OrientedEdge T.Edge :=
  T.orientedFaceEdge (T.cyclicFace o.1)
    (ZMod.finEquiv 3 (Fin.cast (T.cyclicBoundaryLength o.1) o.2))

/-- The boundary occurrence belonging to a specified `Fin 3` side of an enumerated face. -/
noncomputable abbrev cyclicOccurrence
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    T.toFiniteCyclicPresentation.BoundaryOccurrence :=
  ⟨f, Fin.cast (T.cyclicBoundaryLength f).symm i⟩

@[simp]
theorem cyclicOccurrence_face
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    (T.cyclicOccurrence f i).1 = f :=
  rfl

@[simp]
theorem cyclicOccurrence_index_cast
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    Fin.cast (T.cyclicBoundaryLength f) (T.cyclicOccurrence f i).2 = i := by
  apply Fin.ext
  rfl

@[simp]
theorem cyclicOrientedEdge_cyclicOccurrence
    (f : T.toFiniteCyclicPresentation.Face) (i : Fin 3) :
    T.cyclicOrientedEdge (T.cyclicOccurrence f i) =
      T.orientedFaceEdge (T.cyclicFace f) (ZMod.finEquiv 3 i) := by
  simp [cyclicOrientedEdge, cyclicOccurrence]

@[simp]
theorem finiteCyclicDartEquiv_cyclicOrientedEdge
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence) :
    T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
        (T.cyclicOrientedEdge o) = o.dart := by
  obtain ⟨p, rfl⟩ :=
    T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv.surjective o
  change T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
      (T.cyclicOrientedEdge
        (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv p)) =
    (T.toFiniteCyclicPresentation.boundary
      (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv p).1).get
        (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv p).2
  rw [T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv_dart]
  congr 1
  unfold GeometricTriangulation.toFiniteSurfaceTriangulation at p
  rcases p with ⟨f, i⟩
  change T.cyclicOrientedEdge
      (T.toFiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv ⟨f, i⟩) =
    (T.triangleBoundary f).get i
  rw [T.triangleBoundary_get]
  simp only [cyclicOrientedEdge, cyclicFace,
    FiniteSurfaceTriangulation.finiteCyclicOccurrenceEquiv]
  congr
  exact T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm_apply_apply f

@[simp]
theorem finiteCyclicDartEquiv_flip (d : OrientedEdge T.Edge) :
    T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d.flip =
      (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d).flip := by
  cases d <;> rfl

@[simp]
theorem orientedEdgeSource_flip (d : OrientedEdge T.Edge) :
    T.orientedEdgeSource d.flip = T.orientedEdgeTarget d := by
  cases d <;> rfl

@[simp]
theorem orientedEdgeTarget_flip (d : OrientedEdge T.Edge) :
    T.orientedEdgeTarget d.flip = T.orientedEdgeSource d := by
  cases d <;> rfl

/-- The enumerated side parameter is carried to the corresponding affine edge parameter. -/
theorem polygonFaceHomeomorph_side
    (f : T.toFiniteCyclicPresentation.Face)
    (i : Fin (T.toFiniteCyclicPresentation.boundary f).length)
    (r : unitInterval) :
    ((T.polygonFaceHomeomorph f) (PolygonCell.side i r)).1.1 =
      AffineMap.lineMap (k := ℝ)
        (Pi.single
          (T.toIntrinsic.faceVertexEmbedding (T.cyclicFace f)
            (Fin.cast (T.cyclicBoundaryLength f) i)) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ)
        (Pi.single
          (T.toIntrinsic.faceVertexEmbedding (T.cyclicFace f)
            (finRotate 3 (Fin.cast (T.cyclicBoundaryLength f) i))) (1 : ℝ) :
          T.toIntrinsic.Vertex → ℝ) r := by
  rw [polygonFaceHomeomorph, Homeomorph.trans_apply,
    PolygonCell.castHomeomorph_side, T.faceCellHomeomorph_side]

/-- The affine endpoints of an enumerated side are the source and target of its original
oriented geometric edge. -/
theorem polygonFaceHomeomorph_side_oriented
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence)
    (r : unitInterval) :
    ((T.polygonFaceHomeomorph o.1) (PolygonCell.side o.2 r)).1.1 =
      AffineMap.lineMap (k := ℝ)
        (Pi.single (T.orientedEdgeSource (T.cyclicOrientedEdge o)) (1 : ℝ) :
          T.Vertex → ℝ)
        (Pi.single (T.orientedEdgeTarget (T.cyclicOrientedEdge o)) (1 : ℝ) :
          T.Vertex → ℝ) r := by
  rw [T.polygonFaceHomeomorph_side]
  rw [cyclicOrientedEdge, T.orientedFaceEdge_source, T.orientedFaceEdge_target,
    T.faceVertexEmbedding_eq_cyclic]
  congr 3
  rw [T.faceVertexEmbedding_eq_cyclic]
  apply congrArg (T.toIntrinsic.faceVertex (T.cyclicFace o.1))
  have hrotate (i : Fin 3) :
      ZMod.finEquiv 3 (finRotate 3 i) = ZMod.finEquiv 3 i + 1 := by
    fin_cases i <;> rfl
  exact hrotate _

/-- Every point of a geometric edge has the affine parameterization determined by either
orientation of that edge. -/
theorem exists_orientedEdgeParameter
    (d : OrientedEdge T.Edge) (x : T.realization)
    (hx : x ∈ T.toIntrinsic.faceCarrier d.edge.1) :
    ∃ r : unitInterval,
      x.1 = AffineMap.lineMap (k := ℝ)
        (Pi.single (T.orientedEdgeSource d) (1 : ℝ) : T.Vertex → ℝ)
        (Pi.single (T.orientedEdgeTarget d) (1 : ℝ) : T.Vertex → ℝ) r := by
  let a := T.orientedEdgeSource d
  let b := T.orientedEdgeTarget d
  have hab : d.edge.1 = {a, b} := by
    cases d with
    | pos e => exact T.edge_eq_pair e
    | neg e =>
        simpa [a, b, orientedEdgeSource, orientedEdgeTarget,
          OrientedEdge.edge, Finset.pair_comm] using T.edge_eq_pair e
  have hne : a ≠ b := by
    cases d with
    | pos e => exact T.edgeSource_ne_edgeTarget e
    | neg e => exact (T.edgeSource_ne_edgeTarget e).symm
  let r : unitInterval :=
    ⟨x.1 b, mem_Icc_of_mem_stdSimplex x.2.1 b⟩
  have hsum : x.1 a + x.1 b = 1 := by
    calc
      x.1 a + x.1 b = ∑ v ∈ d.edge.1, x.1 v := by
        rw [hab]
        simp [hne]
      _ = ∑ v, x.1 v := Finset.sum_subset (Finset.subset_univ d.edge.1)
        (fun v _ hv => hx v hv)
      _ = 1 := x.2.1.2
  refine ⟨r, ?_⟩
  funext v
  rw [AffineMap.lineMap_apply_module]
  by_cases hva : v = a
  · subst v
    simp [a, b, r, hne]
    linarith
  · by_cases hvb : v = b
    · subst v
      simp [a, b, r, hne]
    · have hv : v ∉ d.edge.1 := by
        rw [hab]
        simp [hva, hvb]
      rw [hx v hv]
      simp [a, b, r, hva, hvb]

/-- Compatible signed occurrence pairings have identical images under the facewise geometric
map. -/
theorem polygonalPreMap_pairing_eq
    (pairing : T.toFiniteCyclicPresentation.BoundaryPairing)
    (r : unitInterval) :
    T.polygonalPreMap (pairing.identification.source.point r) =
      T.polygonalPreMap
        (pairing.identification.target.point
          (pairing.identification.parameter r)) := by
  apply Subtype.ext
  change
    ((T.polygonFaceHomeomorph pairing.source.1)
      (PolygonCell.side pairing.source.2 r)).1.1 =
    ((T.polygonFaceHomeomorph pairing.target.1)
      (PolygonCell.side pairing.target.2
        (pairing.direction.homeomorph r))).1.1
  rw [T.polygonFaceHomeomorph_side_oriented,
    T.polygonFaceHomeomorph_side_oriented]
  cases hdirection : pairing.direction with
  | same =>
      have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      have hedge :
          T.cyclicOrientedEdge pairing.target =
            T.cyclicOrientedEdge pairing.source := by
        apply T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv.injective
        rw [T.finiteCyclicDartEquiv_cyclicOrientedEdge,
          T.finiteCyclicDartEquiv_cyclicOrientedEdge, hcompatible]
      simp only [PolygonGluing.ParameterDirection.homeomorph_same_apply]
      rw [hedge]
  | opposite =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      have hedge :
          T.cyclicOrientedEdge pairing.target =
            (T.cyclicOrientedEdge pairing.source).flip := by
        apply T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv.injective
        rw [T.finiteCyclicDartEquiv_cyclicOrientedEdge,
          T.finiteCyclicDartEquiv_flip,
          T.finiteCyclicDartEquiv_cyclicOrientedEdge, hcompatible]
      simp only [PolygonGluing.ParameterDirection.homeomorph_opposite_apply]
      rw [hedge, T.orientedEdgeSource_flip, T.orientedEdgeTarget_flip,
        unitInterval.coe_symm_eq, AffineMap.lineMap_apply_one_sub]

/-- The facewise map is constant on the equivalence relation generated by all compatible
pairings. -/
theorem polygonalPreMap_respects
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {x y : T.toFiniteCyclicPresentation.PolygonalPreRealization}
    (hxy : T.toFiniteCyclicPresentation.PolygonalGluingRel valid x y) :
    T.polygonalPreMap x = T.polygonalPreMap y := by
  induction hxy with
  | rel x y h =>
      cases h with
      | glue identification hidentification r =>
          rcases hidentification with ⟨pairing, rfl⟩
          exact T.polygonalPreMap_pairing_eq pairing r
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Descend the calibrated face maps through the cyclic polygonal quotient. -/
noncomputable def polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    T.toFiniteCyclicPresentation.PolygonalRealization valid → T.realization :=
  Quotient.lift T.polygonalPreMap fun _ _ h => T.polygonalPreMap_respects valid h

@[simp]
theorem polygonalRealizationMap_mk
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (x : T.toFiniteCyclicPresentation.PolygonalPreRealization) :
    T.polygonalRealizationMap valid
        (T.toFiniteCyclicPresentation.polygonalMk valid x) =
      T.polygonalPreMap x :=
  rfl

theorem continuous_polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    Continuous (T.polygonalRealizationMap valid) :=
  T.continuous_polygonalPreMap.quotient_lift fun _ _ h =>
    T.polygonalPreMap_respects valid h

theorem surjective_polygonalPreMap :
    Function.Surjective T.polygonalPreMap := by
  intro x
  have hxall : x ∈ ⋃ f : T.Triangle, T.toIntrinsic.faceCarrier f.1 := by
    rw [← T.toIntrinsic.realization_eq_iUnion_faceCarrier]
    trivial
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxall
  let pf := T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f
  have hface : T.cyclicFace pf = f :=
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.symm_apply_apply f
  let xf : T.toIntrinsic.ClosedFace (T.cyclicFace pf) :=
    ⟨x, hface ▸ hxf⟩
  let z := (T.polygonFaceHomeomorph pf).symm xf
  refine ⟨⟨pf, z⟩, ?_⟩
  change ((T.polygonFaceHomeomorph pf) z).1 = x
  rw [Homeomorph.apply_symm_apply]

theorem surjective_polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    Function.Surjective (T.polygonalRealizationMap valid) := by
  intro x
  obtain ⟨z, rfl⟩ := T.surjective_polygonalPreMap x
  exact ⟨T.toFiniteCyclicPresentation.polygonalMk valid z, rfl⟩

/-- Two distinct occurrences carrying the same oriented geometric edge identify equal side
parameters in the polygonal quotient. -/
theorem polygonalMk_side_eq_of_orientedEdge_eq
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {o p : T.toFiniteCyclicPresentation.BoundaryOccurrence}
    (hop : o ≠ p) (hedge : T.cyclicOrientedEdge p = T.cyclicOrientedEdge o)
    (r : unitInterval) :
    T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
      T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide p).point r) := by
  have hdart : p.dart = o.dart := by
    rw [← T.finiteCyclicDartEquiv_cyclicOrientedEdge,
      ← T.finiteCyclicDartEquiv_cyclicOrientedEdge, hedge]
  have hedgeName : p.edge = o.edge := congrArg FiniteCyclicPresentation.edgeOfDart hdart
  have hsource :=
    T.toFiniteCyclicPresentation.not_isBoundaryEdge_of_ne_of_edge_eq hop hedgeName
  have htarget : ¬T.toFiniteCyclicPresentation.IsBoundaryEdge p.edge := by
    rw [hedgeName]
    exact hsource
  let pairing : T.toFiniteCyclicPresentation.BoundaryPairing :=
    { source := o
      target := p
      source_ne_target := hop
      source_not_boundary := hsource
      target_not_boundary := htarget
      direction := .same
      compatible := hdart }
  have h :=
    T.toFiniteCyclicPresentation.polygonalMk_pairing_eq valid pairing r
  change T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
    T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide p).point r) at h
  exact h

/-- Two distinct occurrences carrying oppositely oriented copies of one geometric edge identify
opposite side parameters in the polygonal quotient. -/
theorem polygonalMk_side_eq_of_orientedEdge_eq_flip
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {o p : T.toFiniteCyclicPresentation.BoundaryOccurrence}
    (hop : o ≠ p)
    (hedge : T.cyclicOrientedEdge p = (T.cyclicOrientedEdge o).flip)
    (r : unitInterval) :
    T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
      T.toFiniteCyclicPresentation.polygonalMk valid
        ((T.toFiniteCyclicPresentation.occurrenceSide p).point
          (unitInterval.symm r)) := by
  have hdart : p.dart = o.dart.flip := by
    calc
      p.dart =
          T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
            (T.cyclicOrientedEdge p) :=
        (T.finiteCyclicDartEquiv_cyclicOrientedEdge p).symm
      _ = T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
          (T.cyclicOrientedEdge o).flip := congrArg _ hedge
      _ = (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
          (T.cyclicOrientedEdge o)).flip :=
        T.finiteCyclicDartEquiv_flip _
      _ = o.dart.flip :=
        congrArg SurfaceCellComplex.SignedDart.flip
          (T.finiteCyclicDartEquiv_cyclicOrientedEdge o)
  have hedgeName : p.edge = o.edge := by
    change FiniteCyclicPresentation.edgeOfDart p.dart =
      FiniteCyclicPresentation.edgeOfDart o.dart
    rw [hdart]
    cases o.dart <;> rfl
  have hsource :=
    T.toFiniteCyclicPresentation.not_isBoundaryEdge_of_ne_of_edge_eq hop hedgeName
  have htarget : ¬T.toFiniteCyclicPresentation.IsBoundaryEdge p.edge := by
    rw [hedgeName]
    exact hsource
  let pairing : T.toFiniteCyclicPresentation.BoundaryPairing :=
    { source := o
      target := p
      source_ne_target := hop
      source_not_boundary := hsource
      target_not_boundary := htarget
      direction := .opposite
      compatible := hdart }
  have h :=
    T.toFiniteCyclicPresentation.polygonalMk_pairing_eq valid pairing r
  change T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide o).point r) =
    T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide p).point
        (unitInterval.symm r)) at h
  exact h

/-- Invert one calibrated face map and include that polygon in the quotient. -/
noncomputable abbrev faceQuotientMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (f : T.toFiniteCyclicPresentation.Face) :
    T.toIntrinsic.ClosedFace (T.cyclicFace f) →
      T.toFiniteCyclicPresentation.PolygonalRealization valid :=
  fun x => T.toFiniteCyclicPresentation.polygonalMk valid
    ⟨f, (T.polygonFaceHomeomorph f).symm x⟩

/-- Transport a closed face along equality of its face name. -/
noncomputable def closedFaceCastHomeomorph
    {f g : T.Triangle} (h : f = g) :
    T.toIntrinsic.ClosedFace f ≃ₜ T.toIntrinsic.ClosedFace g := by
  subst g
  exact Homeomorph.refl _

@[simp]
theorem closedFaceCastHomeomorph_val
    {f g : T.Triangle} (h : f = g)
    (x : T.toIntrinsic.ClosedFace f) :
    (T.closedFaceCastHomeomorph h x).1 = x.1 := by
  subst g
  rfl

theorem continuous_faceQuotientMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (f : T.toFiniteCyclicPresentation.Face) :
    Continuous (T.faceQuotientMap valid f) :=
  T.toFiniteCyclicPresentation.continuous_polygonalMk valid |>.comp
    (continuous_sigmaMk.comp (T.polygonFaceHomeomorph f).symm.continuous)

/-- Changing only the proof-level name of a packed face does not change its inverse quotient
value. -/
theorem faceQuotientMap_congr
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {f g : T.toFiniteCyclicPresentation.Face} (hfg : f = g)
    (x : T.toIntrinsic.ClosedFace (T.cyclicFace f))
    (y : T.toIntrinsic.ClosedFace (T.cyclicFace g))
    (hxy : x.1 = y.1) :
    T.faceQuotientMap valid f x = T.faceQuotientMap valid g y := by
  subst g
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

@[simp]
theorem faceQuotientMap_faceHomeomorph
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (f : T.toFiniteCyclicPresentation.Face)
    (z : PolygonCell (T.toFiniteCyclicPresentation.boundary f).length) :
    T.faceQuotientMap valid f (T.polygonFaceHomeomorph f z) =
      T.toFiniteCyclicPresentation.polygonalMk valid ⟨f, z⟩ := by
  simp [faceQuotientMap]

/-- The two inverse face maps agree in the quotient along a common geometric edge. -/
theorem faceQuotientMap_eq_of_inter_card_two
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    {f g : T.toFiniteCyclicPresentation.Face} (hfg : f ≠ g)
    (hcard : ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1).card = 2)
    (x : T.realization)
    (hxf : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace f).1)
    (hxg : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace g).1) :
    T.faceQuotientMap valid f ⟨x, hxf⟩ =
      T.faceQuotientMap valid g ⟨x, hxg⟩ := by
  let e : T.Edge :=
    ⟨(T.cyclicFace f).1 ∩ (T.cyclicFace g).1, by
      change (T.cyclicFace f).1 ∩ (T.cyclicFace g).1 ∈
        T.faces.biUnion fun t => t.powersetCard 2
      apply Finset.mem_biUnion.mpr
      exact ⟨(T.cyclicFace f).1, (T.cyclicFace f).2,
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hcard⟩⟩⟩
  have hef : e.1 ⊆ (T.cyclicFace f).1 := Finset.inter_subset_left
  have heg : e.1 ⊆ (T.cyclicFace g).1 := Finset.inter_subset_right
  obtain ⟨i, hi⟩ :=
    T.toIntrinsic.exists_faceEdge_eq_of_subset (T.cyclicFace f) e hef
  obtain ⟨j, hj⟩ :=
    T.toIntrinsic.exists_faceEdge_eq_of_subset (T.cyclicFace g) e heg
  let oi : Fin 3 := (ZMod.finEquiv 3).symm i
  let oj : Fin 3 := (ZMod.finEquiv 3).symm j
  have hoedge :
      (T.cyclicOrientedEdge (T.cyclicOccurrence f oi)).edge = e := by
    rw [cyclicOrientedEdge_cyclicOccurrence, T.orientedFaceEdge_edge]
    rw [(ZMod.finEquiv 3).apply_symm_apply i]
    exact hi
  have hpedge :
      (T.cyclicOrientedEdge (T.cyclicOccurrence g oj)).edge = e := by
    rw [cyclicOrientedEdge_cyclicOccurrence, T.orientedFaceEdge_edge]
    rw [(ZMod.finEquiv 3).apply_symm_apply j]
    exact hj
  have hxedge : x ∈ T.toIntrinsic.faceCarrier e.1 := by
    rw [← T.toIntrinsic.faceCarrier_inter]
    exact ⟨hxf, hxg⟩
  obtain ⟨r, hxr⟩ :=
    T.exists_orientedEdgeParameter
      (T.cyclicOrientedEdge (T.cyclicOccurrence f oi)) x
      (hoedge ▸ hxedge)
  have hop : T.cyclicOccurrence f oi ≠ T.cyclicOccurrence g oj := by
    intro hop
    apply hfg
    exact congrArg Sigma.fst hop
  rcases orientedEdge_eq_or_eq_flip_of_edge_eq T
      (hpedge.trans hoedge.symm) with horiented | horiented
  · have hfo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence f oi).1
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) =
          ⟨x, by simpa using hxf⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented]
      exact hxr.symm
    have hfo :
        T.polygonFaceHomeomorph f
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) = ⟨x, hxf⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hfo'
    have hgo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence g oj).1
            (PolygonCell.side (T.cyclicOccurrence g oj).2 r) =
          ⟨x, by simpa using hxg⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented, horiented]
      exact hxr.symm
    have hgo :
        T.polygonFaceHomeomorph g
            (PolygonCell.side (T.cyclicOccurrence g oj).2 r) = ⟨x, hxg⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hgo'
    rw [← hfo, ← hgo, T.faceQuotientMap_faceHomeomorph,
      T.faceQuotientMap_faceHomeomorph]
    exact T.polygonalMk_side_eq_of_orientedEdge_eq valid hop horiented r
  · have hfo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence f oi).1
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) =
          ⟨x, by simpa using hxf⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented]
      exact hxr.symm
    have hfo :
        T.polygonFaceHomeomorph f
            (PolygonCell.side (T.cyclicOccurrence f oi).2 r) = ⟨x, hxf⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hfo'
    have hgo' :
        T.polygonFaceHomeomorph (T.cyclicOccurrence g oj).1
            (PolygonCell.side (T.cyclicOccurrence g oj).2
              (unitInterval.symm r)) =
          ⟨x, by simpa using hxg⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [T.polygonFaceHomeomorph_side_oriented, horiented,
        T.orientedEdgeSource_flip, T.orientedEdgeTarget_flip,
        unitInterval.coe_symm_eq, AffineMap.lineMap_apply_one_sub]
      exact hxr.symm
    have hgo :
        T.polygonFaceHomeomorph g
            (PolygonCell.side (T.cyclicOccurrence g oj).2
              (unitInterval.symm r)) = ⟨x, hxg⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val hgo'
    rw [← hfo, ← hgo, T.faceQuotientMap_faceHomeomorph,
      T.faceQuotientMap_faceHomeomorph]
    exact T.polygonalMk_side_eq_of_orientedEdge_eq_flip valid hop horiented r

private theorem card_inter_eq_two_of_faceAdjacentAtVertex_of_ne
    {v : T.Vertex} {f g : T.Triangle}
    (hfg : f ≠ g)
    (hadj : TriangleFamily.FaceAdjacentAtVertex T.faces v f g) :
    (f.1 ∩ g.1).card = 2 := by
  rcases hadj with ⟨e, hecard, _hve, hef, heg⟩
  have heinter : e ⊆ f.1 ∩ g.1 := by
    intro w hw
    exact Finset.mem_inter.mpr ⟨hef hw, heg hw⟩
  have hlower : 2 ≤ (f.1 ∩ g.1).card := by
    rw [← hecard]
    exact Finset.card_le_card heinter
  have hupper : (f.1 ∩ g.1).card ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ (f.1 ∩ g.1).card := by omega
    have hinterf : f.1 ∩ g.1 = f.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [T.triangle_card f]
        exact hthree)
    have hinterg : f.1 ∩ g.1 = g.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [T.triangle_card g]
        exact hthree)
    exact hfg (Subtype.ext (hinterf.symm.trans hinterg))
  omega

private theorem card_inter_le_two_of_ne
    {f g : T.Triangle} (hfg : f ≠ g) :
    (f.1 ∩ g.1).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ (f.1 ∩ g.1).card := by omega
  have hinterf : f.1 ∩ g.1 = f.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [T.triangle_card f]
      exact hthree)
  have hinterg : f.1 ∩ g.1 = g.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
      rw [T.triangle_card g]
      exact hthree)
  exact hfg (Subtype.ext (hinterf.symm.trans hinterg))

/-- At a fixed vertex, inverse face maps agree across one star-adjacency step. -/
theorem faceQuotientMap_eq_vertexPoint_of_faceAdjacentAtVertex
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (v : T.toIntrinsic.UsedVertex) {f g : T.Triangle}
    (hvf : v.1 ∈ f.1) (hvg : v.1 ∈ g.1)
    (hadj : TriangleFamily.FaceAdjacentAtVertex T.faces v.1 f g) :
    T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvf⟩ =
      T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvg⟩ := by
  by_cases hfg : f = g
  · subst g
    rfl
  · have hpacked :
        T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f ≠
          T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g :=
      T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.injective.ne hfg
    have hcyclic :
        T.cyclicFace (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f) ≠
          T.cyclicFace
            (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g) := by
      rw [T.cyclicFace_finiteCyclicFaceEquiv,
        T.cyclicFace_finiteCyclicFaceEquiv]
      exact hfg
    apply T.faceQuotientMap_eq_of_inter_card_two valid hpacked
      (T.card_inter_eq_two_of_faceAdjacentAtVertex_of_ne hcyclic (by
        simpa only [T.cyclicFace_finiteCyclicFaceEquiv] using hadj))

/-- Strong fixed-star connectivity makes the quotient value of a vertex independent of the
incident face used to compute it. -/
theorem faceQuotientMap_eq_vertexPoint
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (v : T.toIntrinsic.UsedVertex) (f g : T.Triangle)
    (hvf : v.1 ∈ f.1) (hvg : v.1 ∈ g.1) :
    T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvf⟩ =
      T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv g)
        ⟨T.toIntrinsic.vertexPoint v,
          by
            rw [T.cyclicFace_finiteCyclicFaceEquiv,
              T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
            exact hvg⟩ := by
  have hpath := hstar v.1 f g hvf hvg
  induction hpath with
  | refl => rfl
  | tail hpath hstep ih =>
      have hvleft :
          v.1 ∈ _ :=
        TriangleFamily.mem_of_reflTransGen_faceAdjacentAtVertex hvf hpath
      have hvright :
          v.1 ∈ _ :=
        TriangleFamily.mem_right_of_faceAdjacentAtVertex hstep
      exact (ih hvleft).trans
        (T.faceQuotientMap_eq_vertexPoint_of_faceAdjacentAtVertex
          valid v hvleft hvright hstep)

/-- Under strong fixed-star connectivity, inverse face maps agree on every face overlap. -/
theorem faceQuotientMap_eq_of_mem
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (f g : T.toFiniteCyclicPresentation.Face) (x : T.realization)
    (hxf : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace f).1)
    (hxg : x ∈ T.toIntrinsic.faceCarrier (T.cyclicFace g).1) :
    T.faceQuotientMap valid f ⟨x, hxf⟩ =
      T.faceQuotientMap valid g ⟨x, hxg⟩ := by
  by_cases hfg : f = g
  · subst g
    rfl
  have hcyclic : T.cyclicFace f ≠ T.cyclicFace g := by
    intro h
    apply hfg
    calc
      f = T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
          (T.cyclicFace f) := (T.finiteCyclicFaceEquiv_cyclicFace f).symm
      _ = T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
          (T.cyclicFace g) := congrArg _ h
      _ = g := T.finiteCyclicFaceEquiv_cyclicFace g
  by_cases htwo : ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1).card = 2
  · exact T.faceQuotientMap_eq_of_inter_card_two valid hfg htwo x hxf hxg
  have hle : ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1).card ≤ 1 := by
    have :=
      T.card_inter_le_two_of_ne hcyclic
    omega
  have hxinter :
      x ∈ T.toIntrinsic.faceCarrier
        ((T.cyclicFace f).1 ∩ (T.cyclicFace g).1) := by
    rw [← T.toIntrinsic.faceCarrier_inter]
    exact ⟨hxf, hxg⟩
  obtain ⟨v, hxv⟩ :=
    T.toIntrinsic.exists_eq_vertexPoint_of_mem_faceCarrier_of_card_le_one
      (T.cyclicFace f) Finset.inter_subset_left hle hxinter
  have hvf : v.1 ∈ (T.cyclicFace f).1 := by
    apply (T.toIntrinsic.vertexPoint_mem_faceCarrier_iff v _).mp
    rw [← hxv]
    exact hxf
  have hvg : v.1 ∈ (T.cyclicFace g).1 := by
    apply (T.toIntrinsic.vertexPoint_mem_faceCarrier_iff v _).mp
    rw [← hxv]
    exact hxg
  have hvertex := T.faceQuotientMap_eq_vertexPoint valid hstar v
    (T.cyclicFace f) (T.cyclicFace g) hvf hvg
  subst x
  let pf :=
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv (T.cyclicFace f)
  let pg :=
    T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv (T.cyclicFace g)
  let xf' : T.toIntrinsic.ClosedFace (T.cyclicFace pf) :=
    ⟨T.toIntrinsic.vertexPoint v, by
      rw [T.cyclicFace_finiteCyclicFaceEquiv,
        T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
      exact hvf⟩
  let xg' : T.toIntrinsic.ClosedFace (T.cyclicFace pg) :=
    ⟨T.toIntrinsic.vertexPoint v, by
      rw [T.cyclicFace_finiteCyclicFaceEquiv,
        T.toIntrinsic.vertexPoint_mem_faceCarrier_iff]
      exact hvg⟩
  have hmiddle :
      T.faceQuotientMap valid pf xf' =
        T.faceQuotientMap valid pg xg' := by
    exact hvertex
  calc
    T.faceQuotientMap valid f
        ⟨T.toIntrinsic.vertexPoint v, hxf⟩ =
        T.faceQuotientMap valid pf xf' := by
      apply T.faceQuotientMap_congr valid
        (T.finiteCyclicFaceEquiv_cyclicFace f).symm
      rfl
    _ = T.faceQuotientMap valid pg xg' := hmiddle
    _ = T.faceQuotientMap valid g
        ⟨T.toIntrinsic.vertexPoint v, hxg⟩ := by
      apply T.faceQuotientMap_congr valid
        (T.finiteCyclicFaceEquiv_cyclicFace g)
      rfl

/-- Choose one containing face and use its inverse face map. Overlap compatibility makes this
choice immaterial. -/
noncomputable def realizationInverse
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (x : T.realization) :
    T.toFiniteCyclicPresentation.PolygonalRealization valid :=
  let f := T.toIntrinsic.containingFace x
  T.faceQuotientMap valid
    (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
    ⟨x, by
      rw [T.cyclicFace_finiteCyclicFaceEquiv]
      exact T.toIntrinsic.mem_faceCarrier_containingFace x⟩

theorem realizationInverse_eqOn_face
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (f : T.Triangle) (x : T.realization)
    (hxf : x ∈ T.toIntrinsic.faceCarrier f.1) :
    T.realizationInverse valid x =
      T.faceQuotientMap valid
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)
        ⟨x, by
          rw [T.cyclicFace_finiteCyclicFaceEquiv]
          exact hxf⟩ := by
  unfold realizationInverse
  apply T.faceQuotientMap_eq_of_mem valid hstar

theorem continuous_realizationInverse
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    Continuous (T.realizationInverse valid) := by
  let carriers : T.Triangle → Set T.realization :=
    fun f => T.toIntrinsic.faceCarrier f.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hclosed : ∀ f : T.Triangle, IsClosed (carriers f) :=
    fun f => T.toIntrinsic.faceCarrier_closed f.1
  have hlocal : ∀ f : T.Triangle,
      ContinuousOn (T.realizationInverse valid) (carriers f) := by
    intro f
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : T.toIntrinsic.ClosedFace f =>
      T.realizationInverse valid x.1)
    let pf := T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f
    have hface : T.cyclicFace pf = f :=
      T.cyclicFace_finiteCyclicFaceEquiv f
    have hc : Continuous (fun x : T.toIntrinsic.ClosedFace f =>
        T.faceQuotientMap valid pf
          (T.closedFaceCastHomeomorph hface.symm x)) :=
      (T.continuous_faceQuotientMap valid pf).comp
        (T.closedFaceCastHomeomorph hface.symm).continuous
    apply hc.congr
    intro x
    symm
    refine (T.realizationInverse_eqOn_face valid hstar f x.1 x.2).trans ?_
    apply T.faceQuotientMap_congr valid rfl
    exact (T.closedFaceCastHomeomorph_val hface.symm x).symm
  exact hfinite.continuous
    T.toIntrinsic.realization_eq_iUnion_faceCarrier.symm hclosed hlocal

theorem polygonalRealizationMap_realizationInverse
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (x : T.realization) :
    T.polygonalRealizationMap valid (T.realizationInverse valid x) = x := by
  unfold realizationInverse faceQuotientMap
  change
    ((T.polygonFaceHomeomorph
      (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
        (T.toIntrinsic.containingFace x)))
      ((T.polygonFaceHomeomorph
        (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
          (T.toIntrinsic.containingFace x))).symm ⟨x, _⟩)).1 = x
  rw [Homeomorph.apply_symm_apply]

theorem realizationInverse_polygonalRealizationMap
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces)
    (q : T.toFiniteCyclicPresentation.PolygonalRealization valid) :
    T.realizationInverse valid (T.polygonalRealizationMap valid q) = q := by
  induction q using Quotient.inductionOn with
  | _ z =>
      rcases z with ⟨f, z⟩
      have hz :=
        (T.polygonFaceHomeomorph f z).2
      change T.realizationInverse valid (T.polygonFaceHomeomorph f z).1 = _
      rw [T.realizationInverse_eqOn_face valid hstar (T.cyclicFace f)
        (T.polygonFaceHomeomorph f z).1 hz]
      calc
        T.faceQuotientMap valid
            (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv
              (T.cyclicFace f))
            ⟨(T.polygonFaceHomeomorph f z).1, _⟩ =
            T.faceQuotientMap valid f (T.polygonFaceHomeomorph f z) := by
          apply T.faceQuotientMap_congr valid
            (T.finiteCyclicFaceEquiv_cyclicFace f)
          rfl
        _ = T.toFiniteCyclicPresentation.polygonalMk valid ⟨f, z⟩ :=
          T.faceQuotientMap_faceHomeomorph valid f z

/-- The faithful homeomorphism from the cyclic polygonal quotient to the barycentric geometric
realization. -/
noncomputable def polygonalRealizationHomeomorph
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ T.realization where
  toFun := T.polygonalRealizationMap valid
  invFun := T.realizationInverse valid
  left_inv := T.realizationInverse_polygonalRealizationMap valid hstar
  right_inv := T.polygonalRealizationMap_realizationInverse valid
  continuous_toFun := T.continuous_polygonalRealizationMap valid
  continuous_invFun := T.continuous_realizationInverse valid hstar

/-- Existence form used by the classification pipeline. -/
theorem polygonalRealization_homeomorphic
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    Nonempty
      (T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ
        T.realization) :=
  ⟨T.polygonalRealizationHomeomorph valid hstar⟩

/-- For a genuine surface triangulation, fixed-star connectivity follows from the manifold
charts, so the faithful polygonal realization needs no extra combinatorial hypothesis. -/
theorem polygonalRealization_homeomorphic_of_surface
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid) :
    Nonempty
      (T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ
        T.realization) :=
  T.polygonalRealization_homeomorphic valid
    T.faces_isStrongVertexStarConnected

end GeometricTriangulation

section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- The Radó triangulation of a compact Eval surface has connected fixed-vertex stars. -/
theorem compact_eval_surface_geometricTriangulation_isStrongVertexStarConnected :
    TriangleFamily.IsStrongVertexStarConnected
      (compactEvalSurfaceGeometricTriangulation S).faces :=
  (compactEvalSurfaceGeometricTriangulation S).faces_isStrongVertexStarConnected

/-- The Eval-surface triangulation simultaneously carries cyclic validity, dual connectivity,
and the fixed-star connectivity used by the faithful geometric quotient. -/
theorem compact_eval_surface_polygonalRealization_certificates :
    (compactEvalSurfaceFiniteCyclicPresentation S).IsSurfaceValid ∧
      TriangleFamily.IsDualConnected
        (compactEvalSurfaceGeometricTriangulation S).faces ∧
      TriangleFamily.IsStrongVertexStarConnected
        (compactEvalSurfaceGeometricTriangulation S).faces :=
  ⟨compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S,
    (compact_eval_surface_geometricTriangulation_surfaceIncidence S).dual_connected,
    compact_eval_surface_geometricTriangulation_isStrongVertexStarConnected S⟩

/-- The polygonal quotient enumerated from the Radó triangulation is homeomorphic to its honest
barycentric geometric realization. -/
theorem compact_eval_surface_polygonalRealization_homeomorphic :
    Nonempty
      ((compactEvalSurfaceFiniteCyclicPresentation S).PolygonalRealization
          (compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S) ≃ₜ
        (compactEvalSurfaceGeometricTriangulation S).realization) :=
  GeometricTriangulation.polygonalRealization_homeomorphic_of_surface
      (compactEvalSurfaceGeometricTriangulation S)
      (compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S)

/-- Surface-level form of the geometric bridge: the valid polygonal quotient obtained from the
named Radó triangulation is homeomorphic to the original compact Eval surface. -/
theorem compact_eval_surface_polygonalRealization_homeomorphic_surface :
    Nonempty
      ((compactEvalSurfaceFiniteCyclicPresentation S).PolygonalRealization
          (compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S) ≃ₜ S) := by
  exact Nonempty.map
    (fun h ↦ h.trans (compactEvalSurfaceGeometricTriangulation S).homeo)
    (compact_eval_surface_polygonalRealization_homeomorphic S)

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
