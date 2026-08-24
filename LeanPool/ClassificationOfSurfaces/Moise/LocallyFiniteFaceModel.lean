/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteFaceBoundary
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceModel

/-!
# Standard plane models for locally finite faces

A maximal face of a `LocallyFiniteTriangleComplex` is already parametrized by a standard
simplex on its three literal global vertices. This file reindexes those coordinates by the
chosen cyclic `Fin 3` ordering and identifies the result with the standard closed plane
triangle. The cyclic sides are carried exactly to the corresponding standard polygon sides.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (K : LocallyFiniteTriangleComplex S)

/-- The closed standard triangle used as the source model for every locally finite face. -/
abbrev standardFaceRegion : Set Plane := standardTrianglePlaneComplex.support

/-- The frontier of the standard source triangle, as a subtype. -/
abbrev StandardFaceBoundary :=
  {p : Plane // p ∈ frontier standardFaceRegion}

theorem standardFaceBoundary_mem_region (p : StandardFaceBoundary) :
    p.1 ∈ standardFaceRegion :=
  standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset p.2

/-- One closed maximal face in its native simplex coordinates. -/
abbrev ClosedFace (f : K.Face) := stdSimplex ℝ {v // v ∈ K.faceVertices f}

/-- Reindex native face coordinates by the chosen cyclic `Fin 3` ordering. -/
noncomputable def faceReindexToStandard (f : K.Face) (x : K.ClosedFace f) :
    stdSimplex ℝ (Fin 3) := by
  refine ⟨fun i ↦ x (K.faceVertexEquiv f i), ?_, ?_⟩
  · exact fun i ↦ x.2.1 _
  · exact (K.faceVertexEquiv f).sum_comp (fun v ↦ x v) |>.trans x.2.2

/-- Undo the cyclic coordinate reindexing. -/
noncomputable def faceReindexFromStandard (f : K.Face) (z : stdSimplex ℝ (Fin 3)) :
    K.ClosedFace f := by
  refine ⟨fun v ↦ z ((K.faceVertexEquiv f).symm v), ?_, ?_⟩
  · exact fun v ↦ z.2.1 _
  · exact (K.faceVertexEquiv f).symm.sum_comp (fun i ↦ z i) |>.trans z.2.2

@[simp] theorem faceReindexFromStandard_toStandard (f : K.Face)
    (x : K.ClosedFace f) :
    K.faceReindexFromStandard f (K.faceReindexToStandard f x) = x := by
  apply Subtype.ext
  funext v
  change x (K.faceVertexEquiv f ((K.faceVertexEquiv f).symm v)) = x v
  rw [(K.faceVertexEquiv f).apply_symm_apply]

@[simp] theorem faceReindexToStandard_fromStandard (f : K.Face)
    (z : stdSimplex ℝ (Fin 3)) :
    K.faceReindexToStandard f (K.faceReindexFromStandard f z) = z := by
  apply Subtype.ext
  funext i
  change z ((K.faceVertexEquiv f).symm (K.faceVertexEquiv f i)) = z i
  rw [(K.faceVertexEquiv f).symm_apply_apply]

theorem continuous_faceReindexToStandard (f : K.Face) :
    Continuous (K.faceReindexToStandard f) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i ↦
    (continuous_apply (K.faceVertexEquiv f i)).comp continuous_subtype_val

theorem continuous_faceReindexFromStandard (f : K.Face) :
    Continuous (K.faceReindexFromStandard f) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun v ↦
    (continuous_apply ((K.faceVertexEquiv f).symm v)).comp continuous_subtype_val

/-- Native face coordinates are canonically homeomorphic to `stdSimplex ℝ (Fin 3)`. -/
noncomputable def faceReindexHomeomorph (f : K.Face) :
    K.ClosedFace f ≃ₜ stdSimplex ℝ (Fin 3) where
  toFun := K.faceReindexToStandard f
  invFun := K.faceReindexFromStandard f
  left_inv := K.faceReindexFromStandard_toStandard f
  right_inv := K.faceReindexToStandard_fromStandard f
  continuous_toFun := K.continuous_faceReindexToStandard f
  continuous_invFun := K.continuous_faceReindexFromStandard f

/-- Insert a standard simplex point into the one-face intrinsic realization used by the
standard plane triangle complex. -/
noncomputable def standardSimplexToRealization (z : stdSimplex ℝ (Fin 3)) :
    standardTrianglePlaneComplex.toIntrinsic.realization :=
  ⟨z.1, z.2, ⟨Finset.univ, standardTriangle_univ_mem_cells, by simp⟩⟩

/-- Forget the vacuous one-face support witness in the standard intrinsic realization. -/
noncomputable def standardRealizationToSimplex
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) :
    stdSimplex ℝ (Fin 3) :=
  ⟨z.1, z.2.1⟩

@[simp] theorem standardRealizationToSimplex_toRealization (z : stdSimplex ℝ (Fin 3)) :
    standardRealizationToSimplex (standardSimplexToRealization z) = z := rfl

@[simp] theorem standardSimplexToRealization_toSimplex
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) :
    standardSimplexToRealization (standardRealizationToSimplex z) = z := by
  apply Subtype.ext
  rfl

/-- The standard simplex and the canonical intrinsic realization of the standard triangle are
the same topological simplex. -/
noncomputable def standardSimplexRealizationHomeomorph :
    stdSimplex ℝ (Fin 3) ≃ₜ standardTrianglePlaneComplex.toIntrinsic.realization where
  toFun := standardSimplexToRealization
  invFun := standardRealizationToSimplex
  left_inv := standardRealizationToSimplex_toRealization
  right_inv := standardSimplexToRealization_toSimplex
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- A cyclic face edge is contained in the face which names it. -/
theorem faceEdge_subset_faceVertices (f : K.Face) (i : ZMod 3) :
    (K.faceEdge f i).1 ⊆ K.faceVertices f := by
  rw [K.faceEdge_val f i]
  exact Finset.insert_subset_iff.mpr
    ⟨K.faceVertex_mem f i, Finset.singleton_subset_iff.mpr
      (K.faceVertex_mem f (i + 1))⟩

theorem edgeFirst_faceEdge_mem_face (f : K.Face) (i : ZMod 3) :
    K.edgeFirst (K.faceEdge f i) ∈ K.faceVertices f :=
  K.faceEdge_subset_faceVertices f i (K.edgeFirst_mem (K.faceEdge f i))

theorem edgeSecond_faceEdge_mem_face (f : K.Face) (i : ZMod 3) :
    K.edgeSecond (K.faceEdge f i) ∈ K.faceVertices f :=
  K.faceEdge_subset_faceVertices f i (K.edgeSecond_mem (K.faceEdge f i))

/-- The standard plane realization of one locally finite closed face. -/
noncomputable def facePlaneHomeomorph (f : K.Face) :
    K.ClosedFace f ≃ₜ standardTrianglePlaneComplex.support :=
  (K.faceReindexHomeomorph f).trans
    (standardSimplexRealizationHomeomorph.trans
      (standardTrianglePlaneComplex.realizationHomeomorph
        standardTrianglePlaneComplex_pure))

/-- The chosen ordering of a locally finite face, viewed in the global vertex type. -/
noncomputable def faceVertexEmbedding (f : K.Face) : Fin 3 ↪ K.Vertex where
  toFun j := (K.faceVertexEquiv f j).1
  inj' := fun _ _ h ↦ (K.faceVertexEquiv f).injective (Subtype.ext h)

/-- The standard corner corresponding to the globally chosen first endpoint of a face edge. -/
noncomputable def faceEdgeFirstIndex (f : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv f).symm
    ⟨K.edgeFirst (K.faceEdge f i), K.edgeFirst_faceEdge_mem_face f i⟩

/-- The standard corner corresponding to the globally chosen second endpoint of a face edge. -/
noncomputable def faceEdgeSecondIndex (f : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv f).symm
    ⟨K.edgeSecond (K.faceEdge f i), K.edgeSecond_faceEdge_mem_face f i⟩

@[simp] theorem faceVertexEmbedding_faceEdgeFirstIndex (f : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding f (K.faceEdgeFirstIndex f i) =
      K.edgeFirst (K.faceEdge f i) := by
  change ((K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _)).1 = _
  rw [(K.faceVertexEquiv f).apply_symm_apply]

@[simp] theorem faceVertexEmbedding_faceEdgeSecondIndex (f : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding f (K.faceEdgeSecondIndex f i) =
      K.edgeSecond (K.faceEdge f i) := by
  change ((K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _)).1 = _
  rw [(K.faceVertexEquiv f).apply_symm_apply]

/-- The two standard indices of cyclic side `i`, ordered by the global abstract edge. -/
theorem faceStandardEdge_eq_endpointIndices (f : K.Face) (i : ZMod 3) :
    IntrinsicTwoComplex.faceStandardEdge i =
      {K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} := by
  rcases K.faceEdge_endpoint_order f i with hforward | hreverse
  · have hfirst : K.faceEdgeFirstIndex f i = (ZMod.finEquiv 3).symm i := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hforward.1
    have hsecond : K.faceEdgeSecondIndex f i =
        (ZMod.finEquiv 3).symm (i + 1) := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hforward.2
    simp [IntrinsicTwoComplex.faceStandardEdge, hfirst, hsecond]
  · have hfirst : K.faceEdgeFirstIndex f i =
        (ZMod.finEquiv 3).symm (i + 1) := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hreverse.1
    have hsecond : K.faceEdgeSecondIndex f i = (ZMod.finEquiv 3).symm i := by
      apply (K.faceVertexEquiv f).injective
      change (K.faceVertexEquiv f) ((K.faceVertexEquiv f).symm _) = _
      rw [(K.faceVertexEquiv f).apply_symm_apply]
      exact Subtype.ext hreverse.2
    rw [IntrinsicTwoComplex.faceStandardEdge, hfirst, hsecond]
    exact Finset.pair_comm _ _

/-- The standard source point on a face side, oriented by the global edge ordering. -/
noncomputable def faceEdgeSourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) : Plane :=
  AffineMap.lineMap
    (standardTriangleVertex (K.faceEdgeFirstIndex f i))
    (standardTriangleVertex (K.faceEdgeSecondIndex f i)) r

/-- The affine barycentric coordinate along the globally oriented standard side. -/
noncomputable def faceEdgeParameterAffine (f : K.Face) (i : ZMod 3) :
    Plane →ᵃ[ℝ] ℝ :=
  (LinearMap.proj (K.faceEdgeSecondIndex f i)).toAffineMap.comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

@[simp] theorem faceEdgeParameterAffine_sourcePoint
    (f : K.Face) (i : ZMod 3) (r : ℝ) :
    K.faceEdgeParameterAffine f i (K.faceEdgeSourcePoint f i r) = r := by
  have hfirst := standardTrianglePlaneComplex.faceCoords_position
    standardTriangleMeshFace
    (v := K.faceEdgeFirstIndex f i) (by
      change K.faceEdgeFirstIndex f i ∈ (Finset.univ : Finset (Fin 3)); simp)
  have hsecond := standardTrianglePlaneComplex.faceCoords_position
    standardTriangleMeshFace
    (v := K.faceEdgeSecondIndex f i) (by
      change K.faceEdgeSecondIndex f i ∈ (Finset.univ : Finset (Fin 3)); simp)
  have hne : K.faceEdgeFirstIndex f i ≠ K.faceEdgeSecondIndex f i := by
    intro h
    apply K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
    rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
      ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, h]
  rw [standardTrianglePlaneComplex_position] at hfirst hsecond
  rw [faceEdgeParameterAffine, faceEdgeSourcePoint, AffineMap.comp_apply,
    AffineMap.apply_lineMap, hfirst, hsecond]
  simp [AffineMap.lineMap_apply_module, hne]

theorem faceEdgeSourcePoint_mem_standardEdge (f : K.Face) (i : ZMod 3)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint f i r ∈
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices f i, PlaneComplex.cellCarrier]
  rw [show standardTriangleVertex ''
      (({K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex f i),
        standardTriangleVertex (K.faceEdgeSecondIndex f i)} by
    ext p; simp [eq_comm]]
  rw [convexHull_pair, segment_eq_image_lineMap]
  exact ⟨r, hr, rfl⟩

theorem faceEdgeSourcePoint_image_Icc (f : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint f i '' Set.Icc (0 : ℝ) 1 =
      standardTrianglePlaneComplex.cellCarrier
        (IntrinsicTwoComplex.faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices f i, PlaneComplex.cellCarrier]
  rw [show standardTriangleVertex ''
      (({K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex f i),
        standardTriangleVertex (K.faceEdgeSecondIndex f i)} by
    ext p; simp [eq_comm]]
  rw [convexHull_pair, segment_eq_image_lineMap]
  rfl

/-- Native face-simplex points supported on cyclic edge `i`. -/
def faceSide (f : K.Face) (i : ZMod 3) : Set (K.ClosedFace f) :=
  {x | ∀ v, v.1 ∉ (K.faceEdge f i).1 → x v = 0}

private theorem eq_edgeFirst_or_edgeSecond (e : K.Edge) {v : K.Vertex}
    (hv : v ∈ e.1) : v = K.edgeFirst e ∨ v = K.edgeSecond e := by
  rw [K.edge_eq_pair e] at hv
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hv

/-- The two endpoint coordinates of a face point supported on an edge add to one. -/
theorem supportedOnEdge_endpoint_sum (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) (x : K.ClosedFace f)
    (hx : ∀ v, v.1 ∉ e.1 → x v = 0) :
    x ⟨K.edgeFirst e, hef (K.edgeFirst_mem e)⟩ +
        x ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩ = 1 := by
  let a : {v // v ∈ K.faceVertices f} :=
    ⟨K.edgeFirst e, hef (K.edgeFirst_mem e)⟩
  let b : {v // v ∈ K.faceVertices f} :=
    ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩
  let E : Finset {v // v ∈ K.faceVertices f} :=
    Finset.univ.filter fun v ↦ v.1 ∈ e.1
  have hab : a ≠ b := by
    intro h
    exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)
  have hE : E = {a, b} := by
    ext v
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [K.edge_eq_pair e]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  change x a + x b = 1
  calc
    x a + x b = ∑ v ∈ E, x v := by rw [hE]; simp [hab]
    _ = ∑ v, x v := by
      apply Finset.sum_subset (Finset.subset_univ E)
      intro v _ hvE
      apply hx v
      intro hve
      apply hvE
      change v.1 ∈ e.1 at hve
      simp [E, hve]
    _ = 1 := x.2.2

theorem faceSide_endpoint_sum (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) (hx : x ∈ K.faceSide f i) :
    x ⟨K.edgeFirst (K.faceEdge f i), K.edgeFirst_faceEdge_mem_face f i⟩ +
        x ⟨K.edgeSecond (K.faceEdge f i), K.edgeSecond_faceEdge_mem_face f i⟩ = 1 :=
  K.supportedOnEdge_endpoint_sum f (K.faceEdge f i)
    (K.faceEdge_subset_faceVertices f i) x hx

/-- Restrict a face-simplex point supported on an arbitrary incident edge. -/
noncomputable def supportedOnEdgeToSimplex (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) (x : K.ClosedFace f)
    (_hx : ∀ v, v.1 ∉ e.1 → x v = 0) :
    stdSimplex ℝ {v // v ∈ e.1} :=
  K.edgeSimplexPath e
    ⟨x ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩,
      mem_Icc_of_mem_stdSimplex x.2
        ⟨K.edgeSecond e, hef (K.edgeSecond_mem e)⟩⟩

/-- Restrict a face-simplex point supported on side `i` to the corresponding edge simplex. -/
noncomputable def faceSideToEdgeSimplex (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) (hx : x ∈ K.faceSide f i) :
    stdSimplex ℝ {v // v ∈ (K.faceEdge f i).1} :=
  K.supportedOnEdgeToSimplex f (K.faceEdge f i)
    (K.faceEdge_subset_faceVertices f i) x hx

/-- A face point supported on an incident edge maps into that edge carrier. -/
theorem faceMap_mem_edgeCarrier_of_supportedOnEdge (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) (x : K.ClosedFace f)
    (hx : ∀ v, v.1 ∉ e.1 → x v = 0) :
    K.faceMap f x ∈ K.edgeCarrier e := by
  let z := K.supportedOnEdgeToSimplex f e hef x hx
  refine ⟨z, ?_⟩
  rw [K.edgeMap_eq_faceMap e f hef z]
  apply K.faceMap_eq_iff.mpr
  rw [extendFaceCoordinates_map_subset]
  funext v
  by_cases hv : v ∈ e.1
  · rw [extendFaceCoordinates_of_mem e.1 z hv,
      extendFaceCoordinates_of_mem (K.faceVertices f) x (hef hv)]
    rcases K.eq_edgeFirst_or_edgeSecond e hv with hv | hv
    · subst v
      rw [show (⟨K.edgeFirst e, hv⟩ : {w // w ∈ e.1}) =
        ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ by apply Subtype.ext; rfl]
      dsimp [z, supportedOnEdgeToSimplex]
      rw [K.edgeSimplexPath_apply_first]
      linarith [K.supportedOnEdge_endpoint_sum f e hef x hx]
    · subst v
      rw [show (⟨K.edgeSecond e, hv⟩ : {w // w ∈ e.1}) =
        ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ by apply Subtype.ext; rfl]
      dsimp [z, supportedOnEdgeToSimplex]
      rw [K.edgeSimplexPath_apply_second]
  · rw [extendFaceCoordinates_of_notMem e.1 z hv]
    by_cases hvf : v ∈ K.faceVertices f
    · rw [extendFaceCoordinates_of_mem (K.faceVertices f) x hvf]
      exact (hx ⟨v, hvf⟩ hv).symm
    · rw [extendFaceCoordinates_of_notMem (K.faceVertices f) x hvf]

/-- A point of a native face side maps into the corresponding ambient edge carrier. -/
theorem faceMap_mem_edgeCarrier_of_mem_faceSide (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) (hx : x ∈ K.faceSide f i) :
    K.faceMap f x ∈ K.edgeCarrier (K.faceEdge f i) :=
  K.faceMap_mem_edgeCarrier_of_supportedOnEdge f (K.faceEdge f i)
    (K.faceEdge_subset_faceVertices f i) x hx

/-- Include edge-local simplex coordinates in any incident maximal face. -/
noncomputable def edgeSimplexInFace (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1}) : K.ClosedFace f :=
  stdSimplex.map (fun v : {v // v ∈ e.1} ↦ ⟨v.1, hef v.2⟩) z

theorem faceMap_edgeSimplexInFace (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1}) :
    K.faceMap f (K.edgeSimplexInFace f e hef z) = K.edgeMap e z :=
  (K.edgeMap_eq_faceMap e f hef z).symm

theorem edgeSimplexInFace_supported (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f)
    (z : stdSimplex ℝ {v // v ∈ e.1})
    (v : {v // v ∈ K.faceVertices f}) (hv : v.1 ∉ e.1) :
    K.edgeSimplexInFace f e hef z v = 0 := by
  simp only [edgeSimplexInFace, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply]
  have hempty : Finset.univ.filter
      (fun w : {w // w ∈ e.1} ↦
        (⟨w.1, hef w.2⟩ : {q // q ∈ K.faceVertices f}) = v) = ∅ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    intro hw
    apply hv
    rw [← congrArg Subtype.val hw]
    exact w.2
  rw [hempty]
  simp

/-- Reindexing the canonical edge simplex inside a face gives the same oriented affine
parameter on the corresponding two standard vertices. -/
theorem faceReindexToStandard_edgeSimplexPath (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    (K.faceReindexToStandard f
      (K.edgeSimplexInFace f (K.faceEdge f i)
        (K.faceEdge_subset_faceVertices f i)
        (K.edgeSimplexPath (K.faceEdge f i) r))).1 =
      AffineMap.lineMap
        (Pi.single (K.faceEdgeFirstIndex f i) (1 : ℝ) : Fin 3 → ℝ)
        (Pi.single (K.faceEdgeSecondIndex f i) (1 : ℝ) : Fin 3 → ℝ) r.1 := by
  classical
  funext j
  let e := K.faceEdge f i
  let hef := K.faceEdge_subset_faceVertices f i
  let x := K.edgeSimplexPath e r
  have hcoords := congrFun (extendFaceCoordinates_map_subset hef x)
    (K.faceVertexEmbedding f j)
  have hvf : K.faceVertexEmbedding f j ∈ K.faceVertices f :=
    (K.faceVertexEquiv f j).2
  rw [extendFaceCoordinates_of_mem (K.faceVertices f) _ hvf] at hcoords
  change (K.edgeSimplexInFace f e hef x) (K.faceVertexEquiv f j) = _
  change (K.edgeSimplexInFace f e hef x) (K.faceVertexEquiv f j) =
    extendFaceCoordinates e.1 x (K.faceVertexEmbedding f j) at hcoords
  by_cases hve : K.faceVertexEmbedding f j ∈ e.1
  · rcases K.eq_edgeFirst_or_edgeSecond e hve with hfirst | hsecond
    · have hj : j = K.faceEdgeFirstIndex f i := by
        apply (K.faceVertexEmbedding f).injective
        rw [K.faceVertexEmbedding_faceEdgeFirstIndex f i]
        exact hfirst
      subst j
      rw [hcoords, extendFaceCoordinates_of_mem e.1 x hve,
        show (⟨K.faceVertexEmbedding f (K.faceEdgeFirstIndex f i), hve⟩ :
          {v // v ∈ e.1}) =
            ⟨K.edgeFirst e, K.edgeFirst_mem e⟩ by
              apply Subtype.ext
              exact K.faceVertexEmbedding_faceEdgeFirstIndex f i,
        K.edgeSimplexPath_apply_first]
      have hne : K.faceEdgeFirstIndex f i ≠ K.faceEdgeSecondIndex f i := by
        intro h
        apply K.edgeFirst_ne_edgeSecond e
        rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
          ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, h]
      simp [AffineMap.lineMap_apply_module, hne]
    · have hj : j = K.faceEdgeSecondIndex f i := by
        apply (K.faceVertexEmbedding f).injective
        rw [K.faceVertexEmbedding_faceEdgeSecondIndex f i]
        exact hsecond
      subst j
      rw [hcoords, extendFaceCoordinates_of_mem e.1 x hve,
        show (⟨K.faceVertexEmbedding f (K.faceEdgeSecondIndex f i), hve⟩ :
          {v // v ∈ e.1}) =
            ⟨K.edgeSecond e, K.edgeSecond_mem e⟩ by
              apply Subtype.ext
              exact K.faceVertexEmbedding_faceEdgeSecondIndex f i,
        K.edgeSimplexPath_apply_second]
      have hne : K.faceEdgeSecondIndex f i ≠ K.faceEdgeFirstIndex f i := by
        intro h
        apply K.edgeFirst_ne_edgeSecond e
        rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
          ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, ← h]
      simp [AffineMap.lineMap_apply_module, hne]
  · have hjFirst : j ≠ K.faceEdgeFirstIndex f i := by
      intro h
      subst j
      exact hve (by
        rw [K.faceVertexEmbedding_faceEdgeFirstIndex f i]
        exact K.edgeFirst_mem e)
    have hjSecond : j ≠ K.faceEdgeSecondIndex f i := by
      intro h
      subst j
      exact hve (by
        rw [K.faceVertexEmbedding_faceEdgeSecondIndex f i]
        exact K.edgeSecond_mem e)
    rw [hcoords, extendFaceCoordinates_of_notMem e.1 x hve]
    simp [AffineMap.lineMap_apply_module, hjFirst, hjSecond]

/-- The standard plane chart sends the canonical edge-simplex path to the globally oriented
affine parameter on the corresponding standard side. -/
theorem facePlaneHomeomorph_edgeSimplexPath (f : K.Face) (i : ZMod 3)
    (r : Set.Icc (0 : ℝ) 1) :
    (K.facePlaneHomeomorph f
      (K.edgeSimplexInFace f (K.faceEdge f i)
        (K.faceEdge_subset_faceVertices f i)
        (K.edgeSimplexPath (K.faceEdge f i) r))).1 =
      K.faceEdgeSourcePoint f i r.1 := by
  rw [facePlaneHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    PlaneComplex.realizationHomeomorph_apply]
  change standardTrianglePlaneComplex.baryEval
      (K.faceReindexToStandard f
        (K.edgeSimplexInFace f (K.faceEdge f i)
          (K.faceEdge_subset_faceVertices f i)
          (K.edgeSimplexPath (K.faceEdge f i) r))).1 = _
  rw [K.faceReindexToStandard_edgeSimplexPath f i]
  rw [PlaneComplex.baryEval, faceEdgeSourcePoint,
    AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp_rw [add_smul]
  rw [Finset.sum_add_distrib]
  have hfirst :
      ∑ j : Fin 3,
          ((1 - r.1) * if j = K.faceEdgeFirstIndex f i then 1 else 0) •
            standardTrianglePlaneComplex.position j =
        (1 - r.1) • standardTriangleVertex (K.faceEdgeFirstIndex f i) := by
    simp []
  have hsecond :
      ∑ j : Fin 3,
          (r.1 * if j = K.faceEdgeSecondIndex f i then 1 else 0) •
            standardTrianglePlaneComplex.position j =
        r.1 • standardTriangleVertex (K.faceEdgeSecondIndex f i) := by
    simp []
  rw [hfirst, hsecond, AffineMap.lineMap_apply_module]

theorem edgeCarrier_subset_faceCarrier_of_subset (f : K.Face) (e : K.Edge)
    (hef : e.1 ⊆ K.faceVertices f) :
    K.edgeCarrier e ⊆ K.faceCarrier f := by
  rintro y ⟨z, rfl⟩
  exact ⟨K.edgeSimplexInFace f e hef z,
    K.faceMap_edgeSimplexInFace f e hef z⟩

theorem faceReindexToStandard_mem_faceCarrier (f : K.Face) (i : ZMod 3)
    (x : K.ClosedFace f) :
    standardSimplexToRealization (K.faceReindexToStandard f x) ∈
        standardTrianglePlaneComplex.toIntrinsic.faceCarrier
          (IntrinsicTwoComplex.faceStandardEdge i) ↔
      x ∈ K.faceSide f i := by
  constructor
  · intro hx v hv
    let j : Fin 3 := (K.faceVertexEquiv f).symm v
    have hj : j ∉ IntrinsicTwoComplex.faceStandardEdge i := by
      intro hj
      apply hv
      rw [K.faceEdge_val f i]
      simp only [IntrinsicTwoComplex.faceStandardEdge, Finset.mem_insert,
        Finset.mem_singleton] at hj ⊢
      rcases hj with hj | hj
      · left
        have heq : K.faceVertexEquiv f j = v :=
          (K.faceVertexEquiv f).apply_symm_apply v
        calc
          v.1 = (K.faceVertexEquiv f j).1 := congrArg Subtype.val heq.symm
          _ = K.faceVertex f i := by rw [hj]; rfl
      · right
        have heq : K.faceVertexEquiv f j = v :=
          (K.faceVertexEquiv f).apply_symm_apply v
        calc
          v.1 = (K.faceVertexEquiv f j).1 := congrArg Subtype.val heq.symm
          _ = K.faceVertex f (i + 1) := by rw [hj]; rfl
    have hz := hx j hj
    change x (K.faceVertexEquiv f j) = 0 at hz
    simpa [j] using hz
  · intro hx j hj
    change x (K.faceVertexEquiv f j) = 0
    apply hx
    intro hmem
    apply hj
    rw [K.faceEdge_val f i] at hmem
    simp only [IntrinsicTwoComplex.faceStandardEdge, Finset.mem_insert,
      Finset.mem_singleton] at hmem ⊢
    rcases hmem with hmem | hmem
    · left
      apply (K.faceVertexEquiv f).injective
      exact Subtype.ext hmem
    · right
      apply (K.faceVertexEquiv f).injective
      exact Subtype.ext hmem

/-- The standard plane chart sends cyclic source side `i` exactly onto cyclic side `i` of the
standard triangle. -/
theorem facePlaneHomeomorph_image_edge (f : K.Face) (i : ZMod 3) :
    (fun x : K.ClosedFace f ↦ (K.facePlaneHomeomorph f x).1) '' K.faceSide f i =
      standardTriangleCircle.edgeSegment i := by
  let s := IntrinsicTwoComplex.faceStandardEdge i
  have hs : s ∈ standardTrianglePlaneComplex.simplexes :=
    IntrinsicTwoComplex.faceStandardEdge_mem_simplexes i
  have hgeom := standardTrianglePlaneComplex.realizationHomeomorph_image_faceCarrier
    standardTrianglePlaneComplex_pure hs
  rw [IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i] at hgeom
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    let z := standardSimplexToRealization (K.faceReindexToStandard f x)
    have hz : z ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s := by
      exact (K.faceReindexToStandard_mem_faceCarrier f i x).mpr hx
    rw [← hgeom]
    exact ⟨z, hz, rfl⟩
  · intro p hp
    rw [← hgeom] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    let x : K.ClosedFace f :=
      (K.faceReindexHomeomorph f).symm (standardRealizationToSimplex z)
    have hx : x ∈ K.faceSide f i := by
      apply (K.faceReindexToStandard_mem_faceCarrier f i x).mp
      have heq : standardSimplexToRealization (K.faceReindexToStandard f x) = z := by
        apply Subtype.ext
        change (K.faceReindexHomeomorph f x).1 = z.1
        rw [(K.faceReindexHomeomorph f).apply_symm_apply]
        rfl
      rwa [heq]
    refine ⟨x, hx, ?_⟩
    change (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure
        (standardSimplexToRealization (K.faceReindexHomeomorph f x))).1 = p
    simpa [x] using hzp

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
