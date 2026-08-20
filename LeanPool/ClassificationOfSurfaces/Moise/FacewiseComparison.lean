/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteControlledApproximation

/-!
# The per-face comparison map for locally finite side preservation

This file discharges the side-preservation entry of the locally finite Chapter 6 replacement
through the parametrization-independent interface `cellwiseCompatibility_of_comparison`.

The canonical replacement arcs only track the *trimmed* original edge curve
(`CentralPolygonalArc.curve_close`), with the `Path.trans` parameter misaligned against the
original face parametrization, so no same-parameter estimate can beat the mesh scale.  The
comparison map built here is the original face chart composed with a clamped radial
reparametrization of the standard triangle (`sidePiece`, glued over three closed sectors in
`facewiseComparison`): on each side the boundary parameter is redistributed so that the middle
replacement range covers exactly the matched trim window, and the spoke ranges cover the two
trimmed-off end pieces.  All values lie in the original face image, so the cthickening
membership required by `cellwiseCompatibility_of_comparison` is automatic.

The key quantitative input is `exists_comparisonScale`: the original face chart and its
inverse are both uniformly continuous on the compact standard triangle, so once the vertex
isolation disk and central tube of an edge are small in the *image*, the endpoints of each
trimmed-off piece have close images, hence (inverse modulus) close standard parameters, hence
(forward modulus) the whole reparametrized piece stays within a quarter separation radius of
the vertex image.  In particular the last-exit trim cannot make the trimmed-off original
curve wander once the controls undercut the comparison scale — the wandering is bounded by
the two-sided modulus, not by any mesh estimate.

Everything is arranged for a realization with shrunken approximation controls
(`withApproximationControls`), which changes neither the embedded map nor the face separation
radii; the resulting entry point is `exists_controlled_polygonalReplacement_of_comparison`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

/-! ## Barycentric coordinates on the standard triangle -/

/-- The standard triangle vertices as an affine basis of the plane. -/
noncomputable def stdTriBasis : AffineBasis (Fin 3) ℝ Plane :=
  planeAffineBasisOfTriple standardTriangleVertex standardTriangleVertex_affineIndependent

@[simp] theorem stdTriBasis_apply (j : Fin 3) :
    stdTriBasis j = standardTriangleVertex j := rfl

theorem range_stdTriBasis :
    Set.range ⇑stdTriBasis = Set.range standardTriangleVertex := rfl

/-- The barycentric coordinate of a plane point with respect to a standard triangle vertex. -/
noncomputable def triCoord (j : Fin 3) (x : Plane) : ℝ := stdTriBasis.coord j x

theorem continuous_triCoord (j : Fin 3) : Continuous (triCoord j) :=
  (stdTriBasis.coord j).continuous_of_finiteDimensional

@[simp] theorem triCoord_vertex_self (j : Fin 3) :
    triCoord j (standardTriangleVertex j) = 1 := by
  simpa [triCoord] using stdTriBasis.coord_apply_eq j

theorem triCoord_vertex_ne {j k : Fin 3} (hjk : j ≠ k) :
    triCoord j (standardTriangleVertex k) = 0 := by
  simpa [triCoord] using stdTriBasis.coord_apply_ne hjk

theorem sum_triCoord (x : Plane) : ∑ j, triCoord j x = 1 :=
  stdTriBasis.sum_coord_apply_eq_one x

theorem triCoord_lineMap (j : Fin 3) (a b : Plane) (t : ℝ) :
    triCoord j (AffineMap.lineMap a b t) =
      AffineMap.lineMap (triCoord j a) (triCoord j b) t := by
  simp only [triCoord]
  exact (stdTriBasis.coord j).apply_lineMap a b t

theorem standardFaceRegion_eq_convexHull :
    standardFaceRegion = convexHull ℝ (Set.range standardTriangleVertex) :=
  standardTrianglePlaneComplex_support

theorem convex_standardFaceRegion : Convex ℝ standardFaceRegion := by
  rw [standardFaceRegion_eq_convexHull]
  exact convex_convexHull ℝ _

theorem mem_standardFaceRegion_iff {x : Plane} :
    x ∈ standardFaceRegion ↔ ∀ j, 0 ≤ triCoord j x := by
  rw [standardFaceRegion_eq_convexHull, ← range_stdTriBasis,
    stdTriBasis.convexHull_eq_nonneg_coord]
  rfl

theorem interior_standardFaceRegion :
    interior standardFaceRegion = {x | ∀ j, 0 < triCoord j x} := by
  rw [standardFaceRegion_eq_convexHull, ← range_stdTriBasis]
  exact interior_convexHull_affineBasis stdTriBasis

theorem mem_frontier_standardFaceRegion_iff {x : Plane} :
    x ∈ frontier standardFaceRegion ↔
      x ∈ standardFaceRegion ∧ ∃ j, triCoord j x = 0 := by
  rw [standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_eq,
    Set.mem_sdiff, interior_standardFaceRegion]
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    by_contra hall
    push Not at hall
    apply hnot
    intro j
    exact lt_of_le_of_ne (mem_standardFaceRegion_iff.mp hx j) (Ne.symm (hall j))
  · rintro ⟨hx, j, hj⟩
    refine ⟨hx, ?_⟩
    intro hint
    exact (hint j).ne' hj

theorem mem_frontier_of_triCoord_eq_zero {x : Plane}
    (hx : x ∈ standardFaceRegion) {j : Fin 3} (hj : triCoord j x = 0) :
    x ∈ frontier standardFaceRegion :=
  mem_frontier_standardFaceRegion_iff.mpr ⟨hx, j, hj⟩

/-- The barycenter of the standard triangle. -/
noncomputable def triCenter : Plane :=
  Finset.univ.centroid ℝ standardTriangleVertex

@[simp] theorem triCoord_triCenter (j : Fin 3) :
    triCoord j triCenter = 1 / 3 := by
  have h := stdTriBasis.coord_apply_centroid
    (s := (Finset.univ : Finset (Fin 3))) (i := j) (Finset.mem_univ j)
  have hcentroid : Finset.univ.centroid ℝ ⇑stdTriBasis = triCenter := rfl
  rw [hcentroid] at h
  simpa [triCoord] using h

theorem triCenter_mem_standardFaceRegion : triCenter ∈ standardFaceRegion := by
  rw [mem_standardFaceRegion_iff]
  intro j
  rw [triCoord_triCenter]
  norm_num

/-! ## The clamped unit parameter -/

/-- Clamp a real parameter into `[0, 1]`. -/
noncomputable def unitClamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem continuous_unitClamp : Continuous unitClamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem unitClamp_nonneg (t : ℝ) : 0 ≤ unitClamp t := le_max_left _ _

theorem unitClamp_le_one (t : ℝ) : unitClamp t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem unitClamp_mem (t : ℝ) : unitClamp t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨unitClamp_nonneg t, unitClamp_le_one t⟩

theorem unitClamp_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    unitClamp t = t := by
  rw [unitClamp, min_eq_right ht.2, max_eq_right ht.1]

@[simp] theorem unitClamp_zero : unitClamp 0 = 0 :=
  unitClamp_of_mem ⟨le_rfl, zero_le_one⟩

@[simp] theorem unitClamp_one : unitClamp 1 = 1 :=
  unitClamp_of_mem ⟨zero_le_one, le_rfl⟩

/-- A clamped line-map combination of two points of a convex set stays in the set. -/
theorem lineMap_unitClamp_mem {s : Set Plane} (hs : Convex ℝ s) {a b : Plane}
    (ha : a ∈ s) (hb : b ∈ s) (t : ℝ) :
    AffineMap.lineMap a b (unitClamp t) ∈ s := by
  have hseg : AffineMap.lineMap a b (unitClamp t) ∈ segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    exact ⟨unitClamp t, unitClamp_mem t, rfl⟩
  exact hs.segment_subset ha hb hseg

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-! ## Coordinates along one oriented standard side -/

theorem faceEdgeFirstIndex_ne_secondIndex (f : K.Face) (i : ZMod 3) :
    K.faceEdgeFirstIndex f i ≠ K.faceEdgeSecondIndex f i := by
  intro h
  apply K.edgeFirst_ne_edgeSecond (K.faceEdge f i)
  rw [← K.faceVertexEmbedding_faceEdgeFirstIndex f i,
    ← K.faceVertexEmbedding_faceEdgeSecondIndex f i, h]

theorem triCoord_secondIndex_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    triCoord (K.faceEdgeSecondIndex f i) (K.faceEdgeSourcePoint f i r) = r := by
  rw [faceEdgeSourcePoint, triCoord_lineMap,
    triCoord_vertex_ne (Ne.symm (K.faceEdgeFirstIndex_ne_secondIndex f i)),
    triCoord_vertex_self]
  simp [AffineMap.lineMap_apply_module]

theorem triCoord_firstIndex_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    triCoord (K.faceEdgeFirstIndex f i) (K.faceEdgeSourcePoint f i r) = 1 - r := by
  rw [faceEdgeSourcePoint, triCoord_lineMap, triCoord_vertex_self,
    triCoord_vertex_ne (K.faceEdgeFirstIndex_ne_secondIndex f i)]
  simp [AffineMap.lineMap_apply_module]

theorem triCoord_other_sourcePoint (f : K.Face) (i : ZMod 3) {j : Fin 3}
    (hj₁ : j ≠ K.faceEdgeFirstIndex f i) (hj₂ : j ≠ K.faceEdgeSecondIndex f i)
    (r : ℝ) :
    triCoord j (K.faceEdgeSourcePoint f i r) = 0 := by
  rw [faceEdgeSourcePoint, triCoord_lineMap, triCoord_vertex_ne hj₁,
    triCoord_vertex_ne hj₂]
  simp

@[simp] theorem faceEdgeSourcePoint_zero (f : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint f i 0 =
      standardTriangleVertex (K.faceEdgeFirstIndex f i) :=
  AffineMap.lineMap_apply_zero _ _

@[simp] theorem faceEdgeSourcePoint_one (f : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint f i 1 =
      standardTriangleVertex (K.faceEdgeSecondIndex f i) :=
  AffineMap.lineMap_apply_one _ _

theorem faceEdgeSourcePoint_mem_region (f : K.Face) (i : ZMod 3) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint f i r ∈ standardFaceRegion := by
  rw [mem_standardFaceRegion_iff]
  intro j
  by_cases hj₁ : j = K.faceEdgeFirstIndex f i
  · rw [hj₁, triCoord_firstIndex_sourcePoint]
    linarith [hr.2]
  by_cases hj₂ : j = K.faceEdgeSecondIndex f i
  · rw [hj₂, triCoord_secondIndex_sourcePoint]
    exact hr.1
  · rw [triCoord_other_sourcePoint f i hj₁ hj₂]

theorem continuous_faceEdgeSourcePoint (f : K.Face) (i : ZMod 3) :
    Continuous (K.faceEdgeSourcePoint f i) :=
  (AffineMap.lineMap _ _).continuous_of_finiteDimensional.comp
    (by exact continuous_id) |>.congr fun r => rfl

/-! ## The original face chart along a source side -/

/-- The original face chart carries the oriented standard side to the charted edge curve with
the identical parameter. -/
theorem faceOriginalMap_sourcePoint (f : K.Face) (i : ZMod 3) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    faceOriginalMap G f (K.faceEdgeSourcePoint f i r) =
      G.chartEdgeCurve (K.faceEdge f i) r := by
  let r' : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  have hmem : K.faceEdgeSourcePoint f i r ∈ standardFaceRegion :=
    K.faceEdgeSourcePoint_mem_region f i hr
  have happly := faceOriginalMap_apply (G := G) f
    ⟨K.faceEdgeSourcePoint f i r, hmem⟩
  have hsupport := K.faceBoundarySupportPoint_sourcePoint f i r'
  have hsupport' : faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm ⟨K.faceEdgeSourcePoint f i r, hmem⟩) =
      edgePathInSupport (K := K) (K.faceEdge f i) r' := by
    exact hsupport
  rw [happly, hsupport', G.chartEdgeCurve_eq_of_mem _ hr]
  rfl

/-- The original face chart is injective on the closed standard triangle. -/
theorem faceOriginalMap_injOn (f : K.Face) :
    Set.InjOn (faceOriginalMap G f) standardFaceRegion := by
  intro x hx y hy hxy
  rw [faceOriginalMap_apply (G := G) f ⟨x, hx⟩,
    faceOriginalMap_apply (G := G) f ⟨y, hy⟩] at hxy
  have hsupp : faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm ⟨x, hx⟩) =
      faceToSupport (K := K) f ((K.facePlaneHomeomorph f).symm ⟨y, hy⟩) :=
    G.isEmbedding.injective hxy
  have hface : K.faceMap f ((K.facePlaneHomeomorph f).symm ⟨x, hx⟩) =
      K.faceMap f ((K.facePlaneHomeomorph f).symm ⟨y, hy⟩) :=
    congrArg Subtype.val hsupp
  have := (K.facePlaneHomeomorph f).symm.injective (K.faceMap_injective f hface)
  exact congrArg Subtype.val this

/-! ## The comparison scale of a face

The face separation radius bounds the target tolerance; the two-sided uniform continuity of
the original face chart converts image smallness into segment-image smallness.  The resulting
scale is what the shrunken approximation controls must undercut. -/

/-- Two-sided modulus: once two standard points have images within twice this scale, the whole
straight segment between them has image within a quarter separation radius of either end. -/
theorem exists_comparisonScale (G : K.PlaneGraphRealization) (f : K.Face) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ faceVertexSeparationRadius G f / 8 ∧
      ∀ x ∈ standardFaceRegion, ∀ y ∈ standardFaceRegion,
        dist (faceOriginalMap G f x) (faceOriginalMap G f y) ≤ 2 * eta →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist (faceOriginalMap G f (AffineMap.lineMap x y t))
            (faceOriginalMap G f x) ≤ faceVertexSeparationRadius G f / 4 := by
  classical
  set r := faceVertexSeparationRadius G f with hr
  have hrpos : 0 < r := faceVertexSeparationRadius_pos (G := G) f
  set h := faceOriginalMap G f with hh
  have hcont : ContinuousOn h standardFaceRegion :=
    continuousOn_faceOriginalMap (G := G) f
  have hcompact : IsCompact standardFaceRegion :=
    standardTrianglePlaneComplex.isCompact_support
  -- forward modulus
  obtain ⟨d₁, hd₁, hd₁close⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (hcompact.uniformContinuousOn_of_continuous hcont)) (r / 4) (by positivity)
  -- inverse modulus by compactness of the far diagonal
  set KK : Set (Plane × Plane) :=
    (standardFaceRegion ×ˢ standardFaceRegion) ∩ {p | d₁ ≤ dist p.1 p.2} with hKK
  have hKKcompact : IsCompact KK :=
    (hcompact.prod hcompact).inter_right
      (isClosed_le continuous_const (continuous_dist))
  have hinverse : ∃ mu : ℝ, 0 < mu ∧
      ∀ x ∈ standardFaceRegion, ∀ y ∈ standardFaceRegion,
        dist (h x) (h y) < mu → dist x y < d₁ := by
    rcases KK.eq_empty_or_nonempty with hempty | hne
    · refine ⟨1, one_pos, ?_⟩
      intro x hx y hy _
      by_contra hfar
      push Not at hfar
      exact absurd (Set.eq_empty_iff_forall_notMem.mp hempty (x, y))
        (fun hnot => hnot ⟨⟨hx, hy⟩, hfar⟩)
    · have hFcont : ContinuousOn (fun p : Plane × Plane => dist (h p.1) (h p.2)) KK := by
        have h1 : ContinuousOn (fun p : Plane × Plane => h p.1) KK :=
          hcont.comp continuousOn_fst fun p hp => hp.1.1
        have h2 : ContinuousOn (fun p : Plane × Plane => h p.2) KK :=
          hcont.comp continuousOn_snd fun p hp => hp.1.2
        exact continuous_dist.comp_continuousOn (h1.prodMk h2)
      obtain ⟨p₀, hp₀KK, hp₀min⟩ := hKKcompact.exists_isMinOn hne hFcont
      have hp₀pos : 0 < dist (h p₀.1) (h p₀.2) := by
        rw [dist_pos]
        intro heq
        have hne12 : p₀.1 ≠ p₀.2 := by
          intro h12
          have hfar : d₁ ≤ dist p₀.1 p₀.2 := hp₀KK.2
          rw [h12, dist_self] at hfar
          exact absurd hfar (not_le.mpr hd₁)
        exact hne12 (faceOriginalMap_injOn (G := G) f hp₀KK.1.1 hp₀KK.1.2 heq)
      refine ⟨dist (h p₀.1) (h p₀.2), hp₀pos, ?_⟩
      intro x hx y hy hclose
      by_contra hfar
      push Not at hfar
      have hxyKK : (x, y) ∈ KK := ⟨⟨hx, hy⟩, hfar⟩
      exact absurd (hp₀min hxyKK) (not_le.mpr hclose)
  obtain ⟨mu, hmu, hmuinv⟩ := hinverse
  refine ⟨min (r / 8) (mu / 4), lt_min (by positivity) (by positivity),
    min_le_left _ _, ?_⟩
  intro x hx y hy hclose t ht
  have hclose' : dist (h x) (h y) < mu := by
    have h2 : 2 * min (r / 8) (mu / 4) ≤ mu / 2 := by
      have := min_le_right (r / 8) (mu / 4)
      linarith
    calc dist (h x) (h y) ≤ 2 * min (r / 8) (mu / 4) := hclose
      _ ≤ mu / 2 := h2
      _ < mu := by linarith
  have hxy : dist x y < d₁ := hmuinv x hx y hy hclose'
  set z := AffineMap.lineMap x y t with hz
  have hzmem : z ∈ standardFaceRegion := by
    have hseg : z ∈ segment ℝ x y := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    exact convex_standardFaceRegion.segment_subset hx hy hseg
  have hzx : dist z x < d₁ := by
    have hdist : dist z x = |t| * dist x y := by
      rw [hz, dist_lineMap_left, Real.norm_eq_abs]
    rw [hdist]
    calc |t| * dist x y ≤ 1 * dist x y := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          rw [abs_of_nonneg ht.1]
          exact ht.2
      _ = dist x y := one_mul _
      _ < d₁ := hxy
  exact (hd₁close z hzmem x hx hzx).le

/-- A canonical positive comparison scale for every face. -/
noncomputable def comparisonScale (G : K.PlaneGraphRealization) (f : K.Face) : ℝ :=
  Classical.choose (exists_comparisonScale G f)

theorem comparisonScale_pos (G : K.PlaneGraphRealization) (f : K.Face) :
    0 < comparisonScale G f :=
  (Classical.choose_spec (exists_comparisonScale G f)).1

theorem comparisonScale_le (G : K.PlaneGraphRealization) (f : K.Face) :
    comparisonScale G f ≤ faceVertexSeparationRadius G f / 8 :=
  (Classical.choose_spec (exists_comparisonScale G f)).2.1

theorem comparisonScale_segment (G : K.PlaneGraphRealization) (f : K.Face)
    {x y : Plane} (hx : x ∈ standardFaceRegion) (hy : y ∈ standardFaceRegion)
    (hclose : dist (faceOriginalMap G f x) (faceOriginalMap G f y) ≤
      2 * comparisonScale G f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (faceOriginalMap G f (AffineMap.lineMap x y t))
      (faceOriginalMap G f x) ≤ faceVertexSeparationRadius G f / 4 :=
  (Classical.choose_spec (exists_comparisonScale G f)).2.2 x hx y hy hclose t ht

/-! ## The standard index opposite a cyclic side -/

/-- The standard corner index not lying on cyclic side `i`. -/
noncomputable def standardOppIndex (i : ZMod 3) : Fin 3 :=
  (ZMod.finEquiv 3).symm (i + 2)

theorem finEquiv_symm_injective :
    Function.Injective ((ZMod.finEquiv 3).symm : ZMod 3 → Fin 3) :=
  (ZMod.finEquiv 3).symm.injective

theorem faceEdge_index_cases (f : K.Face) (i : ZMod 3) :
    (K.faceEdgeFirstIndex f i = (ZMod.finEquiv 3).symm i ∧
        K.faceEdgeSecondIndex f i = (ZMod.finEquiv 3).symm (i + 1)) ∨
      (K.faceEdgeFirstIndex f i = (ZMod.finEquiv 3).symm (i + 1) ∧
        K.faceEdgeSecondIndex f i = (ZMod.finEquiv 3).symm i) := by
  have hpair : ({K.faceEdgeFirstIndex f i, K.faceEdgeSecondIndex f i} :
      Finset (Fin 3)) =
      {(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)} :=
    (K.faceStandardEdge_eq_endpointIndices f i).symm
  have hfs : K.faceEdgeFirstIndex f i ∈
      ({(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)} :
        Finset (Fin 3)) := by
    rw [← hpair]
    exact Finset.mem_insert_self _ _
  have hss : K.faceEdgeSecondIndex f i ∈
      ({(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)} :
        Finset (Fin 3)) := by
    rw [← hpair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hne := K.faceEdgeFirstIndex_ne_secondIndex f i
  rcases Finset.mem_insert.mp hfs with h₁ | h₁
  · rcases Finset.mem_insert.mp hss with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hne
    · exact Or.inl ⟨h₁, Finset.mem_singleton.mp h₂⟩
  · rcases Finset.mem_insert.mp hss with h₂ | h₂
    · exact Or.inr ⟨Finset.mem_singleton.mp h₁, h₂⟩
    · exact absurd ((Finset.mem_singleton.mp h₁).trans
        (Finset.mem_singleton.mp h₂).symm) hne

theorem standardOppIndex_ne_symm (i : ZMod 3) :
    standardOppIndex i ≠ (ZMod.finEquiv 3).symm i := by
  intro h
  exact (by decide : ∀ z : ZMod 3, z + 2 ≠ z) i (finEquiv_symm_injective h)

theorem standardOppIndex_ne_symm_succ (i : ZMod 3) :
    standardOppIndex i ≠ (ZMod.finEquiv 3).symm (i + 1) := by
  intro h
  exact (by decide : ∀ z : ZMod 3, z + 2 ≠ z + 1) i (finEquiv_symm_injective h)

theorem standardOppIndex_ne_firstIndex (f : K.Face) (i : ZMod 3) :
    standardOppIndex i ≠ K.faceEdgeFirstIndex f i := by
  rcases K.faceEdge_index_cases f i with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · rw [h₁]; exact standardOppIndex_ne_symm i
  · rw [h₁]; exact standardOppIndex_ne_symm_succ i

theorem standardOppIndex_ne_secondIndex (f : K.Face) (i : ZMod 3) :
    standardOppIndex i ≠ K.faceEdgeSecondIndex f i := by
  rcases K.faceEdge_index_cases f i with ⟨-, h₂⟩ | ⟨-, h₂⟩
  · rw [h₂]; exact standardOppIndex_ne_symm_succ i
  · rw [h₂]; exact standardOppIndex_ne_symm i

theorem triCoord_oppIndex_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    triCoord (standardOppIndex i) (K.faceEdgeSourcePoint f i r) = 0 :=
  K.triCoord_other_sourcePoint f i (K.standardOppIndex_ne_firstIndex f i)
    (K.standardOppIndex_ne_secondIndex f i) r

/-- The three coordinates named by one side enumerate the whole coordinate sum. -/
theorem triCoord_side_sum (f : K.Face) (i : ZMod 3) (x : Plane) :
    triCoord (K.faceEdgeFirstIndex f i) x + triCoord (K.faceEdgeSecondIndex f i) x +
      triCoord (standardOppIndex i) x = 1 := by
  classical
  set a := K.faceEdgeFirstIndex f i
  set b := K.faceEdgeSecondIndex f i
  set c := standardOppIndex i
  have hab : a ≠ b := K.faceEdgeFirstIndex_ne_secondIndex f i
  have hca : c ≠ a := K.standardOppIndex_ne_firstIndex f i
  have hcb : c ≠ b := K.standardOppIndex_ne_secondIndex f i
  have hbc : b ∉ ({c} : Finset (Fin 3)) := by
    rw [Finset.mem_singleton]
    exact fun h => hcb h.symm
  have habc : a ∉ ({b, c} : Finset (Fin 3)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hab, fun h => hca h.symm⟩
  have hcard : ({a, b, c} : Finset (Fin 3)).card = 3 := by
    rw [Finset.card_insert_of_notMem habc, Finset.card_insert_of_notMem hbc,
      Finset.card_singleton]
  have huniv : ({a, b, c} : Finset (Fin 3)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard]; rfl)
  have hsum := sum_triCoord x
  rw [← huniv, Finset.sum_insert habc, Finset.sum_insert hbc,
    Finset.sum_singleton] at hsum
  linarith

/-! ## The matched trim parameters of one side -/

/-- The original edge parameter matched to the polygonal arc's left exit. -/
noncomputable def sideTrimLeft (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : ℝ :=
  AffineMap.lineMap (G.edgeTrim (K.faceEdge f i)).left
    (G.edgeTrim (K.faceEdge f i)).right
    (G.replacementArc (K.faceEdge f i)).exitData.left

/-- The original edge parameter matched to the polygonal arc's right exit. -/
noncomputable def sideTrimRight (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : ℝ :=
  AffineMap.lineMap (G.edgeTrim (K.faceEdge f i)).left
    (G.edgeTrim (K.faceEdge f i)).right
    (G.replacementArc (K.faceEdge f i)).exitData.right

theorem sideTrim_left_le_right (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideTrimLeft G f i ≤ sideTrimRight G f i := by
  have hT := (G.edgeTrim (K.faceEdge f i)).left_lt_right
  have hX := (G.replacementArc (K.faceEdge f i)).exitData.left_lt_right
  simp only [sideTrimLeft, sideTrimRight, AffineMap.lineMap_apply_ring]
  nlinarith

theorem sideTrimLeft_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideTrimLeft G f i ∈ Set.Icc (0 : ℝ) 1 := by
  have hTl := (G.edgeTrim (K.faceEdge f i)).left_pos
  have hTlr := (G.edgeTrim (K.faceEdge f i)).left_lt_right
  have hTr := (G.edgeTrim (K.faceEdge f i)).right_lt_one
  have hXl := (G.replacementArc (K.faceEdge f i)).exitData.left_nonneg
  have hXlr := (G.replacementArc (K.faceEdge f i)).exitData.left_lt_right
  have hXr := (G.replacementArc (K.faceEdge f i)).exitData.right_le_one
  simp only [sideTrimLeft, AffineMap.lineMap_apply_ring]
  constructor <;> nlinarith

theorem sideTrimRight_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideTrimRight G f i ∈ Set.Icc (0 : ℝ) 1 := by
  have hTl := (G.edgeTrim (K.faceEdge f i)).left_pos
  have hTlr := (G.edgeTrim (K.faceEdge f i)).left_lt_right
  have hTr := (G.edgeTrim (K.faceEdge f i)).right_lt_one
  have hXl := (G.replacementArc (K.faceEdge f i)).exitData.left_nonneg
  have hXlr := (G.replacementArc (K.faceEdge f i)).exitData.left_lt_right
  have hXr := (G.replacementArc (K.faceEdge f i)).exitData.right_le_one
  simp only [sideTrimRight, AffineMap.lineMap_apply_ring]
  constructor <;> nlinarith

/-! ## The matched boundary parameter profile of one side -/

/-- The piecewise-affine reparametrization of one side matched to the complete replacement
path: the left spoke range covers the trimmed-off initial edge piece, the middle range covers
the matched trim window, and the right spoke range covers the trimmed-off final piece. -/
noncomputable def sideParamProfile (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (u : ℝ) : ℝ :=
  if u ≤ 1 / 2 then 2 * u * sideTrimLeft G f i
  else if u ≤ 3 / 4 then
    AffineMap.lineMap (sideTrimLeft G f i) (sideTrimRight G f i) (4 * u - 2)
  else AffineMap.lineMap (sideTrimRight G f i) 1 (4 * u - 3)

theorem continuous_sideParamProfile (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : Continuous (sideParamProfile G f i) := by
  apply Continuous.if_le
  · fun_prop
  · apply Continuous.if_le
    · simp only [AffineMap.lineMap_apply_ring]
      fun_prop
    · simp only [AffineMap.lineMap_apply_ring]
      fun_prop
    · fun_prop
    · fun_prop
    · intro u hu
      rw [hu]
      norm_num [AffineMap.lineMap_apply_ring]
  · fun_prop
  · fun_prop
  · intro u hu
    rw [hu]
    norm_num [AffineMap.lineMap_apply_ring]

@[simp] theorem sideParamProfile_zero (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideParamProfile G f i 0 = 0 := by
  norm_num [sideParamProfile]

@[simp] theorem sideParamProfile_one (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : sideParamProfile G f i 1 = 1 := by
  norm_num [sideParamProfile, AffineMap.lineMap_apply_ring]

theorem sideParamProfile_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    sideParamProfile G f i u ∈ Set.Icc (0 : ℝ) 1 := by
  have hl := sideTrimLeft_mem G f i
  have hr := sideTrimRight_mem G f i
  have hlr := sideTrim_left_le_right G f i
  rw [sideParamProfile]
  split_ifs with h₁ h₂
  · constructor <;> nlinarith [hu.1, hu.2, hl.1, hl.2]
  · rw [AffineMap.lineMap_apply_ring]
    push Not at h₁
    constructor <;> nlinarith [hu.1, hu.2, hl.1, hl.2, hr.1, hr.2]
  · rw [AffineMap.lineMap_apply_ring]
    push Not at h₁ h₂
    constructor <;> nlinarith [hu.1, hu.2, hr.1, hr.2]

/-! ## The comparison piece adapted to one side -/

/-- The barycentric depth of a point relative to one side: `1` on the side, `0` at the
barycenter. -/
noncomputable def sideDepth (i : ZMod 3) (x : Plane) : ℝ :=
  1 - 3 * triCoord (standardOppIndex i) x

theorem continuous_sideDepth (i : ZMod 3) : Continuous (sideDepth i) :=
  continuous_const.sub
    (continuous_const.mul (continuous_triCoord (standardOppIndex i)))

/-- The raw radial side parameter of a point: on the side itself it is the oriented affine
side parameter; near the barycenter the clamped denominator keeps it continuous. -/
noncomputable def sideRawParam (f : K.Face) (i : ZMod 3) (x : Plane) : ℝ :=
  (triCoord (K.faceEdgeSecondIndex f i) x - 1 / 3) /
      max (sideDepth i x) (1 / 3) + 1 / 3

theorem continuous_sideRawParam (f : K.Face) (i : ZMod 3) :
    Continuous (sideRawParam f i) := by
  apply Continuous.add _ continuous_const
  apply Continuous.div
  · exact (continuous_triCoord _).sub continuous_const
  · exact (continuous_sideDepth i).max continuous_const
  · intro x
    have : (0 : ℝ) < max (sideDepth i x) (1 / 3) :=
      lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    exact ne_of_gt this

/-- The comparison piece adapted to side `i`: the original face chart evaluated on the clamped
radial interpolation from the barycenter to the reparametrized side point. -/
noncomputable def sidePiece (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (x : Plane) : Plane :=
  faceOriginalMap G f (AffineMap.lineMap triCenter
    (K.faceEdgeSourcePoint f i
      (sideParamProfile G f i (unitClamp (sideRawParam f i x))))
    (unitClamp (3 * sideDepth i x - 1)))

/-- The domain point fed to the original chart by a side piece. -/
theorem sidePiece_arg_mem (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (x : Plane) :
    AffineMap.lineMap triCenter
      (K.faceEdgeSourcePoint f i
        (sideParamProfile G f i (unitClamp (sideRawParam f i x))))
      (unitClamp (3 * sideDepth i x - 1)) ∈ standardFaceRegion := by
  apply lineMap_unitClamp_mem convex_standardFaceRegion
    triCenter_mem_standardFaceRegion
  exact K.faceEdgeSourcePoint_mem_region f i
    (sideParamProfile_mem G f i (unitClamp_mem _))

theorem sidePiece_mem_faceImage (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) (x : Plane) :
    sidePiece G f i x ∈ G.map '' faceInSupport (K := K) f := by
  rw [sidePiece]
  exact faceOriginalMap_mem_face_image (G := G) f
    ⟨_, K.sidePiece_arg_mem G f i x⟩

theorem continuous_sidePiece (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) : Continuous (sidePiece G f i) := by
  apply (continuousOn_faceOriginalMap (G := G) f).comp_continuous
  · have hpt : Continuous fun x : Plane =>
        K.faceEdgeSourcePoint f i
          (sideParamProfile G f i (unitClamp (sideRawParam f i x))) :=
      (K.continuous_faceEdgeSourcePoint f i).comp
        ((continuous_sideParamProfile G f i).comp
          (continuous_unitClamp.comp (K.continuous_sideRawParam f i)))
    have hcoef : Continuous fun x : Plane =>
        unitClamp (3 * sideDepth i x - 1) :=
      continuous_unitClamp.comp
        (((continuous_const.mul (continuous_sideDepth i)).sub continuous_const))
    simp only [AffineMap.lineMap_apply_module]
    exact ((continuous_const.sub hcoef).smul continuous_const).add (hcoef.smul hpt)
  · intro x
    exact K.sidePiece_arg_mem G f i x

/-! ## Evaluation of a side piece -/

theorem unitClamp_of_nonpos {t : ℝ} (ht : t ≤ 0) : unitClamp t = 0 := by
  rw [unitClamp, min_eq_right (ht.trans zero_le_one), max_eq_left ht]

theorem unitClamp_of_one_le {t : ℝ} (ht : 1 ≤ t) : unitClamp t = 1 := by
  rw [unitClamp, min_eq_left ht]
  exact max_eq_right zero_le_one

/-- On the side itself the raw parameter is the oriented affine side parameter. -/
theorem sideRawParam_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    sideRawParam f i (K.faceEdgeSourcePoint f i r) = r := by
  rw [sideRawParam, sideDepth, K.triCoord_oppIndex_sourcePoint f i r,
    K.triCoord_secondIndex_sourcePoint f i r]
  norm_num

theorem sideDepth_sourcePoint (f : K.Face) (i : ZMod 3) (r : ℝ) :
    sideDepth i (K.faceEdgeSourcePoint f i r) = 1 := by
  rw [sideDepth, K.triCoord_oppIndex_sourcePoint f i r]
  norm_num

/-- A side piece evaluated on its own side is the reparametrized original boundary chart. -/
theorem sidePiece_sourcePoint (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    sidePiece G f i (K.faceEdgeSourcePoint f i r) =
      faceOriginalMap G f
        (K.faceEdgeSourcePoint f i (sideParamProfile G f i r)) := by
  rw [sidePiece, K.sideRawParam_sourcePoint f i r, K.sideDepth_sourcePoint f i r,
    unitClamp_of_mem hr, unitClamp_of_one_le (by norm_num),
    AffineMap.lineMap_apply_one]

/-- The first-corner evaluation: whenever the first endpoint coordinate agrees with the
opposite coordinate, the side piece interpolates toward the second corner. -/
theorem sidePiece_of_firstCoord_eq (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {x : Plane}
    (hcc : triCoord (K.faceEdgeFirstIndex f i) x =
      triCoord (standardOppIndex i) x) :
    sidePiece G f i x =
      faceOriginalMap G f (AffineMap.lineMap triCenter
        (standardTriangleVertex (K.faceEdgeSecondIndex f i))
        (unitClamp (3 * sideDepth i x - 1))) := by
  by_cases hd : 1 / 3 ≤ sideDepth i x
  · have hsum := K.triCoord_side_sum f i x
    have hraw : sideRawParam f i x = 1 := by
      rw [sideRawParam, max_eq_left hd]
      have hden : sideDepth i x ≠ 0 := by
        intro h0
        rw [h0] at hd
        norm_num at hd
      have hnum : triCoord (K.faceEdgeSecondIndex f i) x - 1 / 3 =
          2 / 3 * sideDepth i x := by
        rw [sideDepth]
        linarith
      rw [hnum, mul_div_assoc, div_self hden]
      norm_num
    rw [sidePiece, hraw, unitClamp_one, sideParamProfile_one,
      faceEdgeSourcePoint_one]
  · push Not at hd
    have hcoef : unitClamp (3 * sideDepth i x - 1) = 0 :=
      unitClamp_of_nonpos (by linarith)
    rw [sidePiece, hcoef, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_zero]

/-- The second-corner evaluation: whenever the second endpoint coordinate agrees with the
opposite coordinate, the side piece interpolates toward the first corner. -/
theorem sidePiece_of_secondCoord_eq (G : K.PlaneGraphRealization) (f : K.Face)
    (i : ZMod 3) {x : Plane}
    (hcc : triCoord (K.faceEdgeSecondIndex f i) x =
      triCoord (standardOppIndex i) x) :
    sidePiece G f i x =
      faceOriginalMap G f (AffineMap.lineMap triCenter
        (standardTriangleVertex (K.faceEdgeFirstIndex f i))
        (unitClamp (3 * sideDepth i x - 1))) := by
  by_cases hd : 1 / 3 ≤ sideDepth i x
  · have hraw : sideRawParam f i x = 0 := by
      rw [sideRawParam, max_eq_left hd]
      have hden : sideDepth i x ≠ 0 := by
        intro h0
        rw [h0] at hd
        norm_num at hd
      have hnum : triCoord (K.faceEdgeSecondIndex f i) x - 1 / 3 =
          -(1 / 3) * sideDepth i x := by
        rw [sideDepth, hcc]
        ring
      rw [hnum, mul_div_assoc, div_self hden]
      norm_num
    rw [sidePiece, hraw, unitClamp_zero, sideParamProfile_zero,
      faceEdgeSourcePoint_zero]
  · push Not at hd
    have hcoef : unitClamp (3 * sideDepth i x - 1) = 0 :=
      unitClamp_of_nonpos (by linarith)
    rw [sidePiece, hcoef, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_zero]

/-! ## Agreement of adjacent side pieces -/

theorem standardOppIndex_succ (i : ZMod 3) :
    standardOppIndex (i + 1) = (ZMod.finEquiv 3).symm i := by
  rw [standardOppIndex]
  congr 1
  have h30 : (3 : ZMod 3) = 0 := by decide
  calc i + 1 + 2 = i + 3 := by ring
    _ = i := by rw [h30, add_zero]

theorem standardOppIndex_succ_succ (i : ZMod 3) :
    standardOppIndex (i + 2) = (ZMod.finEquiv 3).symm (i + 1) := by
  rw [standardOppIndex]
  congr 1
  have h30 : (3 : ZMod 3) = 0 := by decide
  calc i + 2 + 2 = i + 1 + 3 := by ring
    _ = i + 1 := by rw [h30, add_zero]

/-- Two side pieces agree wherever their opposite coordinates agree.  This is the closed
interface condition of the sector decomposition; no minimality is required. -/
theorem sidePiece_interface (G : K.PlaneGraphRealization) (f : K.Face)
    {i i' : ZMod 3} (hne : i ≠ i') {x : Plane}
    (heq : triCoord (standardOppIndex i) x =
      triCoord (standardOppIndex i') x) :
    sidePiece G f i x = sidePiece G f i' x := by
  have hdepth : sideDepth i x = sideDepth i' x := by
    rw [sideDepth, sideDepth, heq]
  have hcase : i' = i + 1 ∨ i' = i + 2 := by
    have h3 : ∀ a b : ZMod 3, a ≠ b → b = a + 1 ∨ b = a + 2 := by decide
    exact h3 i i' hne
  have h30 : (3 : ZMod 3) = 0 := by decide
  rcases hcase with rfl | rfl
  · -- shared corner: `symm (i + 1)`
    have hopp' : standardOppIndex (i + 1) = (ZMod.finEquiv 3).symm i :=
      standardOppIndex_succ i
    have e1 : i + 1 + 1 = i + 2 := by ring
    have hleft : sidePiece G f i x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1)))
          (unitClamp (3 * sideDepth i x - 1))) := by
      rcases K.faceEdge_index_cases f i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have hcc : triCoord (K.faceEdgeFirstIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₁, ← hopp', ← heq]
        rw [K.sidePiece_of_firstCoord_eq G f i hcc, h₂]
      · have hcc : triCoord (K.faceEdgeSecondIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₂, ← hopp', ← heq]
        rw [K.sidePiece_of_secondCoord_eq G f i hcc, h₁]
    have hright : sidePiece G f (i + 1) x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1)))
          (unitClamp (3 * sideDepth (i + 1) x - 1))) := by
      rcases K.faceEdge_index_cases f (i + 1) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · -- forward: the second endpoint of side `i + 1` is the opposite corner of side `i`
        have hcc : triCoord (K.faceEdgeSecondIndex f (i + 1)) x =
            triCoord (standardOppIndex (i + 1)) x := by
          rw [h₂, e1]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_secondCoord_eq G f (i + 1) hcc, h₁]
      · have hcc : triCoord (K.faceEdgeFirstIndex f (i + 1)) x =
            triCoord (standardOppIndex (i + 1)) x := by
          rw [h₁, e1]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_firstCoord_eq G f (i + 1) hcc, h₂]
    rw [hleft, hright, hdepth]
  · -- shared corner: `symm i`
    have hopp' : standardOppIndex (i + 2) = (ZMod.finEquiv 3).symm (i + 1) :=
      standardOppIndex_succ_succ i
    have e2 : i + 2 + 1 = i := by
      calc i + 2 + 1 = i + 3 := by ring
        _ = i := by rw [h30, add_zero]
    have hleft : sidePiece G f i x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm i))
          (unitClamp (3 * sideDepth i x - 1))) := by
      rcases K.faceEdge_index_cases f i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · -- forward: the second endpoint `symm (i + 1)` is the opposite corner of side `i + 2`
        have hcc : triCoord (K.faceEdgeSecondIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₂, ← hopp', ← heq]
        rw [K.sidePiece_of_secondCoord_eq G f i hcc, h₁]
      · have hcc : triCoord (K.faceEdgeFirstIndex f i) x =
            triCoord (standardOppIndex i) x := by
          rw [h₁, ← hopp', ← heq]
        rw [K.sidePiece_of_firstCoord_eq G f i hcc, h₂]
    have hright : sidePiece G f (i + 2) x =
        faceOriginalMap G f (AffineMap.lineMap triCenter
          (standardTriangleVertex ((ZMod.finEquiv 3).symm i))
          (unitClamp (3 * sideDepth (i + 2) x - 1))) := by
      rcases K.faceEdge_index_cases f (i + 2) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · -- forward: the first endpoint of side `i + 2` is the opposite corner of side `i`
        have hcc : triCoord (K.faceEdgeFirstIndex f (i + 2)) x =
            triCoord (standardOppIndex (i + 2)) x := by
          rw [h₁]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_firstCoord_eq G f (i + 2) hcc, h₂, e2]
      · have hcc : triCoord (K.faceEdgeSecondIndex f (i + 2)) x =
            triCoord (standardOppIndex (i + 2)) x := by
          rw [h₂]
          change triCoord (standardOppIndex i) x = _
          rw [heq]
        rw [K.sidePiece_of_secondCoord_eq G f (i + 2) hcc, h₁, e2]
    rw [hleft, hright, hdepth]

/-! ## The assembled facewise comparison map -/

/-- The comparison map of one face: the three side pieces glued over the closed sectors on
which the corresponding opposite coordinate is minimal. -/
noncomputable def facewiseComparison (G : K.PlaneGraphRealization) (f : K.Face)
    (x : Plane) : Plane :=
  if triCoord (standardOppIndex 0) x ≤
      min (triCoord (standardOppIndex 1) x) (triCoord (standardOppIndex 2) x) then
    sidePiece G f 0 x
  else if triCoord (standardOppIndex 1) x ≤ triCoord (standardOppIndex 2) x then
    sidePiece G f 1 x
  else sidePiece G f 2 x

theorem facewiseComparison_mem_faceImage (G : K.PlaneGraphRealization)
    (f : K.Face) (x : Plane) :
    facewiseComparison G f x ∈ G.map '' faceInSupport (K := K) f := by
  rw [facewiseComparison]
  split_ifs <;> exact K.sidePiece_mem_faceImage G f _ x

theorem continuousOn_facewiseComparison (G : K.PlaneGraphRealization)
    (f : K.Face) :
    ContinuousOn (facewiseComparison G f) standardFaceRegion := by
  apply ContinuousOn.if
  · rintro a ⟨-, haF⟩
    have haeq : triCoord (standardOppIndex 0) a =
        min (triCoord (standardOppIndex 1) a) (triCoord (standardOppIndex 2) a) :=
      frontier_le_subset_eq (continuous_triCoord _)
        ((continuous_triCoord _).min (continuous_triCoord _)) haF
    by_cases h12 : triCoord (standardOppIndex 1) a ≤ triCoord (standardOppIndex 2) a
    · have h01 : triCoord (standardOppIndex 0) a =
          triCoord (standardOppIndex 1) a := by
        rw [haeq, min_eq_left h12]
      rw [K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 1) h01, ite_eq_left h12]
    · have h02 : triCoord (standardOppIndex 0) a =
          triCoord (standardOppIndex 2) a := by
        rw [haeq, min_eq_right (le_of_not_ge h12)]
      rw [K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 2) h02, ite_eq_right h12]
  · exact (K.continuous_sidePiece G f 0).continuousOn
  · apply ContinuousOn.if
    · rintro a ⟨-, haF⟩
      have haeq : triCoord (standardOppIndex 1) a =
          triCoord (standardOppIndex 2) a :=
        frontier_le_subset_eq (continuous_triCoord _) (continuous_triCoord _) haF
      exact K.sidePiece_interface G f (by decide : (1 : ZMod 3) ≠ 2) haeq
    · exact (K.continuous_sidePiece G f 1).continuousOn
    · exact (K.continuous_sidePiece G f 2).continuousOn

/-- On the closed sector of side `i` — in fact anywhere the opposite coordinate of side `i`
vanishes — the comparison map is the side-`i` piece. -/
theorem facewiseComparison_eq_sidePiece (G : K.PlaneGraphRealization)
    (f : K.Face) (i : ZMod 3) {x : Plane} (hx : x ∈ standardFaceRegion)
    (hzero : triCoord (standardOppIndex i) x = 0) :
    facewiseComparison G f x = sidePiece G f i x := by
  have hnn : ∀ j : Fin 3, 0 ≤ triCoord j x := mem_standardFaceRegion_iff.mp hx
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    have h3 : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
    exact h3 i
  rw [facewiseComparison]
  rcases hi with rfl | rfl | rfl
  · rw [ite_eq_left]
    rw [hzero]
    exact le_min (hnn _) (hnn _)
  · split_ifs with h₀ h₁
    · apply K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 1)
      have h₀' : triCoord (standardOppIndex 0) x ≤ 0 := by
        rw [← hzero]
        exact h₀.trans (min_le_left _ _)
      rw [le_antisymm h₀' (hnn _), hzero]
    · rfl
    · exact absurd (hzero ▸ hnn (standardOppIndex 2)) h₁
  · split_ifs with h₀ h₁
    · apply K.sidePiece_interface G f (by decide : (0 : ZMod 3) ≠ 2)
      have h₀' : triCoord (standardOppIndex 0) x ≤ 0 := by
        rw [← hzero]
        exact h₀.trans (min_le_right _ _)
      rw [le_antisymm h₀' (hnn _), hzero]
    · apply K.sidePiece_interface G f (by decide : (1 : ZMod 3) ≠ 2)
      have h₁' : triCoord (standardOppIndex 1) x ≤ 0 := hzero ▸ h₁
      rw [le_antisymm h₁' (hnn _), hzero]
    · rfl

/-! ## The boundary estimate -/

private theorem dist_completePath_comparison_lt_of_middle (G : K.PlaneGraphRealization)
    (f : K.Face) (i : ZMod 3)
    (htube : G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) (hr2 : ¬r ≤ 1 / 2) (hr34 : r ≤ 3 / 4) :
    dist ((G.replacementArc (K.faceEdge f i)).completePath ⟨r, hr⟩)
        (faceOriginalMap G f
          (K.faceEdgeSourcePoint f i (sideParamProfile G f i r))) <
      faceVertexSeparationRadius G f / 2 := by
  set e := K.faceEdge f i with he
  set A := G.replacementArc e with hA
  have hXl : A.exitData.left ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg,
      A.exitData.left_lt_right.le.trans A.exitData.right_le_one⟩
  have hXr : A.exitData.right ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg.trans A.exitData.left_lt_right.le,
      A.exitData.right_le_one⟩
  have hw : (0 : ℝ) ≤ 2 * (2 * r - 1) ∧ 2 * (2 * r - 1) ≤ 1 := by
    constructor <;> nlinarith [not_le.mp hr2]
  have hcp : A.completePath ⟨r, hr⟩ =
      A.parameterizationData.curve
        (AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1))) := by
    rw [CentralPolygonalArc.completePath, Path.trans_apply]
    rw [dite_eq_right (show ¬ ((⟨r, hr⟩ : unitInterval) : ℝ) ≤ 1 / 2 from hr2)]
    rw [Path.trans_apply]
    rw [dite_eq_left (by
      change (2 * ((⟨r, hr⟩ : unitInterval) : ℝ) - 1) ≤ 1 / 2
      linarith)]
    change A.parameterizationData.curve
        (Path.segment A.exitData.left A.exitData.right _) = _
    rw [Path.segment_apply]
  have hprofile : sideParamProfile G f i r =
      AffineMap.lineMap (sideTrimLeft G f i) (sideTrimRight G f i) (4 * r - 2) := by
    rw [sideParamProfile, ite_eq_right hr2, ite_eq_left hr34]
  have hT : AffineMap.lineMap (sideTrimLeft G f i) (sideTrimRight G f i) (4 * r - 2) =
      (G.edgeTrim e).left + ((G.edgeTrim e).right - (G.edgeTrim e).left) *
        (AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1))) := by
    simp only [sideTrimLeft, sideTrimRight, AffineMap.lineMap_apply_ring]
    rw [← he]
    ring
  have htmem : AffineMap.lineMap A.exitData.left A.exitData.right
      (2 * (2 * r - 1)) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [AffineMap.lineMap_apply_ring]
    have hlr := A.exitData.left_lt_right
    constructor <;> nlinarith [hXl.1, hXl.2, hXr.1, hXr.2, hw.1, hw.2]
  have hpmem : sideParamProfile G f i r ∈ Set.Icc (0 : ℝ) 1 :=
    sideParamProfile_mem G f i hr
  rw [hcp, K.faceOriginalMap_sourcePoint f i hpmem, hprofile, hT]
  have hclose := A.curve_close _ htmem
  calc
    dist (A.parameterizationData.curve
        (AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1))))
        (G.chartEdgeCurve e ((G.edgeTrim e).left +
          ((G.edgeTrim e).right - (G.edgeTrim e).left) *
            AffineMap.lineMap A.exitData.left A.exitData.right (2 * (2 * r - 1)))) <
      G.centralTubeRadius e := hclose
    _ ≤ faceVertexSeparationRadius G f / 2 := by
      have := htube.trans (comparisonScale_le G f)
      linarith [faceVertexSeparationRadius_pos (G := G) f]

/-- The complete replacement path of one side stays within half the face separation radius of
the reparametrized original boundary chart, once the vertex isolation disks and the central
tube are below the comparison scale. -/
theorem dist_completePath_comparison_lt (G : K.PlaneGraphRealization)
    (f : K.Face) (i : ZMod 3)
    (hiso₁ : G.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
      comparisonScale G f)
    (hiso₂ : G.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
      comparisonScale G f)
    (htube : G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    dist ((G.replacementArc (K.faceEdge f i)).completePath ⟨r, hr⟩)
        (faceOriginalMap G f
          (K.faceEdgeSourcePoint f i (sideParamProfile G f i r))) <
      faceVertexSeparationRadius G f / 2 := by
  classical
  set e := K.faceEdge f i with he
  set A := G.replacementArc e with hA
  set eta := comparisonScale G f with heta
  set rsep := faceVertexSeparationRadius G f with hrsep
  have hrsep_pos : 0 < rsep := faceVertexSeparationRadius_pos (G := G) f
  have heta8 : eta ≤ rsep / 8 := comparisonScale_le G f
  have hXl : A.exitData.left ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg,
      A.exitData.left_lt_right.le.trans A.exitData.right_le_one⟩
  have hXr : A.exitData.right ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨A.exitData.left_nonneg.trans A.exitData.left_lt_right.le,
      A.exitData.right_le_one⟩
  -- the two matched endpoint estimates
  have hPLQ : dist A.leftEndpoint (G.chartEdgeCurve e (sideTrimLeft G f i)) <
      G.centralTubeRadius e := by
    have hclose := A.curve_close A.exitData.left hXl
    have harg : (G.edgeTrim e).left +
        ((G.edgeTrim e).right - (G.edgeTrim e).left) * A.exitData.left =
        sideTrimLeft G f i := by
      rw [sideTrimLeft, AffineMap.lineMap_apply_ring, ← he]
      ring
    rw [harg] at hclose
    exact hclose
  have hPRQ : dist A.rightEndpoint (G.chartEdgeCurve e (sideTrimRight G f i)) <
      G.centralTubeRadius e := by
    have hclose := A.curve_close A.exitData.right hXr
    have harg : (G.edgeTrim e).left +
        ((G.edgeTrim e).right - (G.edgeTrim e).left) * A.exitData.right =
        sideTrimRight G f i := by
      rw [sideTrimRight, AffineMap.lineMap_apply_ring, ← he]
      ring
    rw [harg] at hclose
    exact hclose
  -- chart values at the distinguished side parameters
  have hsrc0 : faceOriginalMap G f (K.faceEdgeSourcePoint f i 0) =
      G.vertexImage (K.edgeFirst e) := by
    rw [K.faceOriginalMap_sourcePoint f i (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)]
    exact G.chartEdgeCurve_zero e
  have hsrc1 : faceOriginalMap G f (K.faceEdgeSourcePoint f i 1) =
      G.vertexImage (K.edgeSecond e) := by
    rw [K.faceOriginalMap_sourcePoint f i (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
    exact G.chartEdgeCurve_one e
  have hsrcL : faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) =
      G.chartEdgeCurve e (sideTrimLeft G f i) :=
    K.faceOriginalMap_sourcePoint f i (sideTrimLeft_mem G f i)
  have hsrcR : faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimRight G f i)) =
      G.chartEdgeCurve e (sideTrimRight G f i) :=
    K.faceOriginalMap_sourcePoint f i (sideTrimRight_mem G f i)
  -- the modulus premises at the two corners
  have hmodL : dist (faceOriginalMap G f (K.faceEdgeSourcePoint f i 0))
      (faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimLeft G f i))) ≤
      2 * eta := by
    rw [hsrc0, hsrcL]
    calc dist (G.vertexImage (K.edgeFirst e))
          (G.chartEdgeCurve e (sideTrimLeft G f i)) ≤
        dist (G.vertexImage (K.edgeFirst e)) A.leftEndpoint +
          dist A.leftEndpoint (G.chartEdgeCurve e (sideTrimLeft G f i)) :=
          dist_triangle _ _ _
      _ ≤ G.vertexIsolationRadius (K.edgeFirst e) + G.centralTubeRadius e := by
          apply add_le_add _ hPLQ.le
          rw [dist_comm]
          exact (A.leftEndpoint_on_sphere).le
      _ ≤ 2 * eta := by rw [two_mul]; exact add_le_add hiso₁ htube
  have hmodR : dist (faceOriginalMap G f (K.faceEdgeSourcePoint f i 1))
      (faceOriginalMap G f (K.faceEdgeSourcePoint f i (sideTrimRight G f i))) ≤
      2 * eta := by
    rw [hsrc1, hsrcR]
    calc dist (G.vertexImage (K.edgeSecond e))
          (G.chartEdgeCurve e (sideTrimRight G f i)) ≤
        dist (G.vertexImage (K.edgeSecond e)) A.rightEndpoint +
          dist A.rightEndpoint (G.chartEdgeCurve e (sideTrimRight G f i)) :=
          dist_triangle _ _ _
      _ ≤ G.vertexIsolationRadius (K.edgeSecond e) + G.centralTubeRadius e := by
          apply add_le_add _ hPRQ.le
          rw [dist_comm]
          exact (A.rightEndpoint_on_sphere).le
      _ ≤ 2 * eta := by rw [two_mul]; exact add_le_add hiso₂ htube
  by_cases hr2 : r ≤ 1 / 2
  · -- left spoke
    have hcp : A.completePath ⟨r, hr⟩ =
        AffineMap.lineMap (G.vertexImage (K.edgeFirst e)) A.leftEndpoint
          (2 * r) := by
      rw [CentralPolygonalArc.completePath, Path.trans_apply]
      rw [dite_eq_left (show ((⟨r, hr⟩ : unitInterval) : ℝ) ≤ 1 / 2 from hr2)]
      rw [Path.segment_apply]
    have hprofile : sideParamProfile G f i r = 2 * r * sideTrimLeft G f i := by
      rw [sideParamProfile, ite_eq_left hr2]
    have hsrcpt : K.faceEdgeSourcePoint f i (2 * r * sideTrimLeft G f i) =
        AffineMap.lineMap (K.faceEdgeSourcePoint f i 0)
          (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) (2 * r) := by
      have harg : 2 * r * sideTrimLeft G f i =
          AffineMap.lineMap (0 : ℝ) (sideTrimLeft G f i) (2 * r) := by
        rw [AffineMap.lineMap_apply_ring]
        ring
      rw [harg, faceEdgeSourcePoint]
      exact (AffineMap.lineMap _ _).apply_lineMap _ _ _
    rw [hcp, hprofile, hsrcpt]
    have h2r : (2 : ℝ) * r ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [hr.1], by linarith⟩
    calc dist (AffineMap.lineMap (G.vertexImage (K.edgeFirst e))
            A.leftEndpoint (2 * r))
          (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 0)
            (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) (2 * r))) ≤
        dist (AffineMap.lineMap (G.vertexImage (K.edgeFirst e))
            A.leftEndpoint (2 * r)) (G.vertexImage (K.edgeFirst e)) +
          dist (G.vertexImage (K.edgeFirst e))
            (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 0)
              (K.faceEdgeSourcePoint f i (sideTrimLeft G f i)) (2 * r))) :=
          dist_triangle _ _ _
      _ ≤ G.vertexIsolationRadius (K.edgeFirst e) + rsep / 4 := by
          apply add_le_add
          · rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg h2r.1]
            calc 2 * r * dist (G.vertexImage (K.edgeFirst e)) A.leftEndpoint ≤
                1 * dist (G.vertexImage (K.edgeFirst e)) A.leftEndpoint :=
                  mul_le_mul_of_nonneg_right h2r.2 dist_nonneg
              _ = G.vertexIsolationRadius (K.edgeFirst e) := by
                  rw [one_mul, dist_comm]
                  exact A.leftEndpoint_on_sphere
          · rw [← hsrc0, dist_comm]
            exact comparisonScale_segment G f
              (K.faceEdgeSourcePoint_mem_region f i (by norm_num))
              (K.faceEdgeSourcePoint_mem_region f i (sideTrimLeft_mem G f i))
              hmodL h2r
      _ < rsep / 2 := by
          have : G.vertexIsolationRadius (K.edgeFirst e) ≤ rsep / 8 :=
            hiso₁.trans heta8
          linarith
  · by_cases hr34 : r ≤ 3 / 4
    · -- middle range
      exact dist_completePath_comparison_lt_of_middle G f i htube hr hr2 hr34
    · -- right spoke
      push Not at hr2 hr34
      have hw : (0 : ℝ) ≤ 2 * (2 * r - 1) - 1 ∧ 2 * (2 * r - 1) - 1 ≤ 1 := by
        constructor <;> nlinarith [hr.2]
      have hcp : A.completePath ⟨r, hr⟩ =
          AffineMap.lineMap A.rightEndpoint (G.vertexImage (K.edgeSecond e))
            (2 * (2 * r - 1) - 1) := by
        rw [CentralPolygonalArc.completePath, Path.trans_apply]
        rw [dite_eq_right (by linarith : ¬ ((⟨r, hr⟩ : unitInterval) : ℝ) ≤ 1 / 2)]
        rw [Path.trans_apply]
        rw [dite_eq_right (by
          change ¬ (2 * ((⟨r, hr⟩ : unitInterval) : ℝ) - 1) ≤ 1 / 2
          linarith)]
        rw [Path.segment_apply]
      have hprofile : sideParamProfile G f i r =
          AffineMap.lineMap (sideTrimRight G f i) 1 (4 * r - 3) := by
        rw [sideParamProfile, ite_eq_right (not_le.mpr hr2), ite_eq_right (not_le.mpr hr34)]
      have hw' : 4 * r - 3 = 2 * (2 * r - 1) - 1 := by ring
      have hsrcpt : K.faceEdgeSourcePoint f i
          (AffineMap.lineMap (sideTrimRight G f i) 1 (4 * r - 3)) =
          AffineMap.lineMap (K.faceEdgeSourcePoint f i 1)
            (K.faceEdgeSourcePoint f i (sideTrimRight G f i))
            (1 - (2 * (2 * r - 1) - 1)) := by
        rw [faceEdgeSourcePoint]
        rw [show AffineMap.lineMap (sideTrimRight G f i) (1:ℝ) (4 * r - 3) =
            AffineMap.lineMap (1:ℝ) (sideTrimRight G f i)
              (1 - (2 * (2 * r - 1) - 1)) by
          simp only [AffineMap.lineMap_apply_ring]
          ring]
        exact (AffineMap.lineMap _ _).apply_lineMap _ _ _
      rw [hcp, hprofile, hsrcpt]
      have h1w : (1 : ℝ) - (2 * (2 * r - 1) - 1) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [hw.2], by linarith [hw.1]⟩
      calc dist (AffineMap.lineMap A.rightEndpoint
              (G.vertexImage (K.edgeSecond e)) (2 * (2 * r - 1) - 1))
            (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 1)
              (K.faceEdgeSourcePoint f i (sideTrimRight G f i))
              (1 - (2 * (2 * r - 1) - 1)))) ≤
          dist (AffineMap.lineMap A.rightEndpoint
              (G.vertexImage (K.edgeSecond e)) (2 * (2 * r - 1) - 1))
            (G.vertexImage (K.edgeSecond e)) +
            dist (G.vertexImage (K.edgeSecond e))
              (faceOriginalMap G f (AffineMap.lineMap (K.faceEdgeSourcePoint f i 1)
                (K.faceEdgeSourcePoint f i (sideTrimRight G f i))
                (1 - (2 * (2 * r - 1) - 1)))) := dist_triangle _ _ _
        _ ≤ G.vertexIsolationRadius (K.edgeSecond e) + rsep / 4 := by
            apply add_le_add
            · rw [dist_lineMap_right, Real.norm_eq_abs,
                abs_of_nonneg (by linarith [hw.2] : (0:ℝ) ≤ 1 - (2 * (2 * r - 1) - 1))]
              calc (1 - (2 * (2 * r - 1) - 1)) *
                  dist A.rightEndpoint (G.vertexImage (K.edgeSecond e)) ≤
                  1 * dist A.rightEndpoint (G.vertexImage (K.edgeSecond e)) :=
                    mul_le_mul_of_nonneg_right (by linarith [hw.1]) dist_nonneg
                _ = G.vertexIsolationRadius (K.edgeSecond e) := by
                    rw [one_mul]
                    exact A.rightEndpoint_on_sphere
            · rw [← hsrc1, dist_comm]
              exact comparisonScale_segment G f
                (K.faceEdgeSourcePoint_mem_region f i (by norm_num))
                (K.faceEdgeSourcePoint_mem_region f i (sideTrimRight_mem G f i))
                hmodR h1w
        _ < rsep / 2 := by
            have : G.vertexIsolationRadius (K.edgeSecond e) ≤ rsep / 8 :=
              hiso₂.trans heta8
            linarith

/-- The graph replacement on one face boundary stays within half the face separation radius of
the facewise comparison map. -/
theorem facewiseComparison_close (G : K.PlaneGraphRealization) (f : K.Face)
    (hiso : ∀ i : ZMod 3,
      G.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
          comparisonScale G f ∧
        G.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
          comparisonScale G f)
    (htube : ∀ i : ZMod 3,
      G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    (q : StandardFaceBoundary) :
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
        (facewiseComparison G f q.1) < faceVertexSeparationRadius G f / 2 := by
  have hqSide : q.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using q.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqSide
  rw [← IntrinsicTwoComplex.standard_cellCarrier_faceStandardEdge i,
    ← K.faceEdgeSourcePoint_image_Icc f i] at hi
  obtain ⟨r, hrIcc, hrq⟩ := hi
  have hLHS : G.graphReplacementMap (K.faceBoundaryLift f q) =
      (G.replacementArc (K.faceEdge f i)).completePath ⟨r, hrIcc⟩ := by
    rw [← K.faceBoundaryMap_apply (G := G) f q, ← hrq]
    exact K.faceBoundaryMap_sourcePoint (G := G) f i ⟨r, hrIcc⟩
  have hRHS : facewiseComparison G f q.1 =
      faceOriginalMap G f
        (K.faceEdgeSourcePoint f i (sideParamProfile G f i r)) := by
    rw [← hrq]
    rw [K.facewiseComparison_eq_sidePiece G f i
      (K.faceEdgeSourcePoint_mem_region f i hrIcc)
      (K.triCoord_oppIndex_sourcePoint f i r)]
    exact K.sidePiece_sourcePoint G f i hrIcc
  rw [hLHS, hRHS]
  exact K.dist_completePath_comparison_lt G f i (hiso i).1 (hiso i).2 (htube i) hrIcc

/-- The complete cellwise compatibility package from comparison-scale-small approximation
data.  This is the honest side-preservation discharge for the locally finite Chapter 6
replacement: no same-parameter mesh estimate enters. -/
theorem cellwiseCompatibility_of_comparisonScale (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices)
    (hiso : ∀ (f : K.Face) (i : ZMod 3),
      G.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
          comparisonScale G f ∧
        G.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
          comparisonScale G f)
    (htube : ∀ (f : K.Face) (i : ZMod 3),
      G.centralTubeRadius (K.faceEdge f i) ≤ comparisonScale G f)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    K.CellwiseCompatibility G := by
  apply cellwiseCompatibility_of_comparison hfaces
    (fun f => facewiseComparison G f)
    (fun f => K.continuousOn_facewiseComparison G f)
    (fun f p _ => Metric.self_subset_cthickening _
      (K.facewiseComparison_mem_faceImage G f p))
    (fun f q => K.facewiseComparison_close G f (hiso f) (htube f) q)
    hregion hloc

/-! ## Choosing the approximation controls below every incident comparison scale -/

/-- The support point of a global vertex. -/
noncomputable def vertexSupportPoint (K : LocallyFiniteTriangleComplex S) (v : K.Vertex) :
    K.support :=
  ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩

/-- The minimum comparison scale among the finitely many faces through a vertex. -/
noncomputable def comparisonVertexControl (G : K.PlaneGraphRealization)
    (v : K.Vertex) : ℝ :=
  ((facesContaining (K := K) (K.vertexSupportPoint v)).image
    (comparisonScale G)).min' ((facesContaining_nonempty _).image _)

theorem comparisonVertexControl_pos (G : K.PlaneGraphRealization)
    (v : K.Vertex) : 0 < comparisonVertexControl G v := by
  have hmem := Finset.min'_mem
    ((facesContaining (K := K) (K.vertexSupportPoint v)).image (comparisonScale G))
    ((facesContaining_nonempty _).image _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  rw [comparisonVertexControl, ← hf]
  exact comparisonScale_pos G f

theorem comparisonVertexControl_le (G : K.PlaneGraphRealization)
    {v : K.Vertex} {f : K.Face} (hv : v ∈ K.faceVertices f) :
    comparisonVertexControl G v ≤ comparisonScale G f := by
  apply Finset.min'_le
  apply Finset.mem_image_of_mem
  exact mem_facesContaining.mpr
    ((K.vertexSupportPoint_mem_faceInSupport_iff f v).mpr hv)

/-- The minimum comparison scale among the finitely many faces meeting an edge. -/
noncomputable def comparisonEdgeControl (G : K.PlaneGraphRealization)
    (e : K.Edge) : ℝ :=
  ((finite_edgeMeetingFaces (K := K) e).toFinset.image
    (comparisonScale G)).min'
    (Finset.Nonempty.image
      ⟨K.edgeFace e, (Set.Finite.mem_toFinset _).mpr
        (K.edgeFace_mem_edgeMeetingFaces e)⟩ _)

theorem comparisonEdgeControl_pos (G : K.PlaneGraphRealization) (e : K.Edge) :
    0 < comparisonEdgeControl G e := by
  have hmem := Finset.min'_mem
    ((finite_edgeMeetingFaces (K := K) e).toFinset.image (comparisonScale G))
    (Finset.Nonempty.image
      ⟨K.edgeFace e, (Set.Finite.mem_toFinset _).mpr
        (K.edgeFace_mem_edgeMeetingFaces e)⟩ _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  rw [comparisonEdgeControl, ← hf]
  exact comparisonScale_pos G f

theorem comparisonEdgeControl_le (G : K.PlaneGraphRealization)
    {e : K.Edge} {f : K.Face} (hf : f ∈ K.edgeMeetingFaces e) :
    comparisonEdgeControl G e ≤ comparisonScale G f := by
  apply Finset.min'_le
  exact Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).mpr hf)

/-! ## Invariance of the comparison data under control shrinking -/

theorem faceVertexSeparationRadius_withApproximationControls
    (G : K.PlaneGraphRealization)
    (vc : K.Vertex → ℝ) (hvc : ∀ v, 0 < vc v)
    (ec : K.Edge → ℝ) (hec : ∀ e, 0 < ec e) (f : K.Face) :
    faceVertexSeparationRadius (G.withApproximationControls vc hvc ec hec) f =
      faceVertexSeparationRadius G f := rfl

theorem comparisonScale_withApproximationControls (G : K.PlaneGraphRealization)
    (vc : K.Vertex → ℝ) (hvc : ∀ v, 0 < vc v)
    (ec : K.Edge → ℝ) (hec : ∀ e, 0 < ec e) (f : K.Face) :
    comparisonScale (G.withApproximationControls vc hvc ec hec) f =
      comparisonScale G f := rfl

/-- **The side-preservation discharge with shrunken controls.**  For every locally finite
realization there are strictly positive replacement controls below which the complete
cellwise compatibility package holds; the shrunken realization keeps the same map, region and
separation radii. -/
theorem exists_controls_cellwiseCompatibility (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) :
    ∃ (vc : K.Vertex → ℝ) (hvc : ∀ v, 0 < vc v)
      (ec : K.Edge → ℝ) (hec : ∀ e, 0 < ec e),
      ∀ (_ : ∀ f : K.Face,
          (K.facePolygonalCircle
            (G := G.withApproximationControls vc hvc ec hec) f).closedRegion ⊆
            (G.withApproximationControls vc hvc ec hec).region)
        (_ : LocallyFinite fun f : K.Face ↦
          {q : (G.withApproximationControls vc hvc ec hec).region | q.1 ∈
            (K.facePolygonalCircle
              (G := G.withApproximationControls vc hvc ec hec) f).closedRegion}),
        Nonempty (K.CellwiseCompatibility
          (G.withApproximationControls vc hvc ec hec)) := by
  refine ⟨comparisonVertexControl G, comparisonVertexControl_pos G,
    comparisonEdgeControl G, comparisonEdgeControl_pos G, ?_⟩
  intro hregion hloc
  set G' := G.withApproximationControls (comparisonVertexControl G)
    (comparisonVertexControl_pos G) (comparisonEdgeControl G)
    (comparisonEdgeControl_pos G) with hG'
  refine ⟨K.cellwiseCompatibility_of_comparisonScale G' hfaces ?_ ?_ hregion hloc⟩
  · intro f i
    have hscale : comparisonScale G' f = comparisonScale G f :=
      comparisonScale_withApproximationControls G _ _ _ _ f
    constructor
    · calc G'.vertexIsolationRadius (K.edgeFirst (K.faceEdge f i)) ≤
          G'.vertexApproximationControl (K.edgeFirst (K.faceEdge f i)) :=
            G'.vertexIsolationRadius_le_control _
        _ = comparisonVertexControl G (K.edgeFirst (K.faceEdge f i)) := rfl
        _ ≤ comparisonScale G f :=
            comparisonVertexControl_le G (K.edgeFirst_faceEdge_mem_face f i)
        _ = comparisonScale G' f := hscale.symm
    · calc G'.vertexIsolationRadius (K.edgeSecond (K.faceEdge f i)) ≤
          G'.vertexApproximationControl (K.edgeSecond (K.faceEdge f i)) :=
            G'.vertexIsolationRadius_le_control _
        _ = comparisonVertexControl G (K.edgeSecond (K.faceEdge f i)) := rfl
        _ ≤ comparisonScale G f :=
            comparisonVertexControl_le G (K.edgeSecond_faceEdge_mem_face f i)
        _ = comparisonScale G' f := hscale.symm
  · intro f i
    have hscale : comparisonScale G' f = comparisonScale G f :=
      comparisonScale_withApproximationControls G _ _ _ _ f
    calc G'.centralTubeRadius (K.faceEdge f i) ≤
        G'.edgeApproximationControl (K.faceEdge f i) :=
          G'.centralTubeRadius_le_control _
      _ = comparisonEdgeControl G (K.faceEdge f i) := rfl
      _ ≤ comparisonScale G f :=
          comparisonEdgeControl_le G (K.faceEdge_mem_edgeMeetingFaces f i)
      _ = comparisonScale G' f := hscale.symm

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
