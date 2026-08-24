/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveTriangulation
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteFaceModel

/-!
# Affine standard-coordinate formulas for adaptive fan faces

The adaptive fan realization is assembled through faithful midpoint subdivisions.  Although its
definition is geometric, on each named fan triangle its value in the original intrinsic
barycentric coordinates is one affine function of the standard planar face coordinates.  The
relative Radó weld uses this formula after composing with the inverse-affine pieces of retained
polygonal filling certificates.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (L : LocallyFiniteTriangleComplex S)

/-- Reindex standard coordinates onto the literal three-vertex type of one locally finite
face. -/
noncomputable def faceCoordExtensionAffineLF (f : L.Face) :
    (Fin 3 → ℝ) →ᵃ[ℝ] ({v // v ∈ L.faceVertices f} → ℝ) :=
  AffineMap.pi fun v =>
    (LinearMap.proj ((L.faceVertexEquiv f).symm v)).toAffineMap

@[simp] theorem faceCoordExtensionAffineLF_apply
    (f : L.Face) (z : Fin 3 → ℝ)
    (v : {v // v ∈ L.faceVertices f}) :
    L.faceCoordExtensionAffineLF f z v =
      z ((L.faceVertexEquiv f).symm v) := by
  simp [faceCoordExtensionAffineLF]

/-- The affine inverse-coordinate formula for the standard plane chart of a locally finite
face. -/
noncomputable def facePlaneInverseAffineLF (f : L.Face) :
    Plane →ᵃ[ℝ] ({v // v ∈ L.faceVertices f} → ℝ) :=
  (L.faceCoordExtensionAffineLF f).comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

theorem facePlaneHomeomorph_symm_val_LF (f : L.Face)
    (p : standardTrianglePlaneComplex.support) :
    ((L.facePlaneHomeomorph f).symm p).1 =
      L.facePlaneInverseAffineLF f p.1 := by
  let z := (standardTrianglePlaneComplex.realizationHomeomorph
    standardTrianglePlaneComplex_pure).symm p
  have hz : z.1 = standardTrianglePlaneComplex.faceCoords
      standardTriangleMeshFace p.1 := by
    apply standardTrianglePlaneComplex.realizationHomeomorph_symm_val_eq_faceCoords
      standardTrianglePlaneComplex_pure standardTriangleMeshFace p
    change p.1 ∈ standardTrianglePlaneComplex.cellCarrier
      (Finset.univ : Finset (Fin 3))
    rw [standardTriangle_cellCarrier_univ]
    exact p.2
  change
    (L.faceReindexFromStandard f
      (standardRealizationToSimplex z)).1 =
        L.facePlaneInverseAffineLF f p.1
  funext v
  simp only [faceReindexFromStandard, standardRealizationToSimplex,
    facePlaneInverseAffineLF, AffineMap.comp_apply,
    L.faceCoordExtensionAffineLF_apply]
  exact congrFun hz ((L.faceVertexEquiv f).symm v)

end LocallyFiniteTriangleComplex

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {U : Set K.realization}
variable [K.AdaptiveSafety U]
variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- Relabeling a global adaptive fan simplex preserves the source-weighted affine sum. -/
theorem adaptiveFanRelabel_source_sum_apply
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f})
    (v : (K.safeSubdivision f.1.1).refined.Vertex) :
    (∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        (K.adaptiveFanRelabelSimplex U hU f x) p *
          (K.adaptiveFanVertexSource U hU f p).1 v) =
      ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        x ((K.adaptiveFanFaceVertexEquiv U hU f).symm p) *
          (K.adaptiveFanVertexSource U hU f p).1 v := by
  classical
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  let q : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} :=
    (K.adaptiveFanFaceVertexEquiv U hU f).symm p
  have hweight :=
    K.adaptiveFanRelabel_extended_apply U hU f x q.1
  change
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f)
        (K.adaptiveFanRelabelSimplex U hU f x) p.1 =
      extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU f) x q.1
    at hweight
  rw [extendFaceCoordinates_of_mem _ _ p.2,
    extendFaceCoordinates_of_mem _ _ q.2] at hweight
  exact hweight

theorem adaptiveGlobalFanFaceMap_standardAffine_point
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (aQ : ((K.safeSubdivision f.1.1).refined.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ))
    (haQ : ∀ z : (K.safeSubdivision f.1.1).refined.realization,
      z ∈ (K.safeSubdivision f.1.1).refined.faceCarrier f.1.2.1.1 →
        ((K.safeSubdivision f.1.1).homeo z).1 = aQ z.1)
    (b : ({v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ) →ₗ[ℝ]
      (K.safeSubdivision f.1.1).refined.Vertex → ℝ)
    (hb : ∀ (z : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ)
      (v : (K.safeSubdivision f.1.1).refined.Vertex),
      b z v = ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        z ((K.adaptiveFanFaceVertexEquiv U hU f).symm p) *
          (K.adaptiveFanVertexSource U hU f p).1 v) :
    ∀ x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
      ((K.safeSubdivision f.1.1).homeo
          (K.adaptiveFanSourcePoint U hU f
            (K.adaptiveFanRelabelSimplex U hU f x))).1 =
        aQ (b ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneInverseAffineLF f
          ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1)) := by
  classical
  let R := K.adaptiveLocallyFiniteTriangleComplex U hU
  let Q := K.safeSubdivision f.1.1
  intro x
  let y := K.adaptiveFanRelabelSimplex U hU f x
  have hyCarrier : K.adaptiveFanSourcePoint U hU f y ∈
      Q.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanSourcePoint_mem_carrier U hU f y
  have hxPlane : x.1 = R.facePlaneInverseAffineLF f
      (R.facePlaneHomeomorph f x).1 := by
    have h := R.facePlaneHomeomorph_symm_val_LF f (R.facePlaneHomeomorph f x)
    rw [(R.facePlaneHomeomorph f).symm_apply_apply] at h
    exact h
  change (Q.homeo (K.adaptiveFanSourcePoint U hU f y)).1 =
    aQ (b (R.facePlaneInverseAffineLF f (R.facePlaneHomeomorph f x).1))
  rw [haQ _ hyCarrier]
  apply congrArg aQ
  rw [← hxPlane]
  funext v
  change (∑ p, y p * (K.adaptiveFanVertexSource U hU f p).1 v) = b x.1 v
  rw [hb]
  exact K.adaptiveFanRelabel_source_sum_apply hU f x v

/-- The affine subdivision map on the refined face supporting a global fan. -/
noncomputable def adaptiveGlobalFanAffinePiece
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    ((K.safeSubdivision f.1.1).refined.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  Classical.choose ((K.safeSubdivision f.1.1).affineOnFace
    f.1.2.1.1 f.1.2.1.2)

/-- The linear map that relabels global fan coordinates into refined coordinates. -/
noncomputable def adaptiveGlobalFanLinearPiece
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    ({v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ) →ₗ[ℝ]
      ((K.safeSubdivision f.1.1).refined.Vertex → ℝ) :=
  ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
    (LinearMap.proj
      ((K.adaptiveFanFaceVertexEquiv U hU f).symm p)).smulRight
        (K.adaptiveFanVertexSource U hU f p).1

/-- The affine map describing one global adaptive fan face in standard coordinates. -/
noncomputable def adaptiveGlobalFanMapStandardAffine
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    Plane →ᵃ[ℝ] (K.Vertex → ℝ) :=
  ((K.adaptiveGlobalFanAffinePiece hU f).comp
      (K.adaptiveGlobalFanLinearPiece hU f).toAffineMap).comp
    ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneInverseAffineLF f)

/-- The standard simplex indexing a global adaptive fan face. -/
abbrev adaptiveGlobalFanSimplex (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :=
  stdSimplex ℝ {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}

/-- The intrinsic-coordinate value of a global adaptive fan face map. -/
noncomputable def adaptiveGlobalFanFaceMapValue
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    K.adaptiveGlobalFanSimplex hU f → (K.Vertex → ℝ) :=
  fun x ↦ (K.adaptiveGlobalFanFaceMap U hU f x).1.1

theorem adaptiveGlobalFanMapStandardAffine_apply
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    K.adaptiveGlobalFanFaceMapValue hU f x =
      K.adaptiveGlobalFanMapStandardAffine hU f
        ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1 := by
  classical
  have haQ := Classical.choose_spec ((K.safeSubdivision f.1.1).affineOnFace
    f.1.2.1.1 f.1.2.1.2)
  have hb : ∀ (z : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ)
      (v : (K.safeSubdivision f.1.1).refined.Vertex),
      K.adaptiveGlobalFanLinearPiece hU f z v =
        ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
          z ((K.adaptiveFanFaceVertexEquiv U hU f).symm p) *
            (K.adaptiveFanVertexSource U hU f p).1 v := by
    intro z v
    simp only [adaptiveGlobalFanLinearPiece, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  have hpoint := K.adaptiveGlobalFanFaceMap_standardAffine_point hU f
    (K.adaptiveGlobalFanAffinePiece hU f) haQ
      (K.adaptiveGlobalFanLinearPiece hU f) hb x
  change ((K.safeSubdivision f.1.1).homeo
      (K.adaptiveFanSourcePoint U hU f
        (K.adaptiveFanRelabelSimplex U hU f x))).1 = _
  change _ =
    (((K.adaptiveGlobalFanAffinePiece hU f).comp
      (K.adaptiveGlobalFanLinearPiece hU f).toAffineMap).comp
        ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneInverseAffineLF f))
      ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1
  exact hpoint

/- One adaptive global fan face is affine, in original intrinsic barycentric coordinates, as a
function of its standard planar face coordinates. -/
theorem adaptiveGlobalFanFaceMap_standardAffine
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    ∃ a : Plane →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : K.adaptiveGlobalFanSimplex hU f,
        K.adaptiveGlobalFanFaceMapValue hU f x =
          a ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1 := by
  refine ⟨K.adaptiveGlobalFanMapStandardAffine hU f, ?_⟩
  intro x
  exact K.adaptiveGlobalFanMapStandardAffine_apply hU f x

/-- On one local fan triangle, the transported old barycentric coordinates are the
barycentric weighted sum of the coordinates of its three geometric vertices.  This is the
supporting-face formula used by the bordered chart straightening. -/
theorem adaptiveFanFaceMap_val_eq_vertex_sum
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    (K.adaptiveFanFaceMap U hU f x).1.1 =
      fun v ↦ ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        x p * p.1.1 v := by
  classical
  let Q := K.safeSubdivision f.1.1
  obtain ⟨a, ha⟩ := Q.affineOnFace f.1.2.1.1 f.1.2.1.2
  let point :
      {p // p ∈ K.adaptiveFanFaceVertices U hU f} →
        (Q.refined.Vertex → ℝ) :=
    fun p ↦ (K.adaptiveFanVertexSource U hU f p).1
  let weight : {p // p ∈ K.adaptiveFanFaceVertices U hU f} → ℝ :=
    fun p ↦ x p
  have hweight : ∑ p, weight p = 1 := x.2.2
  let zfun : Q.refined.Vertex → ℝ :=
    (Finset.univ : Finset
      {p // p ∈ K.adaptiveFanFaceVertices U hU f}
    ).affineCombination ℝ point weight
  have hzfun :
      zfun = (K.adaptiveFanSourcePoint U hU f x).1 := by
    rw [show zfun =
        ∑ p, weight p • point p by
      exact Finset.affineCombination_eq_linear_combination
        Finset.univ point weight hweight]
    funext v
    simp only [weight, point, adaptiveFanSourcePoint,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsourceCarrier :
      K.adaptiveFanSourcePoint U hU f x ∈
        Q.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanSourcePoint_mem_carrier U hU f x
  have hvertex (p : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
      a (point p) = p.1.1 := by
    have hpCarrier :=
      K.adaptiveFanVertexSource_mem_carrier U hU f p
    have hpAffine := ha (K.adaptiveFanVertexSource U hU f p) hpCarrier
    rw [← hpAffine]
    exact congrArg Subtype.val
      (Q.homeo.apply_symm_apply p.1)
  change
    (Q.homeo (K.adaptiveFanSourcePoint U hU f x)).1 =
      fun v ↦ ∑ p, x p * p.1.1 v
  rw [ha _ hsourceCarrier]
  change a (K.adaptiveFanSourcePoint U hU f x).1 = _
  rw [← hzfun,
    (Finset.univ : Finset
      {p // p ∈ K.adaptiveFanFaceVertices U hU f}
    ).map_affineCombination point weight hweight a,
    Finset.affineCombination_eq_linear_combination
      Finset.univ (a ∘ point) weight hweight]
  funext v
  simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, weight]
  apply Finset.sum_congr rfl
  intro p _
  rw [hvertex p]

/-- The same vertex-sum formula after relabeling a fan triangle by the global vertex type of
the locally finite adaptive complex. -/
theorem adaptiveGlobalFanFaceMap_val_eq_vertex_sum
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    (K.adaptiveGlobalFanFaceMap U hU f x).1.1 =
      fun k ↦ ∑ v :
          {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
        x v * v.1.1.1 k := by
  classical
  let E := K.adaptiveFanFaceVertexEquiv U hU f
  let y := K.adaptiveFanRelabelSimplex U hU f x
  rw [show K.adaptiveGlobalFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU f y by rfl,
    K.adaptiveFanFaceMap_val_eq_vertex_sum hU f y]
  funext k
  rw [← E.sum_comp
    (fun p : {p // p ∈ K.adaptiveFanFaceVertices U hU f} ↦
      y p * p.1.1 k)]
  apply Finset.sum_congr rfl
  intro v _
  have hweight :
      y (E v) = x v := by
    let gv : K.AdaptiveFanVertex U hU := v.1
    have h :=
      K.adaptiveFanRelabel_extended_apply U hU f x gv
    have hp : gv.1 ∈ K.adaptiveFanFaceVertices U hU f :=
      (E v).2
    rw [extendFaceCoordinates_of_mem
        (K.adaptiveFanFaceVertices U hU f)
          (K.adaptiveFanRelabelSimplex U hU f x) hp,
      extendFaceCoordinates_of_mem
        (K.adaptiveGlobalFanFaceVertices U hU f) x v.2] at h
    have hEv :
        E v = (⟨gv.1, hp⟩ :
          {p // p ∈ K.adaptiveFanFaceVertices U hU f}) := by
      apply Subtype.ext
      rfl
    rw [hEv]
    simpa only [y] using h
  rw [hweight]
  rfl

/-- The vertices of an adaptive fan face whose geometric source points lie in an old
barycentric carrier. -/
noncomputable def adaptiveGlobalFanFaceVerticesInCarrier
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (b : Finset K.Vertex) : Finset (K.AdaptiveFanVertex U hU) := by
  classical
  exact
    (K.adaptiveGlobalFanFaceVertices U hU f).filter
      (fun w : K.AdaptiveFanVertex U hU ↦
        w.1 ∈ K.faceCarrier b)

/-- Pulling an old barycentric face carrier back to one adaptive fan triangle gives the
simplex face spanned by precisely those adaptive vertices which lie in the old carrier. -/
theorem adaptiveGlobalFanFaceMap_mem_faceCarrier_iff_supported
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (b : Finset K.Vertex)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f}) :
    (K.adaptiveGlobalFanFaceMap U hU f x).1 ∈ K.faceCarrier b ↔
      ∀ v :
          {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
        v.1 ∉ K.adaptiveGlobalFanFaceVerticesInCarrier hU f b →
          x v = 0 := by
  classical
  rw [K.mem_faceCarrier_iff]
  rw [K.adaptiveGlobalFanFaceMap_val_eq_vertex_sum hU f x]
  constructor
  · intro hsupport v hv
    have hvNot : v.1.1 ∉ K.faceCarrier b := by
      simpa only [adaptiveGlobalFanFaceVerticesInCarrier,
        Finset.mem_filter, v.2, true_and] using hv
    rw [K.mem_faceCarrier_iff] at hvNot
    push Not at hvNot
    obtain ⟨k, hkb, hvk⟩ := hvNot
    have hvkPos : 0 < v.1.1.1 k :=
      lt_of_le_of_ne (v.1.1.2.1.1 k)
        (Ne.symm hvk)
    by_contra hxv
    have hxvPos : 0 < x v :=
      lt_of_le_of_ne (x.2.1 v) (Ne.symm hxv)
    have hsumPos :
        0 < ∑ w :
            {w // w ∈ K.adaptiveGlobalFanFaceVertices U hU f},
          x w * w.1.1.1 k := by
      apply Finset.sum_pos'
      · intro w _
        exact mul_nonneg (x.2.1 w) (w.1.1.2.1.1 k)
      · exact ⟨v, Finset.mem_univ v, mul_pos hxvPos hvkPos⟩
    have hzero := hsupport k hkb
    exact (ne_of_gt hsumPos) hzero
  · intro hx k hkb
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv :
        v.1 ∈ K.adaptiveGlobalFanFaceVerticesInCarrier hU f b
    · have hvCarrier : v.1.1 ∈ K.faceCarrier b :=
        (by
          simpa only [adaptiveGlobalFanFaceVerticesInCarrier,
            Finset.mem_filter, v.2, true_and] using hv)
      have hvzero :=
        (K.mem_faceCarrier_iff b v.1.1).mp hvCarrier k hkb
      rw [hvzero, mul_zero]
    · rw [hx v hv, zero_mul]

/-- Iterating the strict-interior preservation of midpoint subdivision reaches a level-zero
parent without requiring dependent arithmetic casts in downstream arguments. -/
private theorem exists_levelZeroAncestor_relInterior
    (n : ℕ) (s : K.LevelFace n) :
    ∃ a₀ : K.LevelFace 0,
      K.levelFaceRelInterior s ⊆ K.levelFaceRelInterior a₀ := by
  induction n with
  | zero =>
      exact ⟨s, Set.Subset.rfl⟩
  | succ n ih =>
      let p : K.LevelFace n := K.levelParentFace n s
      obtain ⟨a₀, ha₀⟩ := ih p
      exact ⟨a₀,
        (K.levelFaceRelInterior_subset_parent n s).trans ha₀⟩

/-- The cone center of an adaptive fan face lies in the relative interior of its unique
level-zero parent.  Hence it misses every proper old face of cardinality at most two in any
old triangle to which the refined face is subordinate. -/
theorem adaptiveFaceCenter_not_mem_faceCarrier_of_subordinate
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (t : K.Face)
    (hsub : ∀ x : (K.safeSubdivision f.1.1).refined.realization,
      x ∈ (K.safeSubdivision f.1.1).refined.faceCarrier f.1.2.1.1 →
        (K.safeSubdivision f.1.1).homeo x ∈ K.faceCarrier t.1)
    (b : Finset K.Vertex) (hbt : b ⊆ t.1) (hbcard : b.card ≤ 2) :
    K.adaptiveFaceCenter U f.1 ∉ K.faceCarrier b := by
  classical
  let s : K.LevelFace f.1.1 := f.1.2.1
  obtain ⟨a₀, ha₀⟩ :=
    exists_levelZeroAncestor_relInterior (K := K) f.1.1 s
  let t₀ : K.LevelFace 0 := by
    change K.Face
    exact t
  have hcenterAnc :
      K.adaptiveFaceCenter U f.1 ∈ K.levelFaceRelInterior a₀ := by
    apply ha₀
    exact K.adaptiveFaceCenter_mem_relInterior U f.1
  have hcenterParent :
      K.adaptiveFaceCenter U f.1 ∈ K.levelFaceCarrier t₀ := by
    have hc := K.adaptiveFaceCenter_mem_carrier U f.1
    obtain ⟨z, hz, hzeq⟩ := hc
    have hzParent := hsub z hz
    rw [hzeq] at hzParent
    change K.adaptiveFaceCenter U f.1 ∈
      (Subdivision.refl K).homeo '' K.faceCarrier t.1
    exact ⟨K.adaptiveFaceCenter U f.1, hzParent, rfl⟩
  have hat : a₀ = t₀ := by
    by_contra hne
    exact Set.disjoint_left.mp
      (K.disjoint_levelFaceRelInterior_levelFaceCarrier hne)
        hcenterAnc hcenterParent
  have hcenterRel :
      K.adaptiveFaceCenter U f.1 ∈ K.levelFaceRelInterior t₀ := by
    rw [← hat]
    exact hcenterAnc
  have hcenterPos :
      ∀ v ∈ t.1, 0 < (K.adaptiveFaceCenter U f.1).1 v := by
    change K.adaptiveFaceCenter U f.1 ∈
      (K.safeSubdivision 0).homeo ''
        {x : (K.safeSubdivision 0).refined.realization |
          x ∈ (K.safeSubdivision 0).refined.faceCarrier t₀.1 ∧
            ∀ v ∈ t₀.1, 0 < x.1 v} at hcenterRel
    obtain ⟨z, ⟨-, hzpos⟩, hzeq⟩ := hcenterRel
    have hval :
        z.1 = (K.adaptiveFaceCenter U f.1).1 := by
      have := congrArg Subtype.val hzeq
      exact this
    intro v hvt
    rw [← congrFun hval v]
    exact hzpos v hvt
  have hproper : b ⊂ t.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hbt, ?_⟩
    intro h
    have := congrArg Finset.card h
    rw [K.faces_card t.1 t.2] at this
    omega
  obtain ⟨v, hvt, hvb⟩ := Finset.exists_of_ssubset hproper
  intro hcenterB
  have hzero :=
    (K.mem_faceCarrier_iff b (K.adaptiveFaceCenter U f.1)).mp
      hcenterB v hvb
  have hpos := hcenterPos v hvt
  rw [hzero] at hpos
  exact (lt_irrefl 0 hpos)

/-- If one declared fan vertex misses an old carrier, that pullback carrier has at most two
vertices and hence is an exposed proper face of the adaptive triangle. -/
theorem adaptiveGlobalFanFaceMap_exists_exposedFace
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (b : Finset K.Vertex)
    (v₀ : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f})
    (hv₀ : v₀.1.1 ∉ K.faceCarrier b) :
    ∃ d : Finset (K.AdaptiveFanVertex U hU),
      d ⊆ K.adaptiveGlobalFanFaceVertices U hU f ∧
        d.card ≤ 2 ∧
        ∀ x : stdSimplex ℝ
            {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
          ((K.adaptiveGlobalFanFaceMap U hU f x).1 ∈ K.faceCarrier b ↔
            ∀ v :
                {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
              v.1 ∉ d → x v = 0) := by
  classical
  let d := K.adaptiveGlobalFanFaceVerticesInCarrier hU f b
  refine ⟨d, Finset.filter_subset _ _, ?_, ?_⟩
  · have hv₀d : v₀.1 ∉ d := by
      simp only [d, adaptiveGlobalFanFaceVerticesInCarrier,
        Finset.mem_filter, v₀.2, true_and]
      exact hv₀
    have hproper :
        d ⊂ K.adaptiveGlobalFanFaceVertices U hU f := by
      refine Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      apply hv₀d
      rw [heq]
      exact v₀.2
    have hcard :=
      Finset.card_lt_card hproper
    have hthree :
        (K.adaptiveGlobalFanFaceVertices U hU f).card = 3 :=
      (K.adaptiveLocallyFiniteTriangleComplex U hU).faceVertices_card f
    omega
  · intro x
    exact
      K.adaptiveGlobalFanFaceMap_mem_faceCarrier_iff_supported hU f b x

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
