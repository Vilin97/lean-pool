/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.Anchors

/-!
# Standard plane models for intrinsic faces

Every maximal face of an intrinsic complex is a closed barycentric triangle.  This file gives
the explicit coordinate reindexing homeomorphism to the standard plane triangle.  It is the
source-side bridge used to apply the already proved polygonal Schoenflies extension cellwise.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open scoped BigOperators _root_.Topology

theorem standardTrianglePlaneComplex_pure : standardTrianglePlaneComplex.IsPure2 := by
  intro s hs
  refine ⟨Finset.univ, ?_, Finset.subset_univ s, ?_⟩
  · change (Finset.univ : Finset (Fin 3)) ∈
      (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty)
    simp
  · change (Finset.univ : Finset (Fin 3)).card = 3
    decide

theorem standardTriangle_univ_mem_cells :
    (Finset.univ : Finset (Fin 3)) ∈ standardTrianglePlaneComplex.cells := by
  change (Finset.univ : Finset (Fin 3)) ∈
    (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty).filter
      fun t => t.card = 3
  decide

/-- The unique maximal face of the standard triangle mesh. -/
noncomputable def standardTriangleMeshFace :
    standardTrianglePlaneComplex.toTriangleMesh.Triangle :=
  ⟨Finset.univ, standardTriangle_univ_mem_cells⟩

theorem standardTrianglePlaneComplex_support :
    standardTrianglePlaneComplex.support =
      convexHull ℝ (Set.range standardTriangleVertex) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    rw [PlaneComplex.cellCarrier] at hxs
    apply convexHull_mono _ hxs
    rintro y ⟨i, hi, rfl⟩
    exact ⟨i, rfl⟩
  · intro x hx
    apply standardTrianglePlaneComplex.cellCarrier_subset_support
      (standardTrianglePlaneComplex.mem_simplexes_of_mem_cells
        standardTriangle_univ_mem_cells)
    rw [PlaneComplex.cellCarrier]
    change x ∈ convexHull ℝ
      (standardTriangleVertex '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)))
    simpa only [Finset.coe_univ, Set.image_univ] using hx

theorem standardTriangle_cellCarrier_univ :
    standardTrianglePlaneComplex.cellCarrier (Finset.univ : Finset (Fin 3)) =
      standardTrianglePlaneComplex.support := by
  rw [PlaneComplex.cellCarrier, standardTrianglePlaneComplex_position]
  change convexHull ℝ
    (standardTriangleVertex '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))) = _
  rw [Finset.coe_univ, Set.image_univ, ← standardTrianglePlaneComplex_support]

theorem standardTrianglePlaneComplex_isTriangle :
    IsTriangle standardTrianglePlaneComplex.support := by
  exact ⟨standardTriangleVertex, standardTriangleVertex_affineIndependent,
    standardTrianglePlaneComplex_support⟩

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

@[simp] theorem finEquiv_symm_three (i : ZMod 3) :
    (ZMod.finEquiv 3).symm i = i := rfl

/-- The chosen ordering of one intrinsic face, viewed as an embedding into all vertices. -/
noncomputable def faceVertexEmbedding (t : K.Face) : Fin 3 ↪ K.Vertex where
  toFun i := (K.faceVertexEquiv t i).1
  inj' := fun _ _ hij => (K.faceVertexEquiv t).injective (Subtype.ext hij)

/-- The two standard indices belonging to cyclic side `i`. -/
noncomputable def faceStandardEdge (i : ZMod 3) : Finset (Fin 3) :=
  {(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)}

theorem faceVertexEmbedding_cyclic (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t ((ZMod.finEquiv 3).symm i) = K.faceVertex t i := rfl

theorem faceStandardEdge_map (t : K.Face) (i : ZMod 3) :
    (faceStandardEdge i).map (K.faceVertexEmbedding t) = (K.faceEdge t i).1 := by
  simp only [faceStandardEdge, Finset.map_insert, Finset.map_singleton,
    faceVertexEmbedding, K.faceEdge_val]
  rfl

theorem faceStandardEdge_mem_simplexes (i : ZMod 3) :
    faceStandardEdge i ∈ standardTrianglePlaneComplex.simplexes := by
  change faceStandardEdge i ∈
    (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
  exact ⟨i, Finset.mem_insert_self i {i + 1}⟩

/-- The geometric carrier of a standard cyclic edge is its polygon side. -/
theorem standard_cellCarrier_faceStandardEdge (i : ZMod 3) :
    standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) =
      standardTriangleCircle.edgeSegment i := by
  change standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) =
    segment ℝ (standardTriangleVertex ((ZMod.finEquiv 3).symm i))
      (standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1)))
  rw [PlaneComplex.cellCarrier, ← convexHull_pair]
  congr 1
  ext p
  constructor
  · rintro ⟨j, hj, rfl⟩
    change j ∈ ({(ZMod.finEquiv 3).symm i,
      (ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)) at hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl rfl
    · have hj' := Finset.mem_singleton.mp hj
      subst j
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨(ZMod.finEquiv 3).symm i, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨(ZMod.finEquiv 3).symm (i + 1),
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), rfl⟩

/-- The one-skeleton of the standard triangle complex is exactly its polygonal frontier. -/
theorem standardTriangle_oneSkeleton_support :
    standardTrianglePlaneComplex.oneSkeleton.support =
      standardTriangleCircle.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hsData := standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mp hs
    have hsSide : ∃ i : ZMod 3, s ⊆ faceStandardEdge i := by
      by_cases h0 : (0 : Fin 3) ∈ s
      · by_cases h1 : (1 : Fin 3) ∈ s
        · have h2 : (2 : Fin 3) ∉ s := by
            intro h2
            have hsub : ({0, 1, 2} : Finset (Fin 3)) ⊆ s := by
              simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
              exact ⟨h0, h1, h2⟩
            have hcard := Finset.card_le_card hsub
            have hthree : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
            rw [hthree] at hcard
            exact (by omega : ¬ (3 : ℕ) ≤ 2) (hcard.trans hsData.2)
          refine ⟨0, ?_⟩
          change s ⊆ ({0, 1} : Finset (Fin 3))
          intro j hj
          fin_cases j
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact (h2 hj).elim
        · refine ⟨2, ?_⟩
          change s ⊆ ({2, 0} : Finset (Fin 3))
          intro j hj
          fin_cases j
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact (h1 hj).elim
          · exact Finset.mem_insert_self _ _
      · refine ⟨1, ?_⟩
        change s ⊆ ({1, 2} : Finset (Fin 3))
        intro j hj
        fin_cases j
        · exact (h0 hj).elim
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨i, hsi⟩ := hsSide
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← standard_cellCarrier_faceStandardEdge i]
    exact convexHull_mono (Set.image_mono hsi) hxs
  · intro x hx
    change x ∈ ⋃ i : ZMod 3, standardTriangleCircle.edgeSegment i at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [← standard_cellCarrier_faceStandardEdge i] at hxi
    rw [PlaneComplex.support]
    apply Set.mem_iUnion₂.mpr
    refine ⟨faceStandardEdge i, ?_, hxi⟩
    apply standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
    refine ⟨faceStandardEdge_mem_simplexes i, ?_⟩
    rw [faceStandardEdge]
    calc
      ({(ZMod.finEquiv 3).symm i,
          (ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)).card ≤
          ({(ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by rw [Finset.card_singleton]

/-- One closed maximal face, as a subtype of the intrinsic realization. -/
abbrev ClosedFace (t : K.Face) := {x : K.realization // x ∈ K.faceCarrier t.1}

/-- Reindex the barycentric coordinates of an intrinsic face by its chosen `Fin 3` ordering. -/
noncomputable def faceReindexToStandard (t : K.Face) (x : K.ClosedFace t) :
    standardTrianglePlaneComplex.toIntrinsic.realization := by
  let z : Fin 3 → ℝ := fun i => x.1.1 (K.faceVertexEquiv t i).1
  refine ⟨z, ⟨?_, ?_⟩, ⟨Finset.univ, standardTriangle_univ_mem_cells, ?_⟩⟩
  · intro i
    exact x.1.2.1.1 _
  · calc
      ∑ i, z i = ∑ v : t.1, x.1.1 v.1 :=
        (K.faceVertexEquiv t).sum_comp (fun v : t.1 => x.1.1 v.1)
      _ = ∑ v ∈ t.1, x.1.1 v := by rw [Finset.sum_coe_sort]
      _ = ∑ v, x.1.1 v :=
        Finset.sum_subset (Finset.subset_univ t.1) fun v _ hv => x.2 v hv
      _ = 1 := x.1.2.1.2
  · intro i hi
    exact (hi (Finset.mem_univ i)).elim

/-- Extend standard barycentric coordinates by zero away from the chosen intrinsic face. -/
noncomputable def faceReindexFromStandard (t : K.Face)
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) : K.ClosedFace t := by
  let x : K.Vertex → ℝ := fun v =>
    if hv : v ∈ t.1 then z.1 ((K.faceVertexEquiv t).symm ⟨v, hv⟩) else 0
  refine ⟨⟨x, ⟨?_, ?_⟩, ⟨t.1, t.2, ?_⟩⟩, ?_⟩
  · intro v
    dsimp [x]
    split_ifs with hv
    · exact z.2.1.1 _
    · exact le_rfl
  · calc
      ∑ v, x v = ∑ v ∈ t.1, x v :=
        (Finset.sum_subset (Finset.subset_univ t.1) fun v _ hv => by
          simp [x, hv]).symm
      _ = ∑ v : t.1, z.1 ((K.faceVertexEquiv t).symm v) := by
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro v hv
        simp [x, v.2]
      _ = ∑ i : Fin 3, z.1 i :=
        (K.faceVertexEquiv t).symm.sum_comp (fun i : Fin 3 => z.1 i)
      _ = 1 := z.2.1.2
  · intro v hv
    simp [x, hv]
  · intro v hv
    simp [x, hv]

@[simp] theorem faceReindexFromStandard_toStandard (t : K.Face) (x : K.ClosedFace t) :
    K.faceReindexFromStandard t (K.faceReindexToStandard t x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ t.1
  · simp [faceReindexFromStandard, faceReindexToStandard, hv]
  · simp [faceReindexFromStandard, hv, x.2 v hv]

@[simp] theorem faceReindexToStandard_fromStandard (t : K.Face)
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) :
    K.faceReindexToStandard t (K.faceReindexFromStandard t z) = z := by
  apply Subtype.ext
  funext i
  simp [faceReindexToStandard, faceReindexFromStandard]

theorem continuous_faceReindexToStandard (t : K.Face) :
    Continuous (K.faceReindexToStandard t) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_apply (K.faceVertexEquiv t i).1).comp continuous_subtype_val).comp
    continuous_subtype_val

/-- The canonical barycentric homeomorphism from one intrinsic face to the standard intrinsic
triangle. -/
noncomputable def faceReindexHomeomorph (t : K.Face) :
    K.ClosedFace t ≃ₜ standardTrianglePlaneComplex.toIntrinsic.realization := by
  let e : K.ClosedFace t ≃ standardTrianglePlaneComplex.toIntrinsic.realization := {
    toFun := K.faceReindexToStandard t
    invFun := K.faceReindexFromStandard t
    left_inv := K.faceReindexFromStandard_toStandard t
    right_inv := K.faceReindexToStandard_fromStandard t }
  letI : CompactSpace (K.ClosedFace t) :=
    isCompact_iff_compactSpace.mp (K.faceCarrier_closed t.1).isCompact
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (K.continuous_faceReindexToStandard t)

/-- Reindexing carries any selected standard subface exactly to the corresponding intrinsic
vertex set. -/
theorem faceReindexToStandard_mem_faceCarrier (t : K.Face) (s : Finset (Fin 3))
    (x : K.ClosedFace t) :
    K.faceReindexToStandard t x ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s ↔
      x.1 ∈ K.faceCarrier (s.map (K.faceVertexEmbedding t)) := by
  constructor
  · intro hz v hv
    by_cases hvt : v ∈ t.1
    · let j : Fin 3 := (K.faceVertexEquiv t).symm ⟨v, hvt⟩
      have hj : j ∉ s := by
        intro hjs
        apply hv
        apply Finset.mem_map.mpr
        refine ⟨j, hjs, ?_⟩
        exact congrArg Subtype.val ((K.faceVertexEquiv t).apply_symm_apply ⟨v, hvt⟩)
      have := hz j hj
      change x.1.1 (K.faceVertexEmbedding t j) = 0 at this
      rw [show K.faceVertexEmbedding t j = v from
        congrArg Subtype.val ((K.faceVertexEquiv t).apply_symm_apply ⟨v, hvt⟩)] at this
      exact this
    · exact x.2 v hvt
  · intro hx j hj
    change x.1.1 (K.faceVertexEmbedding t j) = 0
    apply hx
    intro hmem
    obtain ⟨k, hks, hkj⟩ := Finset.mem_map.mp hmem
    have hkj' : k = j := (K.faceVertexEmbedding t).injective hkj
    exact hj (hkj' ▸ hks)

/-- The standard plane realization of one intrinsic closed face. -/
noncomputable def facePlaneHomeomorph (t : K.Face) :
    K.ClosedFace t ≃ₜ standardTrianglePlaneComplex.support :=
  (K.faceReindexHomeomorph t).trans
    (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure)

/-- Restrict ambient intrinsic barycentric coordinates to the ordered vertices of one face. -/
noncomputable def faceCoordRestrictionAffine (t : K.Face) :
    (K.Vertex → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
  AffineMap.pi fun j =>
    (LinearMap.proj (K.faceVertexEmbedding t j)).toAffineMap

@[simp] theorem faceCoordRestrictionAffine_apply (t : K.Face)
    (x : K.Vertex → ℝ) (j : Fin 3) :
    K.faceCoordRestrictionAffine t x j =
      x (K.faceVertexEmbedding t j) := by
  rfl

/-- The forward standard-plane chart is affine in the ambient intrinsic barycentric
coordinates. -/
noncomputable def facePlaneForwardAffine (t : K.Face) :
    (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
  standardTrianglePlaneComplex.baryEvalAffine.comp
    (K.faceCoordRestrictionAffine t)

theorem facePlaneHomeomorph_val_eq_forwardAffine (t : K.Face)
    (x : K.ClosedFace t) :
    (K.facePlaneHomeomorph t x).1 =
      K.facePlaneForwardAffine t x.1.1 := by
  change standardTrianglePlaneComplex.baryEval
      (K.faceReindexToStandard t x).1 =
    standardTrianglePlaneComplex.baryEval
      (K.faceCoordRestrictionAffine t x.1.1)
  apply congrArg standardTrianglePlaneComplex.baryEval
  funext j
  rfl

/-- Affinely extend standard face coordinates by zero away from the selected intrinsic face. -/
noncomputable def faceCoordExtensionAffine (t : K.Face) :
    (Fin 3 → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  AffineMap.pi fun v =>
    if hv : v ∈ t.1 then
      (LinearMap.proj ((K.faceVertexEquiv t).symm ⟨v, hv⟩)).toAffineMap
    else
      AffineMap.const ℝ (Fin 3 → ℝ) 0

@[simp] theorem faceCoordExtensionAffine_apply_of_mem (t : K.Face)
    (z : Fin 3 → ℝ) {v : K.Vertex} (hv : v ∈ t.1) :
    K.faceCoordExtensionAffine t z v =
      z ((K.faceVertexEquiv t).symm ⟨v, hv⟩) := by
  simp [faceCoordExtensionAffine, hv]

@[simp] theorem faceCoordExtensionAffine_apply_of_notMem (t : K.Face)
    (z : Fin 3 → ℝ) {v : K.Vertex} (hv : v ∉ t.1) :
    K.faceCoordExtensionAffine t z v = 0 := by
  simp [faceCoordExtensionAffine, hv]

/-- The barycentric-coordinate formula for the inverse standard plane chart of one intrinsic
face. -/
noncomputable def facePlaneInverseAffine (t : K.Face) :
    Plane →ᵃ[ℝ] (K.Vertex → ℝ) :=
  (K.faceCoordExtensionAffine t).comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

/-- The inverse-chart affine formula takes each standard corner to the corresponding intrinsic
unit barycentric coordinate. -/
theorem facePlaneInverseAffine_standardVertex (t : K.Face) (j : Fin 3) :
    K.facePlaneInverseAffine t (standardTriangleVertex j) =
      Pi.single (K.faceVertexEmbedding t j) 1 := by
  have hc := standardTrianglePlaneComplex.faceCoords_position
    standardTriangleMeshFace (v := j) (by
      change j ∈ (Finset.univ : Finset (Fin 3))
      simp)
  rw [standardTrianglePlaneComplex_position] at hc
  funext v
  by_cases hv : v ∈ t.1
  · rw [facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_mem _ _ hv, hc]
    by_cases hvj : v = K.faceVertexEmbedding t j
    · have hkj : (K.faceVertexEquiv t).symm ⟨v, hv⟩ = j := by
        apply (K.faceVertexEquiv t).injective
        rw [(K.faceVertexEquiv t).apply_symm_apply]
        apply Subtype.ext
        exact hvj
      rw [hkj, hvj]
      simp
    · have hkj : (K.faceVertexEquiv t).symm ⟨v, hv⟩ ≠ j := by
        intro h
        apply hvj
        change v = (K.faceVertexEquiv t j).1
        exact congrArg Subtype.val ((K.faceVertexEquiv t).symm_apply_eq.mp h)
      simp [hkj, hvj]
  · rw [facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_notMem _ _ hv]
    have hvj : v ≠ K.faceVertexEmbedding t j := by
      intro hvj
      apply hv
      rw [hvj]
      exact (K.faceVertexEquiv t j).2
    simp [hvj]

/-- The first endpoint of a cyclic face edge belongs to the containing face. -/
theorem edgeFirst_faceEdge_mem_face (t : K.Face) (i : ZMod 3) :
    K.edgeFirst (K.faceEdge t i) ∈ t.1 := by
  have h := K.edgeFirst_mem (K.faceEdge t i)
  rw [K.faceEdge_val] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · simpa only [h] using K.faceVertex_mem t i
  · simpa only [h] using K.faceVertex_mem t (i + 1)

/-- The second endpoint of a cyclic face edge belongs to the containing face. -/
theorem edgeSecond_faceEdge_mem_face (t : K.Face) (i : ZMod 3) :
    K.edgeSecond (K.faceEdge t i) ∈ t.1 := by
  have h := K.edgeSecond_mem (K.faceEdge t i)
  rw [K.faceEdge_val] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · simpa only [h] using K.faceVertex_mem t i
  · simpa only [h] using K.faceVertex_mem t (i + 1)

/-- The standard corner corresponding to the globally chosen first endpoint of a face edge. -/
noncomputable def faceEdgeFirstIndex (t : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv t).symm
    ⟨K.edgeFirst (K.faceEdge t i), K.edgeFirst_faceEdge_mem_face t i⟩

/-- The standard corner corresponding to the globally chosen second endpoint of a face edge. -/
noncomputable def faceEdgeSecondIndex (t : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv t).symm
    ⟨K.edgeSecond (K.faceEdge t i), K.edgeSecond_faceEdge_mem_face t i⟩

@[simp] theorem faceVertexEmbedding_faceEdgeFirstIndex (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t (K.faceEdgeFirstIndex t i) =
      K.edgeFirst (K.faceEdge t i) := by
  change ((K.faceVertexEquiv t) ((K.faceVertexEquiv t).symm _)).1 = _
  rw [(K.faceVertexEquiv t).apply_symm_apply]

@[simp] theorem faceVertexEmbedding_faceEdgeSecondIndex (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t (K.faceEdgeSecondIndex t i) =
      K.edgeSecond (K.faceEdge t i) := by
  change ((K.faceVertexEquiv t) ((K.faceVertexEquiv t).symm _)).1 = _
  rw [(K.faceVertexEquiv t).apply_symm_apply]

/-- The two standard endpoint indices are exactly the cyclic standard side, with the order
chosen globally by the intrinsic edge. -/
theorem faceStandardEdge_eq_endpointIndices (t : K.Face) (i : ZMod 3) :
    faceStandardEdge i =
      {K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} := by
  apply Finset.map_injective (K.faceVertexEmbedding t)
  rw [K.faceStandardEdge_map t i, Finset.map_insert, Finset.map_singleton,
    K.faceVertexEmbedding_faceEdgeFirstIndex,
    K.faceVertexEmbedding_faceEdgeSecondIndex, K.edge_eq_pair]

/-- The standard source point on a face side, oriented by the global intrinsic edge ordering. -/
noncomputable def faceEdgeSourcePoint (t : K.Face) (i : ZMod 3) (r : ℝ) : Plane :=
  AffineMap.lineMap
    (standardTriangleVertex (K.faceEdgeFirstIndex t i))
    (standardTriangleVertex (K.faceEdgeSecondIndex t i)) r

/-- The inverse face chart carries the oriented standard side parameter to the corresponding
intrinsic barycentric line parameter. -/
theorem facePlaneInverseAffine_faceEdgeSourcePoint (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.facePlaneInverseAffine t (K.faceEdgeSourcePoint t i r) =
      (AffineMap.lineMap (k := ℝ)
        (Pi.single (K.edgeFirst (K.faceEdge t i)) (1 : ℝ) : K.Vertex → ℝ)
        (Pi.single (K.edgeSecond (K.faceEdge t i)) (1 : ℝ) : K.Vertex → ℝ)) r := by
  rw [faceEdgeSourcePoint, AffineMap.apply_lineMap,
    K.facePlaneInverseAffine_standardVertex,
    K.facePlaneInverseAffine_standardVertex,
    K.faceVertexEmbedding_faceEdgeFirstIndex,
    K.faceVertexEmbedding_faceEdgeSecondIndex]

/-- On the oriented standard side, the second intrinsic barycentric coordinate is its affine
parameter. -/
theorem facePlaneInverseAffine_faceEdgeSourcePoint_apply_second
    (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.facePlaneInverseAffine t (K.faceEdgeSourcePoint t i r)
        (K.edgeSecond (K.faceEdge t i)) = r := by
  rw [K.facePlaneInverseAffine_faceEdgeSourcePoint]
  simp [AffineMap.lineMap_apply_module,
    K.edgeFirst_ne_edgeSecond (K.faceEdge t i)]

/-- Every unit-interval source point lies on the corresponding standard side. -/
theorem faceEdgeSourcePoint_mem_standardEdge (t : K.Face) (i : ZMod 3)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint t i r ∈
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices t i, PlaneComplex.cellCarrier]
  change AffineMap.lineMap
      (standardTriangleVertex (K.faceEdgeFirstIndex t i))
      (standardTriangleVertex (K.faceEdgeSecondIndex t i)) r ∈
    convexHull ℝ
      (standardTriangleVertex ''
        (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
          Set (Fin 3)))
  rw [show standardTriangleVertex ''
      (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex t i),
        standardTriangleVertex (K.faceEdgeSecondIndex t i)} by
    ext p
    simp [eq_comm]]
  rw [convexHull_pair, segment_eq_image_lineMap]
  exact ⟨r, hr, rfl⟩

/-- The oriented unit interval covers exactly the corresponding standard side. -/
theorem faceEdgeSourcePoint_image_Icc (t : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint t i '' Set.Icc (0 : ℝ) 1 =
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices t i, PlaneComplex.cellCarrier]
  have himage : standardTriangleVertex ''
      (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex t i),
        standardTriangleVertex (K.faceEdgeSecondIndex t i)} := by
    ext p
    simp [eq_comm]
  rw [himage, convexHull_pair, segment_eq_image_lineMap]
  rfl

/-- The inverse face chart is the restriction of `facePlaneInverseAffine` to the closed
standard triangle. -/
theorem facePlaneHomeomorph_symm_val (t : K.Face)
    (p : standardTrianglePlaneComplex.support) :
    ((K.facePlaneHomeomorph t).symm p).1.1 = K.facePlaneInverseAffine t p.1 := by
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
  change (K.faceReindexFromStandard t z).1.1 = K.facePlaneInverseAffine t p.1
  funext v
  by_cases hv : v ∈ t.1
  · simp only [faceReindexFromStandard, dite_eq_left hv,
      facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_mem _ _ hv]
    exact congrFun hz ((K.faceVertexEquiv t).symm ⟨v, hv⟩)
  · simp [faceReindexFromStandard, facePlaneInverseAffine, hv]

/-- The standard plane chart sends cyclic intrinsic edge `i` exactly onto cyclic side `i` of
the standard triangle. -/
theorem facePlaneHomeomorph_image_edge (t : K.Face) (i : ZMod 3) :
    (fun x : K.ClosedFace t => (K.facePlaneHomeomorph t x).1) ''
        {x : K.ClosedFace t | x.1 ∈ K.faceCarrier (K.faceEdge t i).1} =
      standardTriangleCircle.edgeSegment i := by
  let s := faceStandardEdge i
  have hs : s ∈ standardTrianglePlaneComplex.simplexes :=
    faceStandardEdge_mem_simplexes i
  have hgeom := standardTrianglePlaneComplex.realizationHomeomorph_image_faceCarrier
    standardTrianglePlaneComplex_pure hs
  rw [standard_cellCarrier_faceStandardEdge i] at hgeom
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    let z := K.faceReindexToStandard t x
    have hz : z ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s := by
      rw [K.faceReindexToStandard_mem_faceCarrier t s x,
        K.faceStandardEdge_map t i]
      exact hx
    rw [← hgeom]
    refine ⟨z, hz, ?_⟩
    rfl
  · intro p hp
    rw [← hgeom] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    let x : K.ClosedFace t := (K.faceReindexHomeomorph t).symm z
    have hxEdge : x.1 ∈ K.faceCarrier (K.faceEdge t i).1 := by
      rw [← K.faceStandardEdge_map t i,
        ← K.faceReindexToStandard_mem_faceCarrier t s x]
      have heq : K.faceReindexToStandard t x = z := by
        change K.faceReindexHomeomorph t x = z
        exact (K.faceReindexHomeomorph t).apply_symm_apply z
      rw [heq]
      exact hz
    refine ⟨x, hxEdge, ?_⟩
    change (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure (K.faceReindexHomeomorph t x)).1 = p
    simpa [x] using hzp

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
