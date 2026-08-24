/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ChartExtraction
import LeanPool.ClassificationOfSurfaces.Moise.ElementaryMove

/-!
# A fixed polygonal patch inside the Rado chart models

The four-triangle diamond below has vertices `(+-3/4,0)` and `(0,+-3/4)`.  It lies in the open
unit disk and contains the closed radius-`1/2` disk in its interior.  Its right half gives the
corresponding half-disk patch.  These strict margins are the concrete base geometry for the
Rado induction.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The anisotropic linear equivalence carrying Moise's fixed diamond, with vertices
`(+-1,0),(0,+-2)`, to the radius-`3/4` axis diamond. -/
noncomputable def chartDiamondLinearEquiv : Plane ≃ₗ[ℝ] Plane where
  toFun p := !₂[(3 / 4 : ℝ) * p 0, (3 / 8 : ℝ) * p 1]
  invFun p := !₂[(4 / 3 : ℝ) * p 0, (8 / 3 : ℝ) * p 1]
  left_inv p := by
    ext i
    fin_cases i <;> simp <;> ring
  right_inv p := by
    ext i
    fin_cases i <;> simp <;> ring
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r p := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Affine form of `chartDiamondLinearEquiv`. -/
noncomputable def chartDiamondAffineEquiv : Plane ≃ᵃ[ℝ] Plane :=
  chartDiamondLinearEquiv.toAffineEquiv

@[simp] theorem chartDiamondAffineEquiv_apply_zero (p : Plane) :
    chartDiamondAffineEquiv p 0 = (3 / 4 : ℝ) * p 0 := rfl

@[simp] theorem chartDiamondAffineEquiv_apply_one (p : Plane) :
    chartDiamondAffineEquiv p 1 = (3 / 8 : ℝ) * p 1 := rfl

@[simp] theorem chartDiamondAffineEquiv_symm_apply_zero (p : Plane) :
    chartDiamondAffineEquiv.symm p 0 = (4 / 3 : ℝ) * p 0 := rfl

@[simp] theorem chartDiamondAffineEquiv_symm_apply_one (p : Plane) :
    chartDiamondAffineEquiv.symm p 1 = (8 / 3 : ℝ) * p 1 := rfl

/-- The fixed four-triangle chart patch. -/
noncomputable def chartDiamondMesh : TriangleMesh :=
  (diamondFanMesh 0 (by norm_num) (by norm_num)).mapAffineEquiv chartDiamondAffineEquiv

/-- The fixed chart patch as a pure plane complex. -/
noncomputable def chartDiamondComplex : PlaneComplex :=
  chartDiamondMesh.toPlaneComplex

theorem chartDiamondComplex_pure : chartDiamondComplex.IsPure2 :=
  chartDiamondMesh.toPlaneComplex_isPure2

theorem chartDiamondComplex_support :
    chartDiamondComplex.support = chartDiamondAffineEquiv '' diamondPatch := by
  rw [chartDiamondComplex, chartDiamondMesh,
    TriangleMesh.mapAffineEquiv_support,
    diamondFanMesh_support]

private theorem chartDiamond_vertex_mem_closedBall (v : chartDiamondMesh.Vertex) :
    chartDiamondMesh.position v ∈ Metric.closedBall (0 : Plane) (3 / 4) := by
  have hs9 : Real.sqrt 9 = 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9), Real.sqrt_nonneg 9]
  have hs16 : Real.sqrt 16 = 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_nonneg 16]
  change dist (chartDiamondAffineEquiv (diamondFanPosition 0 v)) 0 ≤ 3 / 4
  rw [dist_zero_right]
  fin_cases v <;>
    simp [chartDiamondAffineEquiv, chartDiamondLinearEquiv, diamondFanPosition,
      planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;>
    norm_num [Real.sqrt_sq_eq_abs, hs9, hs16]

/-- The whole polygonal patch lies strictly inside the open unit disk. -/
theorem chartDiamondComplex_support_subset_ball :
    chartDiamondComplex.support ⊆ Metric.ball (0 : Plane) 1 := by
  intro x hx
  rw [chartDiamondComplex, TriangleMesh.toPlaneComplex_support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  have hclosed : x ∈ Metric.closedBall (0 : Plane) (3 / 4) := by
    apply convexHull_min ?_ (convex_closedBall (0 : Plane) (3 / 4)) hxt
    rintro y ⟨v, hv, rfl⟩
    exact chartDiamond_vertex_mem_closedBall v
  exact Metric.closedBall_subset_ball (by norm_num) hclosed

private theorem abs_add_abs_lt_three_four_of_mem_closedBall_half {x : Plane}
    (hx : x ∈ Metric.closedBall (0 : Plane) (1 / 2)) :
    |x 0| + |x 1| < 3 / 4 := by
  have hnorm : ‖x‖ ≤ 1 / 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hnormsq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_two]
  have hsquares : (|x 0| + |x 1|) ^ 2 ≤ 2 * (x 0 ^ 2 + x 1 ^ 2) := by
    nlinarith [sq_nonneg (|x 0| - |x 1|), sq_abs (x 0), sq_abs (x 1)]
  have hnormnonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have habsnonneg : 0 ≤ |x 0| + |x 1| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [← hnormsq] at hsquares
  nlinarith

/-- The closed radius-`1/2` disk is contained in the interior of the polygonal patch. -/
theorem closedBall_half_subset_interior_chartDiamond :
    Metric.closedBall (0 : Plane) (1 / 2) ⊆ interior chartDiamondComplex.support := by
  intro x hx
  have hl1 := abs_add_abs_lt_three_four_of_mem_closedBall_half hx
  let q : Plane := chartDiamondAffineEquiv.symm x
  have hpp : x 0 + x 1 < 3 / 4 :=
    (add_le_add (le_abs_self _) (le_abs_self _)).trans_lt hl1
  have hpn : x 0 - x 1 < 3 / 4 := by
    have := add_le_add (le_abs_self (x 0)) (neg_le_abs (x 1))
    linarith
  have hnp : -x 0 + x 1 < 3 / 4 := by
    have := add_le_add (neg_le_abs (x 0)) (le_abs_self (x 1))
    linarith
  have hnn : -x 0 - x 1 < 3 / 4 := by
    have := add_le_add (neg_le_abs (x 0)) (neg_le_abs (x 1))
    linarith
  have hq : q ∈ StrictlyInDiamond := by
    change 0 < diamondSlackUR q ∧ 0 < diamondSlackUL q ∧
      0 < diamondSlackLR q ∧ 0 < diamondSlackLL q
    simp only [diamondSlackUR_eq, diamondSlackUL_eq, diamondSlackLR_eq,
      diamondSlackLL_eq, q, chartDiamondAffineEquiv_symm_apply_zero,
      chartDiamondAffineEquiv_symm_apply_one]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hqint : q ∈ interior diamondPatch := strictlyInDiamond_subset_interior hq
  rw [chartDiamondComplex_support]
  change x ∈ interior
    (chartDiamondAffineEquiv.toContinuousAffineEquiv.toHomeomorph '' diamondPatch)
  rw [← chartDiamondAffineEquiv.toContinuousAffineEquiv.toHomeomorph.image_interior]
  exact ⟨q, hqint, chartDiamondAffineEquiv.apply_symm_apply x⟩

/-- The two-triangle right half of the fixed chart diamond. -/
noncomputable abbrev chartHalfDiamondMesh : TriangleMesh :=
  ((diamondFanMesh 0 (by norm_num) (by norm_num)).restrictTriangles
      fun t : Finset (Fin 5) => 1 ∈ t)
    |>.mapAffineEquiv chartDiamondAffineEquiv

/-- The right-half chart patch as a pure plane complex. -/
noncomputable abbrev chartHalfDiamondComplex : PlaneComplex :=
  chartHalfDiamondMesh.toPlaneComplex

theorem chartHalfDiamondComplex_pure : chartHalfDiamondComplex.IsPure2 :=
  chartHalfDiamondMesh.toPlaneComplex_isPure2

private theorem restrictedRightDiamond_support :
    (((diamondFanMesh 0 (by norm_num) (by norm_num)).restrictTriangles
      fun t : Finset (Fin 5) => 1 ∈ t).toPlaneComplex.support) = diamondRightRegion := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ diamondFanTriangles.filter (fun t : Finset (Fin 5) => 1 ∈ t),
    convexHull ℝ (diamondFanPosition 0 '' (t : Set (Fin 5)))) = diamondRightRegion
  rw [← diamondFan_right_union (a := 0) (by norm_num) (by norm_num)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨t, ht, hxt⟩
    rcases Finset.mem_filter.mp ht with ⟨ht, h1t⟩
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · simp at h1t
    · exact Or.inl hxt
    · simp at h1t
    · exact Or.inr hxt
  · rintro (hxt | hxt)
    · exact ⟨{1, 2, 4}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{1, 4, 3}, by simp [diamondFanTriangles], hxt⟩

theorem chartHalfDiamondComplex_support :
    chartHalfDiamondComplex.support = chartDiamondAffineEquiv '' diamondRightRegion := by
  rw [chartHalfDiamondComplex, chartHalfDiamondMesh, TriangleMesh.mapAffineEquiv_support,
    restrictedRightDiamond_support]

theorem chartHalfDiamondComplex_support_subset_modelRegion :
    chartHalfDiamondComplex.support ⊆ ChartKind.halfDisk.modelRegion := by
  rw [chartHalfDiamondComplex_support]
  rintro x ⟨q, hq, rfl⟩
  refine ⟨chartDiamondComplex_support_subset_ball ?_, ?_⟩
  · rw [chartDiamondComplex_support]
    exact ⟨q, Or.inr hq, rfl⟩
  · have hq0 : 0 ≤ q 0 := by
      rw [diamondRightRegion] at hq
      change q ∈ {p : Plane | 0 ≤ cartesianX p}
      apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hq
      rintro y ⟨i, rfl⟩
      fin_cases i <;> simp [planePoint]
    exact mul_nonneg (by norm_num) hq0

theorem diamondRightRegion_eq_patch_inter_nonneg :
    diamondRightRegion = diamondPatch ∩ {p : Plane | 0 ≤ p 0} := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨Or.inr hp, ?_⟩
    rw [diamondRightRegion] at hp
    change p ∈ {q : Plane | 0 ≤ cartesianX q}
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hp
    rintro q ⟨i, rfl⟩
    fin_cases i <;> simp [planePoint]
  · rintro p ⟨hp, hp0⟩
    change 0 ≤ p 0 at hp0
    rw [diamondPatch_eq_inDiamond] at hp
    rcases hp with ⟨hUR, hUL, hLR, hLL⟩
    rw [diamondSlackUR_eq] at hUR
    rw [diamondSlackUL_eq] at hUL
    rw [diamondSlackLR_eq] at hLR
    rw [diamondSlackLL_eq] at hLL
    let w : Fin 3 → ℝ :=
      ![(p 1 + 2 - 2 * p 0) / 4, (2 - 2 * p 0 - p 1) / 4, p 0]
    rw [diamondRightRegion]
    apply mem_convexHull_range_fin3_of_weights _ p w
    · intro i
      fin_cases i <;> simp [w] <;> linarith
    · simp [w]
      ring
    · ext i
      fin_cases i <;> simp [w, planePoint]
      all_goals ring

/-- The closed radius-`1/2` half-disk core is covered by the two-triangle half patch. -/
theorem halfCore_subset_chartHalfDiamond_support :
    ChartKind.halfDisk.modelCore ⊆ chartHalfDiamondComplex.support := by
  rintro x ⟨hxball, hx0⟩
  let q : Plane := chartDiamondAffineEquiv.symm x
  have hxint := closedBall_half_subset_interior_chartDiamond hxball
  have hxsupport : x ∈ chartDiamondComplex.support := interior_subset hxint
  rw [chartDiamondComplex_support] at hxsupport
  rcases hxsupport with ⟨q', hq', hq'x⟩
  have hq'eq : q' = q := by
    apply chartDiamondAffineEquiv.injective
    rw [hq'x, chartDiamondAffineEquiv.apply_symm_apply]
  subst q'
  have hq0 : 0 ≤ q 0 := by
    simp only [q, chartDiamondAffineEquiv_symm_apply_zero]
    exact mul_nonneg (by norm_num) hx0
  rw [chartHalfDiamondComplex_support, diamondRightRegion_eq_patch_inter_nonneg]
  exact ⟨q, ⟨hq', hq0⟩, chartDiamondAffineEquiv.apply_symm_apply x⟩

theorem chartHalfDiamond_support_eq_inter_halfPlane :
    chartHalfDiamondComplex.support = chartDiamondComplex.support ∩ HalfPlaneSet := by
  rw [chartHalfDiamondComplex_support, chartDiamondComplex_support,
    diamondRightRegion_eq_patch_inter_nonneg]
  ext x
  constructor
  · rintro ⟨q, ⟨hqPatch, hq0⟩, rfl⟩
    refine ⟨⟨q, hqPatch, rfl⟩, ?_⟩
    change 0 ≤ (3 / 4 : ℝ) * q 0
    exact mul_nonneg (by norm_num) hq0
  · rintro ⟨⟨q, hqPatch, hqx⟩, hx0⟩
    subst x
    have hq0 : 0 ≤ q 0 := by
      change 0 ≤ (3 / 4 : ℝ) * q 0 at hx0
      nlinarith
    exact ⟨q, ⟨hqPatch, hq0⟩, rfl⟩

/-- In barycentric coordinates on the fixed half-diamond, the normal coordinate is exactly the
weight of its unique positive-normal vertex, up to the fixed positive scale. -/
def chartHalfDiamondRightVertex : chartHalfDiamondComplex.Vertex := by
  change Fin 5
  exact 1

theorem chartHalfDiamond_baryEval_coordZero
    (x : GeometricRealization chartHalfDiamondComplex.Vertex
      chartHalfDiamondComplex.cells) :
    chartHalfDiamondComplex.baryEval x.1 0 =
      (3 / 4 : ℝ) * x.1 chartHalfDiamondRightVertex := by
  obtain ⟨t, ht, hsupport⟩ := x.2.2
  change Finset (Fin 5) at t
  have hzero : x.1 (0 : Fin 5) = 0 := by
    apply hsupport
    intro h0
    have ht' : t = {1, 2, 4} ∨ t = {1, 4, 3} := by
      rw [show chartHalfDiamondComplex.cells = chartHalfDiamondMesh.triangles by
        exact TriangleMesh.toPlaneComplex_cells chartHalfDiamondMesh] at ht
      change t ∈ diamondFanTriangles.filter (fun t : Finset (Fin 5) => 1 ∈ t) at ht
      obtain ⟨htFan, h1⟩ := Finset.mem_filter.mp ht
      simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at htFan
      rcases htFan with rfl | rfl | rfl | rfl
      · simp at h1
      · exact Or.inl rfl
      · simp at h1
      · exact Or.inr rfl
    rcases ht' with rfl | rfl
    · exact (by decide : (0 : Fin 5) ∉ ({1, 2, 4} : Finset (Fin 5))) h0
    · exact (by decide : (0 : Fin 5) ∉ ({1, 4, 3} : Finset (Fin 5))) h0
  change
    (∑ v : Fin 5, x.1 v • chartDiamondAffineEquiv (diamondFanPosition 0 v)) 0 =
      (3 / 4 : ℝ) * x.1 (1 : Fin 5)
  simp [chartDiamondAffineEquiv, chartDiamondLinearEquiv, diamondFanPosition, planePoint,
    Fin.sum_univ_succ, hzero]
  ring

theorem chartHalfDiamond_baryEval_coordZero_eq_zero_iff
    (x : GeometricRealization chartHalfDiamondComplex.Vertex
      chartHalfDiamondComplex.cells) :
    chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
      x.1 chartHalfDiamondRightVertex = 0 := by
  rw [chartHalfDiamond_baryEval_coordZero]
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h, mul_zero]

/-- The `chartHalfDiamondUpperBoundaryEdge` declaration. -/
def chartHalfDiamondUpperBoundaryEdge :
    Finset chartHalfDiamondComplex.Vertex := by
  change Finset (Fin 5)
  exact {2, 4}

/-- The `chartHalfDiamondLowerBoundaryEdge` declaration. -/
def chartHalfDiamondLowerBoundaryEdge :
    Finset chartHalfDiamondComplex.Vertex := by
  change Finset (Fin 5)
  exact {4, 3}

theorem chartHalfDiamond_coordZero_iff_boundaryEdgeCarrier
    (x : GeometricRealization chartHalfDiamondComplex.Vertex
      chartHalfDiamondComplex.cells) :
    chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
      (∀ v ∉ chartHalfDiamondUpperBoundaryEdge, x.1 v = 0) ∨
      (∀ v ∉ chartHalfDiamondLowerBoundaryEdge, x.1 v = 0) := by
  rw [chartHalfDiamond_baryEval_coordZero_eq_zero_iff]
  obtain ⟨t, ht, hsupport⟩ := x.2.2
  change Finset (Fin 5) at t
  have ht' : t = {1, 2, 4} ∨ t = {1, 4, 3} := by
    rw [show chartHalfDiamondComplex.cells = chartHalfDiamondMesh.triangles by
      exact TriangleMesh.toPlaneComplex_cells chartHalfDiamondMesh] at ht
    change t ∈ diamondFanTriangles.filter (fun t : Finset (Fin 5) => 1 ∈ t) at ht
    obtain ⟨htFan, h1⟩ := Finset.mem_filter.mp ht
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at htFan
    rcases htFan with rfl | rfl | rfl | rfl
    · simp at h1
    · exact Or.inl rfl
    · simp at h1
    · exact Or.inr rfl
  constructor
  · intro hright
    rcases ht' with rfl | rfl
    · left
      intro v hv
      change Fin 5 at v
      fin_cases v
      · exact hsupport (0 : Fin 5) (by decide)
      · exact hright
      · exact (hv (by decide)).elim
      · exact hsupport (3 : Fin 5) (by decide)
      · exact (hv (by decide)).elim
    · right
      intro v hv
      change Fin 5 at v
      fin_cases v
      · exact hsupport (0 : Fin 5) (by decide)
      · exact hright
      · exact hsupport (2 : Fin 5) (by decide)
      · exact (hv (by decide)).elim
      · exact (hv (by decide)).elim
  · rintro (hupper | hlower)
    · apply hupper chartHalfDiamondRightVertex
      decide
    · apply hlower chartHalfDiamondRightVertex
      decide

/-- The finite polygonal patch assigned to a disk or half-disk chart model. -/
noncomputable abbrev ChartKind.patchComplex : ChartKind → PlaneComplex
  | .disk => chartDiamondComplex
  | .halfDisk => chartHalfDiamondComplex

/-- The model-boundary condition appropriate to a chart kind.  A disk chart has no boundary
stratum; in a half-disk chart it is the zero normal-coordinate line. -/
def ChartKind.IsModelBoundary : (k : ChartKind) → Plane → Prop
  | .disk, _ => False
  | .halfDisk, p => p 0 = 0

/-- The explicit edge family carrying the model boundary in the fixed chart patch. -/
noncomputable def ChartKind.patchBoundaryEdges :
    (k : ChartKind) → Finset (Finset k.patchComplex.Vertex)
  | .disk => ∅
  | .halfDisk => {chartHalfDiamondUpperBoundaryEdge, chartHalfDiamondLowerBoundaryEdge}

/-- The fixed patch meets its model boundary exactly in the carrier of
`patchBoundaryEdges`. -/
theorem ChartKind.patchComplex_isModelBoundary_iff (k : ChartKind)
    (x : GeometricRealization k.patchComplex.Vertex k.patchComplex.cells) :
    k.IsModelBoundary (k.patchComplex.baryEval x.1) ↔
      ∃ e ∈ k.patchBoundaryEdges, ∀ v ∉ e, x.1 v = 0 := by
  cases k with
  | disk => simp [ChartKind.IsModelBoundary, ChartKind.patchBoundaryEdges]
  | halfDisk =>
      change chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
        ∃ e ∈
          ({chartHalfDiamondUpperBoundaryEdge, chartHalfDiamondLowerBoundaryEdge} :
            Finset (Finset chartHalfDiamondComplex.Vertex)),
          ∀ v ∉ e, x.1 v = 0
      rw [chartHalfDiamond_coordZero_iff_boundaryEdgeCarrier]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact ⟨chartHalfDiamondUpperBoundaryEdge, Or.inl rfl, h⟩
        · exact ⟨chartHalfDiamondLowerBoundaryEdge, Or.inr rfl, h⟩
      · rintro ⟨e, he | he, h⟩
        · subst e
          exact Or.inl h
        · subst e
          exact Or.inr h

/-- Facewise exposed form of the fixed patch boundary.  Every patch triangle meets the model
boundary in an intrinsic face of cardinality at most two. -/
theorem ChartKind.patchComplex_isModelBoundary_facewise (k : ChartKind) :
    ∀ t ∈ k.patchComplex.cells, ∃ b : Finset k.patchComplex.Vertex,
      b ⊆ t ∧ b.card ≤ 2 ∧
        ∀ x : GeometricRealization k.patchComplex.Vertex k.patchComplex.cells,
          (∀ v ∉ t, x.1 v = 0) →
            (k.IsModelBoundary (k.patchComplex.baryEval x.1) ↔
              ∀ v ∉ b, x.1 v = 0) := by
  classical
  cases k with
  | disk =>
      intro t ht
      refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro x hxt
      constructor
      · simp [ChartKind.IsModelBoundary]
      · intro hxEmpty
        have hxzero : ∀ v, x.1 v = 0 := by
          intro v
          exact hxEmpty v (by simp)
        have hsum : ∑ v, x.1 v = 0 := by simp [hxzero]
        linarith [x.2.1.2, hsum]
  | halfDisk =>
      intro t ht
      let r : ChartKind.halfDisk.patchComplex.Vertex := by
        change Fin 5
        exact 1
      let b : Finset ChartKind.halfDisk.patchComplex.Vertex := t.erase r
      refine ⟨b, Finset.erase_subset _ _, ?_, ?_⟩
      · have hr : r ∈ t := by
          change t ∈
            (diamondFanTriangles.filter fun u : Finset (Fin 5) => 1 ∈ u) at ht
          exact (Finset.mem_filter.mp ht).2
        change (t.erase r).card ≤ 2
        rw [Finset.card_erase_of_mem hr]
        have htcard : t.card = 3 :=
          ChartKind.halfDisk.patchComplex.card_of_mem_cells ht
        omega
      · intro x hxt
        change chartHalfDiamondComplex.baryEval x.1 0 = 0 ↔
          ∀ v ∉ t.erase r, x.1 v = 0
        rw [chartHalfDiamond_baryEval_coordZero_eq_zero_iff,
          show chartHalfDiamondRightVertex = r by rfl]
        constructor
        · intro hrZero v hvb
          by_cases hvt : v ∈ t
          · have hvr : v = r := by
              by_contra hne
              exact hvb (Finset.mem_erase.mpr ⟨hne, hvt⟩)
            simpa [r, hvr] using hrZero
          · exact hxt v hvt
        · intro hx
          apply hx r
          simp []

/-- Every explicitly designated patch-boundary edge is an edge of the patch complex. -/
theorem ChartKind.mem_patchComplex_edges_of_mem_patchBoundaryEdges (k : ChartKind)
    {e : Finset k.patchComplex.Vertex} (he : e ∈ k.patchBoundaryEdges) :
    e ∈ k.patchComplex.cells.biUnion fun t => t.powersetCard 2 := by
  cases k with
  | disk => simp [ChartKind.patchBoundaryEdges] at he
  | halfDisk =>
      change e ∈
        ({chartHalfDiamondUpperBoundaryEdge, chartHalfDiamondLowerBoundaryEdge} :
          Finset (Finset chartHalfDiamondComplex.Vertex)) at he
      rcases Finset.mem_insert.mp he with he | he
      · rw [he]
        apply Finset.mem_biUnion.mpr
        refine ⟨({1, 2, 4} : Finset (Fin 5)), ?_, ?_⟩
        · change ({1, 2, 4} : Finset (Fin 5)) ∈
            diamondFanTriangles.filter fun t => 1 ∈ t
          decide
        · exact Finset.mem_powersetCard.mpr ⟨by decide, by decide⟩
      · have he' := Finset.mem_singleton.mp he
        rw [he']
        apply Finset.mem_biUnion.mpr
        refine ⟨({1, 4, 3} : Finset (Fin 5)), ?_, ?_⟩
        · change ({1, 4, 3} : Finset (Fin 5)) ∈
            diamondFanTriangles.filter fun t => 1 ∈ t
          decide
        · exact Finset.mem_powersetCard.mpr ⟨by decide, by decide⟩

theorem ChartKind.patchComplex_pure (k : ChartKind) : k.patchComplex.IsPure2 := by
  cases k with
  | disk => exact chartDiamondComplex_pure
  | halfDisk => exact chartHalfDiamondComplex_pure

/-- The four triangles in the fixed disk-chart patch have a connected dual graph. -/
theorem diamondFanTriangles_isDualConnected :
    TriangleFamily.IsDualConnected diamondFanTriangles := by
  change TriangleFamily.IsDualConnected
    ({{0, 4, 2}, {1, 2, 4}, {0, 3, 4}, {1, 4, 3}} :
      Finset (Finset (Fin 5)))
  have h₃ : TriangleFamily.IsDualConnected
      ({{1, 4, 3}} : Finset (Finset (Fin 5))) :=
    TriangleFamily.isDualConnected_singleton {1, 4, 3}
  have h₂₃ : TriangleFamily.IsDualConnected
      (insert {0, 3, 4} ({{1, 4, 3}} : Finset (Finset (Fin 5)))) := by
    apply TriangleFamily.isDualConnected_insert h₃ {0, 3, 4} ⟨{1, 4, 3}, by simp⟩
    exact ⟨{3, 4}, by decide, by decide, by decide⟩
  have h₁₂₃ : TriangleFamily.IsDualConnected
      (insert {1, 2, 4}
        (insert {0, 3, 4} ({{1, 4, 3}} : Finset (Finset (Fin 5))))) := by
    apply TriangleFamily.isDualConnected_insert h₂₃ {1, 2, 4} ⟨{1, 4, 3}, by simp⟩
    exact ⟨{1, 4}, by decide, by decide, by decide⟩
  apply TriangleFamily.isDualConnected_insert h₁₂₃ {0, 4, 2} ⟨{1, 2, 4}, by simp⟩
  exact ⟨{2, 4}, by decide, by decide, by decide⟩

/-- The two triangles in the fixed half-disk-chart patch have a connected dual graph. -/
theorem halfDiamondTriangles_isDualConnected :
    TriangleFamily.IsDualConnected
      (diamondFanTriangles.filter fun t => 1 ∈ t) := by
  change TriangleFamily.IsDualConnected
    ({{1, 2, 4}, {1, 4, 3}} : Finset (Finset (Fin 5)))
  have h₃ : TriangleFamily.IsDualConnected
      ({{1, 4, 3}} : Finset (Finset (Fin 5))) :=
    TriangleFamily.isDualConnected_singleton {1, 4, 3}
  apply TriangleFamily.isDualConnected_insert h₃ {1, 2, 4} ⟨{1, 4, 3}, by simp⟩
  exact ⟨{1, 4}, by decide, by decide, by decide⟩

/-- Every fixed chart patch starts with a connected dual graph. -/
theorem ChartKind.patchComplex_isDualConnected (k : ChartKind) :
    TriangleFamily.IsDualConnected k.patchComplex.cells := by
  cases k with
  | disk =>
      change TriangleFamily.IsDualConnected diamondFanTriangles
      exact diamondFanTriangles_isDualConnected
  | halfDisk =>
      change TriangleFamily.IsDualConnected
        (diamondFanTriangles.filter fun t => 1 ∈ t)
      exact halfDiamondTriangles_isDualConnected

theorem ChartKind.patchComplex_support_subset_modelRegion (k : ChartKind) :
    k.patchComplex.support ⊆ k.modelRegion := by
  cases k with
  | disk => exact chartDiamondComplex_support_subset_ball
  | halfDisk => exact chartHalfDiamondComplex_support_subset_modelRegion

theorem ChartKind.modelCore_subset_patchComplex_support (k : ChartKind) :
    k.modelCore ⊆ k.patchComplex.support := by
  cases k with
  | disk => exact closedBall_half_subset_interior_chartDiamond |>.trans interior_subset
  | halfDisk => exact halfCore_subset_chartHalfDiamond_support

/-- In model-region topology, the fixed chart core lies in the interior of the fixed polygonal
patch.  In the half-disk case this is relative interior, so edge-line core points are included. -/
theorem ChartKind.modelCore_subset_interior_patchInRegion (k : ChartKind) :
    {p : k.modelRegion | (p : Plane) ∈ k.modelCore} ⊆
      interior {p : k.modelRegion | (p : Plane) ∈ k.patchComplex.support} := by
  intro x hx
  cases k with
  | disk =>
      have hxint : (x : Plane) ∈ interior chartDiamondComplex.support :=
        closedBall_half_subset_interior_chartDiamond hx
      let O : Set (ChartKind.disk.modelRegion) :=
        Subtype.val ⁻¹' interior chartDiamondComplex.support
      have hOopen : IsOpen O :=
        isOpen_interior.preimage continuous_subtype_val
      have hOsub : O ⊆ {p : ChartKind.disk.modelRegion |
          (p : Plane) ∈ chartDiamondComplex.support} :=
        fun p hp => by
          change (p : Plane) ∈ interior chartDiamondComplex.support at hp
          exact (show interior chartDiamondComplex.support ⊆
            chartDiamondComplex.support from interior_subset) hp
      exact interior_maximal hOsub hOopen hxint
  | halfDisk =>
      have hxint : (x : Plane) ∈ interior chartDiamondComplex.support :=
        closedBall_half_subset_interior_chartDiamond hx.1
      let O : Set (ChartKind.halfDisk.modelRegion) :=
        Subtype.val ⁻¹' interior chartDiamondComplex.support
      have hOopen : IsOpen O :=
        isOpen_interior.preimage continuous_subtype_val
      have hOsub : O ⊆ {p : ChartKind.halfDisk.modelRegion |
          (p : Plane) ∈ chartHalfDiamondComplex.support} := by
        intro p hp
        change (p : Plane) ∈ interior chartDiamondComplex.support at hp
        rw [chartHalfDiamond_support_eq_inter_halfPlane]
        exact ⟨(show interior chartDiamondComplex.support ⊆
          chartDiamondComplex.support from interior_subset) hp, p.2.2⟩
      exact interior_maximal hOsub hOopen hxint

/-- Finite valence check for the four-triangle diamond fan. -/
theorem diamondFanTriangles_edge_valence (e : Finset (Fin 5)) (he : e.card = 2) :
    (diamondFanTriangles.filter fun t => e ⊆ t).card ≤ 2 := by
  decide +revert

/-- Finite valence check for the two-triangle half-diamond fan. -/
theorem halfDiamondTriangles_edge_valence (e : Finset (Fin 5)) :
    ((diamondFanTriangles.filter fun t => 1 ∈ t).filter fun t => e ⊆ t).card ≤ 2 := by
  decide +revert

theorem ChartKind.patchComplex_edge_valence (k : ChartKind)
    (e : Finset k.patchComplex.Vertex) (he : e.card = 2) :
    (k.patchComplex.cells.filter fun t => e ⊆ t).card ≤ 2 := by
  cases k with
  | disk =>
      change (chartDiamondMesh.toPlaneComplex.cells.filter fun t => e ⊆ t).card ≤ 2
      rw [TriangleMesh.toPlaneComplex_cells]
      change (diamondFanTriangles.filter fun t => e ⊆ t).card ≤ 2
      exact diamondFanTriangles_edge_valence e he
  | halfDisk =>
      change (chartHalfDiamondMesh.toPlaneComplex.cells.filter fun t => e ⊆ t).card ≤ 2
      rw [TriangleMesh.toPlaneComplex_cells]
      change ((diamondFanTriangles.filter fun t => 1 ∈ t).filter fun t => e ⊆ t).card ≤ 2
      exact halfDiamondTriangles_edge_valence e

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
