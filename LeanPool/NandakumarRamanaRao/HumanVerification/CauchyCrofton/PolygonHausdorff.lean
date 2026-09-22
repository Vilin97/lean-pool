/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.CyclicPolygon

/-!
# Hausdorff perimeter of an inscribed cyclic polygon

The boundary of the polygon `polySet K A` is the union of its `m` edges, distinct edges meet in
at most one point (a set of vanishing one-dimensional Hausdorff measure), and the measure of a
segment is the distance between its endpoints.  Hence the Hausdorff perimeter of the polygon is
the sum of its edge lengths.
-/

open Set MeasureTheory NRR.Geometry
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HumanVerification.CauchyCrofton

variable {K : Body} {A : AngleSystem}

/-- The cyclic sum of edge lengths of the inscribed polygon. -/
def edgeLengthSum (K : Body) (A : AngleSystem) : ℝ :=
  ∑ j ∈ Finset.range A.m, dist (vtx K A (j : ℤ)) (vtx K A ((j : ℤ) + 1))

theorem edgeLengthSum_nonneg (K : Body) (A : AngleSystem) : 0 ≤ edgeLengthSum K A :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

/-- One-dimensional Hausdorff measure of an edge. -/
theorem hausdorffMeasure_edge (j : ℤ) :
    (μH[1] : Measure Point2) (edge K A j) = edist (vtx K A j) (vtx K A (j + 1)) := by
  simp [edge, MeasureTheory.hausdorffMeasure_segment]

/-- Every edge is a closed set. -/
theorem isClosed_edge (j : ℤ) : IsClosed (edge K A j) := by
  rw [edge, segment_eq_image']
  exact ((isCompact_Icc (a := (0:ℝ)) (b := 1)).image (by fun_prop)).isClosed

/-- Distinct edges are almost everywhere disjoint. -/
theorem aedisjoint_edge (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j k : Fin A.m} (hjk : j ≠ k) :
    AEDisjoint (μH[1] : Measure Point2) (edge K A (j : ℤ)) (edge K A (k : ℤ)) := by
  have :=
    MeasureTheory.Measure.nullSingletonClass_hausdorff Point2 zero_lt_one
  have hsub := edge_inter_subset_pair h0 (j := (j : ℤ)) (k := (k : ℤ))
    (by positivity) (by exact_mod_cast j.isLt) (by positivity) (by exact_mod_cast k.isLt)
    (by
      intro hcon
      apply hjk
      have hnat : (j : ℕ) = (k : ℕ) := by exact_mod_cast hcon
      exact Fin.ext hnat)
  change μH[1] (edge K A (j : ℤ) ∩ edge K A (k : ℤ)) = 0
  refine measure_mono_null hsub ?_
  rw [Set.insert_eq, measure_union_null (measure_singleton _) (measure_singleton _)]

/-- **Hausdorff perimeter of the inscribed polygon.** -/
theorem hPerimeter_polyBody (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    hPerimeter (polyBody K A h0) = ENNReal.ofReal (edgeLengthSum K A) := by
  rw [hPerimeter, polyBody_carrier, frontier_polySet h0]
  have hunion : (⋃ j : Fin A.m, edge K A (j : ℤ))
      = ⋃ j ∈ (Finset.univ : Finset (Fin A.m)), edge K A (j : ℤ) := by simp
  rw [hunion, measure_biUnion_finset₀ (fun j _ k _ hjk => aedisjoint_edge h0 hjk)
    (fun j _ => (isClosed_edge (j : ℤ)).nullMeasurableSet)]
  have hterm : ∀ j : Fin A.m, (μH[1] : Measure Point2) (edge K A (j : ℤ))
      = ENNReal.ofReal (dist (vtx K A (j : ℤ)) (vtx K A ((j : ℤ) + 1))) := by
    intro j
    rw [hausdorffMeasure_edge, edist_dist]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), edgeLengthSum,
    ← Finset.sum_range (fun i => ENNReal.ofReal (dist (vtx K A (i : ℤ)) (vtx K A ((i : ℤ) + 1)))),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => dist_nonneg)]

end HumanVerification.CauchyCrofton
