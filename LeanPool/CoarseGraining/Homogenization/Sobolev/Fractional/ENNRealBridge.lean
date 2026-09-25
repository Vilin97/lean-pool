/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Positive.Overlap
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Definitions

/-!
# ℝ≥0∞ bridge for the overlap Besov pieces

The overlap Besov seminorms are real-valued (`eLpNorm`-`.toReal` style); the
comparison estimates run in `ℝ≥0∞`.  This file performs the `ofReal`/`toReal`
crossing **once**: each real Besov piece is rewritten as (or bounded by) its
`ℝ≥0∞` counterpart here, and the proof files never touch `toReal` again.

Bridge lemmas toward the Gagliardo side are stated as junk-value-safe
inequalities (`≤`), which hold without integrability hypotheses; equalities
hold under `MemLp` and are provided where needed.
-/

namespace Homogenization
namespace Gagliardo

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

variable {d : ℕ}

/-- BR4 (junk-safe): the `p`-th power of the overlap oscillation, pushed to
`ℝ≥0∞`, is at most the corresponding `eLpNorm` power.  No integrability
hypothesis: if the `eLpNorm` is infinite the right side is `∞`. -/
theorem ofReal_oscillation_rpow_le (S : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) :
    ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) ≤
      (eLpNorm (fun x => u x - ScalarOverlap.cubeAverage S u) p
        (ScalarOverlap.normalizedCubeMeasure S)) ^ p.toReal := by
  unfold cubeBesovOverlapOscillation ScalarOverlap.cubeLpNorm
  rw [ENNReal.toReal_rpow]
  exact ENNReal.ofReal_toReal_le.trans
    (ENNReal.rpow_le_rpow (integralLpSeminorm_le_eLpNorm _ _ _) ENNReal.toReal_nonneg)

/-- BR3: the depth average crosses to `ℝ≥0∞` as an explicit averaged sum. -/
theorem ofReal_depthAverage_eq (Q : TriadicCube d) (j : ℕ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) :
    ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u j) =
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) := by
  have hcard : (0 : ℝ) < ((ScalarOverlap.centersAtDepth Q j).card : ℝ) := by
    exact_mod_cast ScalarOverlap.centersAtDepth_card_pos Q j
  unfold cubeBesovOverlapDepthAverage ScalarOverlap.centersAverage
  rw [ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hcard))]
  rw [ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_sum_of_nonneg fun S _hS =>
    Real.rpow_nonneg (cubeBesovOverlapOscillation_nonneg S p u) _]

/-- BR2: the depth seminorm's `p`-th power crosses to `ℝ≥0∞` as
weight-power times depth average. -/
theorem ofReal_depthSeminorm_rpow_eq (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) (u : Vec d → ℝ) (j : ℕ) :
    ENNReal.ofReal (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) =
      ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j ^ p.toReal) *
        ENNReal.ofReal (cubeBesovOverlapDepthAverage Q p u j) := by
  have hpr : p.toReal ≠ 0 :=
    (ENNReal.toReal_pos hp0 hpt).ne'
  have hw : 0 ≤ cubeBesovOverlapDepthWeight Q s j :=
    cubeBesovOverlapDepthWeight_nonneg Q s j
  have ha : 0 ≤ cubeBesovOverlapDepthAverage Q p u j :=
    cubeBesovOverlapDepthAverage_nonneg Q p u j
  unfold cubeBesovOverlapDepthSeminorm
  rw [Real.mul_rpow hw (Real.rpow_nonneg ha _), one_div,
    Real.rpow_inv_rpow ha hpr,
    ENNReal.ofReal_mul (Real.rpow_nonneg hw _)]

/-- BR1: the partial seminorm's `p`-th power crosses to `ℝ≥0∞` as the sum of
the depth-seminorm powers (diagonal case `q = p`). -/
theorem ofReal_partialSeminorm_rpow_eq (Q : TriadicCube d) (s : ℝ)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (N : ℕ) (u : Vec d → ℝ) :
    ENNReal.ofReal (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal) =
      ∑ j ∈ Finset.range (N + 1),
        ENNReal.ofReal (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) := by
  have hpr : p.toReal ≠ 0 :=
    (ENNReal.toReal_pos hp0 hpt).ne'
  have hsum : 0 ≤ ∑ j ∈ Finset.range (N + 1),
      cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal :=
    Finset.sum_nonneg fun j _hj =>
      Real.rpow_nonneg (cubeBesovOverlapDepthSeminorm_nonneg Q s p u j) _
  unfold cubeBesovOverlapPartialSeminorm
  rw [one_div, Real.rpow_inv_rpow hsum hpr]
  rw [ENNReal.ofReal_sum_of_nonneg fun j _hj =>
    Real.rpow_nonneg (cubeBesovOverlapDepthSeminorm_nonneg Q s p u j) _]

end

end Gagliardo
end Homogenization
