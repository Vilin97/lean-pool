/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDualNegativeBesov
import LeanPool.CoarseGraining.Homogenization.Besov.Negative

/-!
# Legacy scalar circ versus the source negative Besov envelope

The legacy scalar circ partial norms use real-valued finite sums and include
the depths `0, …, N`.  The source-aligned scalar envelope uses `ENNReal` and
the half-open finite range `0, …, N - 1`.  This module records the literal
finite-depth change of presentation without adding an `Lᵖ` assumption to the
represented `L²` field.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped BigOperators ENNReal

noncomputable section

private theorem cubeScaleFactor_div_pow_eq_sourceZPow {d : ℕ} (Q : TriadicCube d)
    (j : ℕ) :
    cubeScaleFactor Q / (3 : ℝ) ^ j = (3 : ℝ) ^ (Q.scale - (j : ℤ)) := by
  unfold cubeScaleFactor
  rw [zpow_sub₀]
  · simp [div_eq_mul_inv]
  · norm_num

private theorem legacy_circ_depth_weight_eq_source {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (j : ℕ) :
    cubeBesovCircDepthWeight Q s j =
      (3 : ℝ) ^ (s * ((Q.scale - (j : ℤ) : ℤ) : ℝ)) := by
  unfold cubeBesovCircDepthWeight
  rw [cubeScaleFactor_div_pow_eq_sourceZPow]
  rw [← Real.rpow_intCast (3 : ℝ) (Q.scale - (j : ℤ)),
    ← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
  congr 1
  ring

private theorem source_weight_eq_legacy_weight_rpow {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent) (j : ℕ) :
    ENNReal.ofReal
        (Real.rpow 3 (s.1 * p.exponent.toReal *
          (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) =
      (ENNReal.ofReal (cubeBesovCircDepthWeight Q s.1 j)) ^ p.exponent.toReal := by
  rw [legacy_circ_depth_weight_eq_source]
  rw [ENNReal.ofReal_rpow_of_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)]
  congr 1
  rw [← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
  congr 1
  ring

private theorem legacy_circ_depth_average_eq_source_block_sum {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent)
    (f : Vec d → ℝ) (j : ℕ) :
    ENNReal.ofReal (cubeBesovCircDepthAverage Q p.exponent f j) =
      ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (descendantsAtDepth Q j).attach.sum (fun R =>
          (ENNReal.ofReal |cubeAverage R.1 f|) ^ p.exponent.toReal) := by
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
  unfold cubeBesovCircDepthAverage descendantsAverage
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro R _
      rw [Real.norm_eq_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg]
    · intro R _
      exact Real.rpow_nonneg (norm_nonneg _) _
  · exact inv_nonneg.mpr (by positivity)

theorem cubeEuclideanNegativeBesovScalarDepthEnergy_eq_legacy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) (j : ℕ) :
    cubeEuclideanNegativeBesovScalarDepthEnergy Q s p F i j =
      (ENNReal.ofReal
        (cubeBesovCircDepthSeminorm Q s.1 p.exponent (fun x => F.toField x i) j)) ^
        p.exponent.toReal := by
  classical
  have hsource : Q.scale - (j : ℤ) ≤ Q.scale := by omega
  have hdepth : (Q.scale - (Q.scale - (j : ℤ))).toNat = j := by omega
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hweight : 0 ≤ cubeBesovCircDepthWeight Q s.1 j :=
    cubeBesovCircDepthWeight_nonneg Q s.1 j
  have havg : 0 ≤ cubeBesovCircDepthAverage Q p.exponent
      (fun x => F.toField x i) j :=
    cubeBesovCircDepthAverage_nonneg Q p.exponent (fun x => F.toField x i) j
  unfold cubeEuclideanNegativeBesovScalarDepthEnergy
    cubeBesovCircDepthSeminorm
  rw [descendantsAtScale_eq_descendantsAtDepth Q hsource, hdepth]
  rw [source_weight_eq_legacy_weight_rpow]
  rw [mul_assoc]
  rw [← legacy_circ_depth_average_eq_source_block_sum Q p (fun x => F.toField x i) j]
  rw [show (1 / p.exponent.toReal) = (p.exponent.toReal)⁻¹ by ring]
  rw [ENNReal.ofReal_mul hweight]
  rw [← ENNReal.ofReal_rpow_of_nonneg havg (inv_nonneg.mpr hp.le)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [← ENNReal.rpow_mul]
  rw [show (p.exponent.toReal)⁻¹ * p.exponent.toReal = 1 by field_simp [hp.ne']]
  simp only [ENNReal.rpow_one]

/-- The legacy partial norm at truncation `N` includes exactly the source
depths in the half-open range `N + 1`. -/
theorem cubeEuclideanNegativeBesovScalarPartialENorm_succ_eq_legacy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) (N : ℕ) :
    cubeEuclideanNegativeBesovScalarPartialENorm Q s p F i (N + 1) =
      ENNReal.ofReal
        (cubeBesovCircPartialNorm Q s.1 p.exponent p.exponent
          N (fun x => F.toField x i)) := by
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  unfold cubeEuclideanNegativeBesovScalarPartialENorm
    cubeBesovCircPartialNorm cubeBesovCircPartialSeminorm
  rw [show (1 / p.exponent.toReal) = (p.exponent.toReal)⁻¹ by ring]
  rw [← ENNReal.ofReal_rpow_of_nonneg]
  · rw [ENNReal.ofReal_sum_of_nonneg]
    · apply congrArg (fun z : ℝ≥0∞ => z ^ (p.exponent.toReal)⁻¹)
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← ENNReal.ofReal_rpow_of_nonneg]
      · exact cubeEuclideanNegativeBesovScalarDepthEnergy_eq_legacy Q s p F i j
      · exact cubeBesovCircDepthSeminorm_nonneg Q s.1 p.exponent
          (fun x => F.toField x i) j
      · exact hp.le
    · intro j _
      exact Real.rpow_nonneg
        (cubeBesovCircDepthSeminorm_nonneg Q s.1 p.exponent
          (fun x => F.toField x i) j) _
  · exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg
      (cubeBesovCircDepthSeminorm_nonneg Q s.1 p.exponent
        (fun x => F.toField x i) j) _
  · exact inv_nonneg.mpr hp.le

/-- Every finite legacy circ partial norm is top-safely controlled by the
frozen source-facing vector negative Besov seminorm. -/
theorem ennreal_ofReal_cubeBesovCircPartialNorm_le_cubeEuclideanNegativeBesovESeminorm
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (i : Fin d) (N : ℕ) :
    ENNReal.ofReal
        (cubeBesovCircPartialNorm Q s.1 p.exponent p.exponent
          N (fun x => F.toField x i)) ≤
      cubeEuclideanNegativeBesovESeminorm Q s p F := by
  rw [← cubeEuclideanNegativeBesovScalarPartialENorm_succ_eq_legacy Q s p F i N]
  exact cubeEuclideanNegativeBesovScalarPartialENorm_le Q s p F i (N + 1)

end

end ABK26
end Ch03
end Book
end Homogenization
