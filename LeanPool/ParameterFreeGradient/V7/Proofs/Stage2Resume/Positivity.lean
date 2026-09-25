/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2.Controller

/-!
Positive constants and endpoint estimates for geometric trial amortization.
-/

@[expose] public section

namespace V7
namespace Stage2Resume

open scoped BigOperators

/-- The R1 premise is the load-bearing source of positivity for every epoch
scale. -/
theorem epochScale_pos {Ma : ℝ} (hMa : 0 < Ma) (s : ℕ) :
    0 < (2 : ℝ) ^ s * Ma :=
  mul_pos (pow_pos (by norm_num) _) hMa

theorem epochRadius_pos {G Ma : ℝ} (hG : 0 < G) (hMa : 0 < Ma)
    (s j : ℕ) :
    0 < (2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma) :=
  div_pos (mul_pos (pow_pos (by norm_num) _) hG) (epochScale_pos hMa s)

theorem epochKappa_pos {eps G Ma : ℝ} (heps : 0 < eps) (hG : 0 < G)
    (hMa : 0 < Ma) (s j : ℕ) :
    0 < (((2 : ℝ) ^ s * Ma) *
      ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) :=
  div_pos (mul_pos (epochScale_pos hMa s) (epochRadius_pos hG hMa s j)) heps

theorem acceptedRadius_pos {G Ma Da : ℝ} (hG : 0 < G) (hMa : 0 < Ma)
    (hDa : Da = G / Ma) : 0 < Da := by
  rw [hDa]
  exact div_pos hG hMa

theorem localCostExponent_le_one {p : ℝ} (_hp : 1 < p) :
    localCostExponent p ≤ 1 := by
  unfold localCostExponent
  split_ifs with hp2
  · norm_num
  · have htwo : 2 < p := lt_of_not_ge hp2
    have hden : 0 < p + 2 := by linarith
    exact (div_le_one hden).2 (by linarith)

theorem localCostExponent_eq_half_of_le_two {p : ℝ} (hp : p ≤ 2) :
    localCostExponent p = 1 / 2 := by
  simp [localCostExponent, hp]

theorem localCostExponent_eq_above {p : ℝ} (hp : 2 < p) :
    localCostExponent p = p / (p + 2) := by
  simp [localCostExponent, not_le_of_gt hp]

/-- The constant bounding the sum of costs along the realized geometric controller path. -/
noncomputable def amortizationConstant (a : ℝ) : ℝ :=
  1 + 4 / (1 - (2 : ℝ) ^ (-a)) ^ (2 : ℕ)

theorem amortizationConstant_pos {a : ℝ} (ha : 0 < a) :
    0 < amortizationConstant a := by
  have hden := V7.Stage2.one_sub_two_neg_rpow_pos ha
  unfold amortizationConstant
  have hq : 0 ≤ 4 / (1 - (2 : ℝ) ^ (-a)) ^ (2 : ℕ) :=
    div_nonneg (by norm_num) (sq_nonneg _)
  linarith

theorem endpointCoefficient_le_constant {a : ℝ} (ha : 0 < a)
    (hale : a ≤ 1) :
    ((2 : ℝ) ^ a / (1 - (2 : ℝ) ^ (-a))) ^ (2 : ℕ) ≤
      amortizationConstant a := by
  have hpowPos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
  have hpowLe : (2 : ℝ) ^ a ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hale
    simpa using this
  have hsq : ((2 : ℝ) ^ a) ^ (2 : ℕ) ≤ 4 := by nlinarith
  have hden := V7.Stage2.one_sub_two_neg_rpow_pos ha
  have hdenSq : 0 < (1 - (2 : ℝ) ^ (-a)) ^ (2 : ℕ) := sq_pos_of_pos hden
  unfold amortizationConstant
  calc
    ((2 : ℝ) ^ a / (1 - (2 : ℝ) ^ (-a))) ^ (2 : ℕ) =
        ((2 : ℝ) ^ a) ^ (2 : ℕ) /
          (1 - (2 : ℝ) ^ (-a)) ^ (2 : ℕ) := by rw [div_pow]
    _ ≤ 4 / (1 - (2 : ℝ) ^ (-a)) ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right hsq hdenSq.le
    _ ≤ 1 + 4 / (1 - (2 : ℝ) ^ (-a)) ^ (2 : ℕ) := by linarith

end Stage2Resume
end V7
