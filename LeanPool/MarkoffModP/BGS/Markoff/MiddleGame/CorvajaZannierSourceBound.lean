/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.UnionBound

/-!
# The source-faithful Corvaja--Zannier numerical specialization

Corvaja--Zannier, Corollary 2, gives a torsion-intersection bound for a curve of
bidegree `(d₁, d₂)` and Euler characteristic `χ`.  This file records its printed
right-hand side and proves that the specialization `(d₁, d₂, χ) = (2, 2, 4)` is
dominated by the coefficient-`48` envelope used by the Markoff middle game.

This is only the numerical specialization.  It does not postulate or prove the geometric
torsion-intersection estimate.
-/

namespace BGS.Markoff

noncomputable section

/-- The numerical right-hand side printed in Corvaja--Zannier, Corollary 2. -/
def corvajaZannierCorollaryTwoNumericalBound
    (p leftOrder rightOrder firstDegree secondDegree : ℕ) (eulerCharacteristic : ℝ) : ℝ :=
  max
    (3 * (2 * ((leftOrder * rightOrder * firstDegree * secondDegree : ℕ) : ℝ) *
      eulerCharacteristic) ^ ((1 : ℝ) / 3))
    (12 * ((leftOrder * rightOrder * firstDegree * secondDegree : ℕ) : ℝ) / p)

private lemma thirtyTwo_rpow_one_third_le_sixteen :
    (32 : ℝ) ^ ((1 : ℝ) / 3) ≤ 16 := by
  have hpow : (4096 : ℝ) ^ ((1 : ℝ) / 3) = 16 := by
    rw [show (4096 : ℝ) = 16 ^ (3 : ℕ) by norm_num]
    convert Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 16)
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rw [← hpow]
  exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)

private lemma sixtyFour_rpow_one_third_eq_four :
    (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
  rw [show (64 : ℝ) = 4 ^ (3 : ℕ) by norm_num]
  convert Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 4)
    (by norm_num : (3 : ℕ) ≠ 0) using 1
  all_goals norm_num

/-- The exact `(2,2)` and Euler-characteristic-four specialization used by the
Markoff middle game is dominated by the source-faithful coefficient `48`. -/
theorem corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_four_le
    (p leftOrder rightOrder : ℕ) :
    corvajaZannierCorollaryTwoNumericalBound p leftOrder rightOrder 2 2 4 ≤
      corvajaZannierTraceUpperBound p leftOrder rightOrder := by
  let x : ℝ := (leftOrder * rightOrder : ℕ)
  have hx : 0 ≤ x := by positivity
  have hroot : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx _
  have hfirst : 3 * (32 * x) ^ ((1 : ℝ) / 3) ≤ 48 * x ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) hx]
    have hproduct :
        0 ≤ (16 - (32 : ℝ) ^ ((1 : ℝ) / 3)) * x ^ ((1 : ℝ) / 3) :=
      mul_nonneg (sub_nonneg.mpr thirtyTwo_rpow_one_third_le_sixteen) hroot
    nlinarith
  unfold corvajaZannierCorollaryTwoNumericalBound corvajaZannierTraceUpperBound
  simp only [corvajaZannierCorollaryTwoSafeCoefficient]
  have hdegrees :
      ((leftOrder * rightOrder * 2 * 2 : ℕ) : ℝ) = 4 * x := by
    simp [x]
    ring
  rw [hdegrees]
  ring_nf
  apply max_le
  · have h := hfirst.trans
      (mul_le_mul_of_nonneg_left
        (le_max_left (x ^ ((1 : ℝ) / 3)) (x / p)) (by norm_num))
    simpa [x, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · have h := mul_le_mul_of_nonneg_left
      (le_max_right (x ^ ((1 : ℝ) / 3)) (x / p)) (by norm_num : (0 : ℝ) ≤ 48)
    simpa [x, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- The degree-only Euler-characteristic bound `χ ≤ 2 d₁ d₂` gives `χ = 8`
at bidegree `(2,2)`.  This slightly weaker but genuinely general specialization
is still dominated by the coefficient-`48` envelope used downstream. -/
theorem corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_eight_le
    (p leftOrder rightOrder : ℕ) :
    corvajaZannierCorollaryTwoNumericalBound p leftOrder rightOrder 2 2 8 ≤
      corvajaZannierTraceUpperBound p leftOrder rightOrder := by
  let x : ℝ := (leftOrder * rightOrder : ℕ)
  have hx : 0 ≤ x := by positivity
  have hroot : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx _
  have hfirst : 3 * (64 * x) ^ ((1 : ℝ) / 3) ≤
      48 * x ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) hx,
      sixtyFour_rpow_one_third_eq_four]
    nlinarith
  unfold corvajaZannierCorollaryTwoNumericalBound corvajaZannierTraceUpperBound
  simp only [corvajaZannierCorollaryTwoSafeCoefficient]
  have hdegrees :
      ((leftOrder * rightOrder * 2 * 2 : ℕ) : ℝ) = 4 * x := by
    simp [x]
    ring
  rw [hdegrees]
  ring_nf
  apply max_le
  · have h := hfirst.trans
      (mul_le_mul_of_nonneg_left
        (le_max_left (x ^ ((1 : ℝ) / 3)) (x / p)) (by norm_num))
    simpa [x, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · have h := mul_le_mul_of_nonneg_left
      (le_max_right (x ^ ((1 : ℝ) / 3)) (x / p)) (by norm_num : (0 : ℝ) ≤ 48)
    simpa [x, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end

end BGS.Markoff
