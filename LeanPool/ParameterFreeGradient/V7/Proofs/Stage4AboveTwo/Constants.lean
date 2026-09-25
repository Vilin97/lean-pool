/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwo.Geometry

/-!
Positivity of the constants and scales used by the above-two phases.
-/

@[expose] public section

namespace V7.Stage4AboveTwo

theorem uniformConstant_pos {p : ℝ} (hp : 2 < p) :
    0 < aboveUniformConstant p := by
  unfold aboveUniformConstant
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)

theorem errorPower_gt_one {p : ℝ} (hp : 2 < p) :
    1 < aboveErrorPower p := by
  unfold aboveErrorPower
  rw [lt_div_iff₀ (by linarith : 0 < p - 2)]
  linarith

theorem errorConstant_pos {p : ℝ} (hp : 2 < p) :
    0 < aboveErrorConstant p := by
  unfold aboveErrorConstant
  have hbase : 0 < p * aboveUniformConstant p :=
    mul_pos (by linarith) (uniformConstant_pos hp)
  exact mul_pos (div_pos (by linarith) (mul_pos (by norm_num) (by linarith)))
    (Real.rpow_pos_of_pos hbase _)

theorem budgetConstant_pos {p : ℝ} (hp : 2 < p) :
    0 < aboveBudgetConstant p := by
  unfold aboveBudgetConstant
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (errorConstant_pos hp)

theorem budgetExponent_pos {p : ℝ} (hp : 2 < p) :
    0 < aboveBudgetExponent p := by
  unfold aboveBudgetExponent
  exact div_pos (by linarith) (by linarith)

theorem budgetExponent_lt_one {p : ℝ} (hp : 2 < p) :
    aboveBudgetExponent p < 1 := by
  unfold aboveBudgetExponent
  rw [div_lt_one (by linarith : 0 < p)]
  linarith

theorem errorPower_mul_budgetExponent {p : ℝ} (hp : 2 < p) :
    aboveErrorPower p * aboveBudgetExponent p = 1 := by
  unfold aboveErrorPower aboveBudgetExponent
  field_simp [show p ≠ 0 by linarith, show p - 2 ≠ 0 by linarith]

theorem growthConstant_pos {p : ℝ} (hp : 2 < p) :
    0 < aboveGrowthConstant p := by
  unfold aboveGrowthConstant
  exact Real.rpow_pos_of_pos (mul_pos (by norm_num) (budgetConstant_pos hp)) _

theorem hpConstant_pos {p : ℝ} (hp : 2 < p) :
    0 < aboveHp p := by
  unfold aboveHp
  exact div_pos
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _))
    (mul_pos (mul_pos (by norm_num) (by linarith)) (growthConstant_pos hp))

theorem conjugate_pos {p : ℝ} (hp : 2 < p) :
    0 < conjugateExponent p := lt_trans (by norm_num) <|
      O3.one_lt_conjugateExponent (by linarith)

theorem jpConstant_pos {p : ℝ} (hp : 2 < p) :
    0 < aboveJp p := by
  unfold aboveJp
  exact div_pos
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (conjugate_pos hp) _))
    (growthConstant_pos hp)

theorem gamma_pos {p eta : ℝ} {n : ℕ} (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) : 0 < aboveGamma p eta n := by
  unfold aboveGamma
  apply Real.rpow_pos_of_pos
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact div_pos heta
    (mul_pos (mul_pos (by norm_num) (budgetConstant_pos hp)) hnpos)

end V7.Stage4AboveTwo
