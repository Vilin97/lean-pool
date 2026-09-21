/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLower.Parameters

namespace V7.Stage5AboveTwoLower.S5ARepair

/-- A parameter choice close enough to one to leave quantitative room for the
finite-dimensional `\ell_{r₀}`-to-`\ell_p` conversion in the Hessian bound.
The frozen carrier only existentially quantifies `theta`; this definition does
not alter any statement. -/
noncomputable def repairTheta (p : ℝ) (d : ℕ) : ℝ :=
  1 + (Stage5AboveTwoLower.kernelR0 p d - 2) /
    (100 * Stage5AboveTwoLower.kernelR0 p d)

lemma one_lt_repairTheta {p : ℝ} {d : ℕ} (hp : 2 < p) (hd : 2 ≤ d) :
    1 < repairTheta p d := by
  unfold repairTheta
  have hr := Stage5AboveTwoLower.two_lt_kernelR0 hp hd
  have hfrac : 0 < (Stage5AboveTwoLower.kernelR0 p d - 2) /
      (100 * Stage5AboveTwoLower.kernelR0 p d) := by positivity
  linarith

lemma repairTheta_lt_101_div_100 {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    repairTheta p d < 101 / 100 := by
  unfold repairTheta
  have hr := Stage5AboveTwoLower.two_lt_kernelR0 hp hd
  have hden : 0 < 100 * Stage5AboveTwoLower.kernelR0 p d := by positivity
  have hfrac : (Stage5AboveTwoLower.kernelR0 p d - 2) /
      (100 * Stage5AboveTwoLower.kernelR0 p d) < 1 / 100 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

lemma two_mul_repairTheta_lt_kernelR0 {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    2 * repairTheta p d < Stage5AboveTwoLower.kernelR0 p d := by
  unfold repairTheta
  have hr := Stage5AboveTwoLower.two_lt_kernelR0 hp hd
  have hden : 0 < 50 * Stage5AboveTwoLower.kernelR0 p d := by positivity
  have hsmall : (Stage5AboveTwoLower.kernelR0 p d - 2) /
      (50 * Stage5AboveTwoLower.kernelR0 p d) <
        Stage5AboveTwoLower.kernelR0 p d - 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos (sub_pos.mpr hr)
      (by nlinarith : 0 < 50 * Stage5AboveTwoLower.kernelR0 p d - 1)]
  have hid :
      2 * (1 + (Stage5AboveTwoLower.kernelR0 p d - 2) /
        (100 * Stage5AboveTwoLower.kernelR0 p d)) =
      2 + (Stage5AboveTwoLower.kernelR0 p d - 2) /
        (50 * Stage5AboveTwoLower.kernelR0 p d) := by
    field_simp [ne_of_gt hr]
    ring
  rw [hid]
  linarith

lemma repair_hessian_coefficient_lt_101_div_25_mul_r0 {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    4 * repairTheta p d * (Stage5AboveTwoLower.kernelR0 p d - 1) <
      (101 / 25) * Stage5AboveTwoLower.kernelR0 p d := by
  have hr := Stage5AboveTwoLower.two_lt_kernelR0 hp hd
  have ht := repairTheta_lt_101_div_100 hp hd
  have hmul := mul_lt_mul_of_pos_right ht (sub_pos.mpr (by linarith :
    1 < Stage5AboveTwoLower.kernelR0 p d))
  nlinarith

lemma repair_parameter_package {p : ℝ} {d : ℕ} (hp : 2 < p) (hd : 2 ≤ d) :
    Stage5AboveTwoLower.kernelR0 p d = min p (3 * Real.log d) ∧
      1 < repairTheta p d ∧
      2 * repairTheta p d < Stage5AboveTwoLower.kernelR0 p d := by
  exact ⟨rfl, one_lt_repairTheta hp hd, two_mul_repairTheta_lt_kernelR0 hp hd⟩

end V7.Stage5AboveTwoLower.S5ARepair
