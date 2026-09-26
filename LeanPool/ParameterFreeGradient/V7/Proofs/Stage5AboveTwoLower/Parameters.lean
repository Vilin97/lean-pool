/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.LowerBoundStatements
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Explicit exponents and dimension-dependent Hessian constants for the smoothing kernel.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLower

/-- The kernel coordinate exponent, capped by three times the logarithm of the dimension. -/
noncomputable def kernelR0 (p : ℝ) (d : ℕ) : ℝ :=
  min p (3 * Real.log d)

/-- The kernel power parameter chosen strictly between one and half the coordinate exponent. -/
noncomputable def kernelTheta (p : ℝ) (d : ℕ) : ℝ :=
  1 + (kernelR0 p d - 2) / (4 * kernelR0 p d)

lemma two_lt_three_mul_log_nat {d : ℕ} (hd : 2 ≤ d) :
    (2 : ℝ) < 3 * Real.log d := by
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hd_real
  have hlog : Real.log 2 ≤ Real.log d := Real.strictMonoOn_log.monotoneOn
    (by norm_num) hd_pos hd_real
  have hlog_two : (2 : ℝ) < 3 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  nlinarith

lemma two_lt_kernelR0 {p : ℝ} {d : ℕ} (hp : 2 < p) (hd : 2 ≤ d) :
    2 < kernelR0 p d := by
  rw [kernelR0, lt_min_iff]
  exact ⟨hp, two_lt_three_mul_log_nat hd⟩

lemma one_lt_kernelTheta {p : ℝ} {d : ℕ} (hp : 2 < p) (hd : 2 ≤ d) :
    1 < kernelTheta p d := by
  unfold kernelTheta
  have hr0 := two_lt_kernelR0 hp hd
  have hfrac : 0 < (kernelR0 p d - 2) / (4 * kernelR0 p d) := by
    positivity
  linarith

lemma two_mul_kernelTheta_lt_kernelR0 {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    2 * kernelTheta p d < kernelR0 p d := by
  unfold kernelTheta
  have hr0 := two_lt_kernelR0 hp hd
  have hden : 0 < 2 * kernelR0 p d := by positivity
  have hscale : 1 < 2 * kernelR0 p d := by linarith
  have hgap : 0 < kernelR0 p d - 2 := by linarith
  have hfrac : (kernelR0 p d - 2) / (2 * kernelR0 p d) <
      kernelR0 p d - 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos hgap (sub_pos.mpr hscale)]
  have hid :
      2 * (1 + (kernelR0 p d - 2) / (4 * kernelR0 p d)) =
        2 + (kernelR0 p d - 2) / (2 * kernelR0 p d) := by
    field_simp [ne_of_gt (two_lt_kernelR0 hp hd)]
    ring
  rw [hid]
  linarith

lemma kernelTheta_lt_five_four {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    kernelTheta p d < 5 / 4 := by
  unfold kernelTheta
  have hr0 := two_lt_kernelR0 hp hd
  have hden : 0 < 4 * kernelR0 p d := by positivity
  have hfrac : (kernelR0 p d - 2) / (4 * kernelR0 p d) < 1 / 4 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

lemma kernel_hessian_coefficient_lt_five_mul_r0 {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    4 * kernelTheta p d * (kernelR0 p d - 1) < 5 * kernelR0 p d := by
  have hr0 := two_lt_kernelR0 hp hd
  have htheta := kernelTheta_lt_five_four hp hd
  have hmul := mul_lt_mul_of_pos_right htheta (sub_pos.mpr (by linarith : 1 < kernelR0 p d))
  nlinarith

lemma kernel_hessian_coefficient_explicit_bound {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    4 * kernelTheta p d * (kernelR0 p d - 1) ≤
      (if p ≤ 3 * Real.log d then 5 * p
       else 15 * Real.exp (2 / 3) * Real.log d) := by
  have hcoeff := kernel_hessian_coefficient_lt_five_mul_r0 hp hd
  by_cases hregime : p ≤ 3 * Real.log d
  · rw [ite_eq_left hregime]
    rw [kernelR0, min_eq_left hregime] at hcoeff
    rw [kernelR0, min_eq_left hregime]
    exact hcoeff.le
  · rw [ite_eq_right hregime]
    have hr0 : kernelR0 p d = 3 * Real.log d := by
      rw [kernelR0, min_eq_right (le_of_not_ge hregime)]
    rw [hr0] at hcoeff
    rw [hr0]
    have hlog : 0 ≤ Real.log d := by
      exact Real.log_nonneg (by exact_mod_cast hd.trans' (by decide : 1 ≤ 2))
    have hexp : 1 ≤ Real.exp (2 / 3 : ℝ) := Real.one_le_exp (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_right hexp hlog
    nlinarith

lemma kernel_hessian_coefficient_universal_bound {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    4 * kernelTheta p d * (kernelR0 p d - 1) ≤
      15 * min p (Real.log d) := by
  have hcoeff := kernel_hessian_coefficient_lt_five_mul_r0 hp hd
  by_cases h : p ≤ Real.log d
  · have hr0_le : kernelR0 p d ≤ p := min_le_left _ _
    rw [min_eq_left h]
    nlinarith
  · have hr0_le : kernelR0 p d ≤ 3 * Real.log d := min_le_right _ _
    rw [min_eq_right (le_of_not_ge h)]
    nlinarith

lemma kernel_parameter_package {p : ℝ} {d : ℕ} (hp : 2 < p) (hd : 2 ≤ d) :
    kernelR0 p d = min p (3 * Real.log d) ∧
      1 < kernelTheta p d ∧
      2 * kernelTheta p d < kernelR0 p d := by
  exact ⟨rfl, one_lt_kernelTheta hp hd, two_mul_kernelTheta_lt_kernelR0 hp hd⟩

end V7.Stage5AboveTwoLower
