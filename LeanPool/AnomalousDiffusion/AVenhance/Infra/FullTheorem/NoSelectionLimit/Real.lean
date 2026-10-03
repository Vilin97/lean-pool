/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Abstract real lemmas for the no-selection limit argument

* the two-diffusivity coefficient `|a-b|/(2√(ab))` is controlled by `|log(a/b)|`;
* closeness of two logarithms to the same value;
* interpolation `min(A, H h^μ) ≤ √(AH) h^{μ/2}`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem

/-- `|a-b|/(2√(ab)) ≤ 2 |log (a/b)|` when `|log (a/b)| ≤ 1`. -/
theorem diffusivity_ratio_le {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : |Real.log (a / b)| ≤ d) (hd1 : d ≤ 1) :
    |a - b| / (2 * Real.sqrt (a * b)) ≤ 2 * d := by
  set r := a / b with hr
  have hr0 : 0 < r := div_pos ha hb
  have hu1 : |Real.log r| ≤ 1 := hd.trans hd1
  have hexp : |r - 1| ≤ 2 * d := by
    have h := Real.abs_exp_sub_one_le hu1
    rw [Real.exp_log hr0] at h
    linarith
  have hr4 : (1 / 4 : ℝ) ≤ r := by
    have h1 : -1 ≤ Real.log r := (abs_le.1 hu1).1
    have h2 : Real.exp (-1) ≤ r := by
      rw [← Real.exp_log hr0]; exact Real.exp_le_exp.2 h1
    have h3 : Real.exp 1 < 4 := by
      have := Real.exp_one_lt_d9; linarith
    have h4 : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg]
      exact one_div_le_one_div_of_le (Real.exp_pos 1) h3.le |>.trans_eq' (by simp) |>.trans_eq (by
          simp)
    exact h4.trans h2
  have hsq2 : (1 / 2 : ℝ) ≤ Real.sqrt r := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hr4
  have hab : a * b = b ^ 2 * r := by rw [hr]; field_simp
  have hs : Real.sqrt (a * b) = b * Real.sqrt r := by
    rw [hab, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  have hdiff : |a - b| = b * |r - 1| := by
    have : a - b = b * (r - 1) := by rw [hr]; field_simp
    rw [this, abs_mul, abs_of_pos hb]
  rw [hs, hdiff, div_le_iff₀ (by positivity)]
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  calc b * |r - 1| ≤ b * (2 * d) := by gcongr
    _ = 2 * d * b * 1 := by ring
    _ ≤ 2 * d * b * (2 * Real.sqrt r) := by gcongr; linarith
    _ = _ := by ring

/-- Two logarithms close to the same number `s`: the ratio has small logarithm. -/
theorem log_ratio_le {a b D s e₁ e₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (h1 : |Real.log (a / D) - s| ≤ e₁) (h2 : |Real.log (b / D) - s| ≤ e₂) :
    |Real.log (a / b)| ≤ e₁ + e₂ := by
  have e : Real.log (a / b) = (Real.log (a / D) - s) - (Real.log (b / D) - s) := by
    rw [Real.log_div ha.ne' hb.ne', Real.log_div ha.ne' hD.ne', Real.log_div hb.ne' hD.ne']
    ring
  rw [e]
  calc _ ≤ |Real.log (a / D) - s| + |Real.log (b / D) - s| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-- `min(A, H h^μ) ≤ √(A H) h^{μ/2}`. -/
theorem min_interp {x A H h μ : ℝ} (hh : 0 ≤ h) (hx0 : 0 ≤ x) (h1 : x ≤ A)
    (h2 : x ≤ H * h ^ μ) : x ≤ Real.sqrt (A * H) * h ^ (μ / 2) := by
  have hA : 0 ≤ A := hx0.trans h1
  have hhm : 0 ≤ h ^ μ := Real.rpow_nonneg hh _
  have hH : 0 ≤ H * h ^ μ := hx0.trans h2
  have hx : x ≤ Real.sqrt (A * (H * h ^ μ)) := by
    apply Real.le_sqrt_of_sq_le
    calc x ^ 2 = x * x := sq x
      _ ≤ A * (H * h ^ μ) := mul_le_mul h1 h2 hx0 hA
  have e : Real.sqrt (A * (H * h ^ μ)) = Real.sqrt (A * H) * h ^ (μ / 2) := by
    have hAH : 0 ≤ A * H ∨ H * h ^ μ = 0 := by
      by_cases h0 : h ^ μ = 0
      · right; simp [h0]
      · left
        have : 0 < h ^ μ := lt_of_le_of_ne hhm (Ne.symm h0)
        exact mul_nonneg hA (nonneg_of_mul_nonneg_left hH this)
    rcases hAH with hAH | hz
    · rw [← mul_assoc, Real.sqrt_mul hAH, Real.sqrt_eq_rpow (h ^ μ), ← Real.rpow_mul hh]
      congr 2; ring
    · rw [hz]
      have : h ^ μ = 0 ∨ H = 0 := by
        rcases mul_eq_zero.1 hz with h0 | h0
        · right; exact h0
        · left; exact h0
      rcases this with h0 | h0
      · have : h ^ (μ / 2) = 0 := by
          have hh0 : h = 0 := by
            by_contra hne
            exact (Real.rpow_pos_of_pos (lt_of_le_of_ne hh (Ne.symm hne)) μ).ne' h0
          rw [hh0]
          have hμ : μ / 2 ≠ 0 := by
            intro hz2
            have : μ = 0 := by linarith
            rw [hh0, this] at h0
            simp at h0
          exact Real.zero_rpow hμ
        rw [this]; simp
      · rw [h0]; simp
  rw [← e]; exact hx

end AVenhance.Infra.FullTheorem
