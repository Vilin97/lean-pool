/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualPreviousMaterial

/-! # Iterates Previous Material Scale

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Normalize the previous-material energy without discarding its two
preceding amplitudes. Both contributions retain the squared oscillatory gain. -/
theorem iterate_previous_material_scale_bound (n a b : ℕ)
    {κ D V r L Cs Cv Cc Gc Gp q : ℝ}
    (hκ : 0 < κ) (hD : 0 ≤ D) (hV : 0 ≤ V) (hr : 0 ≤ r)
    (hL : 0 < L) (hCs : 0 ≤ Cs) (hCv : 0 ≤ Cv) (hq : 0 ≤ q)
    (hQ : D * L ^ 2 ≤ Cs * q) (hvel : V * r ≤ Cv * κ * L ^ 2) :
    24 * D ^ 2 / κ *
      (8 * κ ^ 2 * Gc ^ 2 * (((n + 2 + a).factorial : ℝ) * L ^ (n + 2)) ^ 2 +
        512 * κ ^ 2 * Cc ^ 2 * Gp ^ 2 * (((n + 2 + b).factorial : ℝ) * L ^ (n + 2)) ^ 2 +
        544 * V ^ 2 * r ^ 2 * Gc ^ 2 * (((n + 1 + a).factorial : ℝ) * L ^ n) ^ 2) ≤
      Cs ^ 2 * q ^ 2 * κ *
        ((192 + 13056 * Cv ^ 2) * Gc ^ 2 * (((n + 2 + a).factorial : ℝ) * L ^ n) ^ 2 +
          12288 * Cc ^ 2 * Gp ^ 2 * (((n + 2 + b).factorial : ℝ) * L ^ n) ^ 2) := by
  have hQsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hQ
  have hdv : D * (V * r) ≤ Cs * q * Cv * κ := by
    have h₁ := mul_le_mul_of_nonneg_left hvel hD
    have h₂ := mul_le_mul_of_nonneg_right hQ (by positivity : 0 ≤ Cv * κ)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp
    nlinarith only [h₁, h₂]
  have hdvsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hdv
  have hf : ((n + 1 + a).factorial : ℝ) ≤ ((n + 2 + a).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n + 1 + a ≤ n + 2 + a)
  have hw := (sq_le_sq₀ (by positivity) (by positivity)).mpr
    (mul_le_mul_of_nonneg_right hf (by positivity : 0 ≤ L ^ n))
  have h₁ := mul_le_mul_of_nonneg_right hQsq
    (by positivity : 0 ≤ 192 * κ * Gc ^ 2 * (((n + 2 + a).factorial : ℝ) * L ^ n) ^ 2)
  have h₂ := mul_le_mul_of_nonneg_right hQsq
    (by positivity : 0 ≤ 12288 * κ * Cc ^ 2 * Gp ^ 2 * (((n + 2 + b).factorial : ℝ) * L ^ n) ^ 2)
  have h₃ := mul_le_mul_of_nonneg_right hdvsq
    (by positivity : 0 ≤ 13056 * Gc ^ 2 * (((n + 1 + a).factorial : ℝ) * L ^ n) ^ 2 / κ)
  have h₄ := mul_le_mul_of_nonneg_left hw
    (by positivity : 0 ≤ 13056 * Gc ^ 2 * Cs ^ 2 * q ^ 2 * Cv ^ 2 * κ)
  have h₃' : 13056 * D ^ 2 * V ^ 2 * r ^ 2 * Gc ^ 2 *
      (((n + 1 + a).factorial : ℝ) * L ^ n) ^ 2 / κ ≤
      13056 * Cs ^ 2 * q ^ 2 * Cv ^ 2 * κ * Gc ^ 2 *
        (((n + 1 + a).factorial : ℝ) * L ^ n) ^ 2 := by
    convert h₃ using 1 <;> field_simp
  calc
    _ = 192 * κ * Gc ^ 2 * (D * L ^ 2) ^ 2 *
          (((n + 2 + a).factorial : ℝ) * L ^ n) ^ 2 +
        12288 * κ * Cc ^ 2 * Gp ^ 2 * (D * L ^ 2) ^ 2 *
          (((n + 2 + b).factorial : ℝ) * L ^ n) ^ 2 +
        13056 * D ^ 2 * V ^ 2 * r ^ 2 * Gc ^ 2 *
          (((n + 1 + a).factorial : ℝ) * L ^ n) ^ 2 / κ := by
      simp only [pow_add]
      field_simp
      ring
    _ ≤ _ := by nlinarith only [h₁, h₂, h₃', h₄]

end AVenhance.Infra.Section4
