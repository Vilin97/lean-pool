/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamBudgetKernel

/-! # Iterates Stream Budget Normalized

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Scalar diffusive normalization of a quadratic stream coefficient. -/
theorem iterate_stream_quadratic_normalization {κ u N A : ℝ} (hκ : 0 < κ) :
    u * (N * A / Real.sqrt κ) ^ 2 = (u / κ) * N ^ 2 * A ^ 2 := by
  rw [div_pow, Real.sq_sqrt hκ.le]
  ring

/-- Scalar diffusive normalization of the linear drift convolution. -/
theorem iterate_stream_linear_normalization {κ c N Aprev A : ℝ} (hκ : 0 < κ) :
    c * (N * Aprev / Real.sqrt κ) * (N * A / Real.sqrt κ) =
      (c / κ) * N ^ 2 * Aprev * A := by
  calc
    _ = c * (N ^ 2 * Aprev * A) / (Real.sqrt κ) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hκ.le]; ring

/-- Both geometric kernels in the actual stream budget have their printed
normalized gains. No division by the initial-data norm occurs. -/
theorem iterate_stream_budget_normalized (n : ℕ)
    {κ u v c N Aprev A W C F ρ : ℝ}
    (hκ : 0 < κ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : 0 ≤ c)
    (hAp : 0 ≤ Aprev) (hA : 0 ≤ A)
    (huF : u / κ ≤ C / F ^ 2) (hvF : v / κ ≤ C / F ^ 4)
    (hcρ : c / κ ≤ C * ρ) :
    iterateStreamEnergyBudget n
      (u * (N * A / Real.sqrt κ) ^ 2)
      (v * (N * A / Real.sqrt κ) ^ 2)
      (c * (N * Aprev / Real.sqrt κ) * (N * A / Real.sqrt κ)) W (fun _ => 1) ≤
      N ^ 2 * ((C / F ^ 2 + 2 * (C / F ^ 4)) * A ^ 2 +
        2 * C * ρ * Aprev * A) * W ^ 2 := by
  have hcprod : 0 ≤ c * (N * Aprev / Real.sqrt κ) * (N * A / Real.sqrt κ) := by
    rw [iterate_stream_linear_normalization hκ]
    positivity
  have hb := iterate_stream_budget_unit_profile n (mul_nonneg hu (sq_nonneg (N * A / Real.sqrt κ)))
    (mul_nonneg hv (sq_nonneg (N * A / Real.sqrt κ))) hcprod (W := W)
  rw [iterate_stream_quadratic_normalization hκ,
    iterate_stream_quadratic_normalization hκ, iterate_stream_linear_normalization hκ] at hb
  have h0 := mul_le_mul_of_nonneg_right huF (mul_nonneg (sq_nonneg N) (sq_nonneg A))
  have h1 := mul_le_mul_of_nonneg_right hvF (mul_nonneg (sq_nonneg N) (sq_nonneg A))
  have h2 := mul_le_mul_of_nonneg_right hcρ
    (mul_nonneg (mul_nonneg (sq_nonneg N) hAp) hA)
  have hm := mul_le_mul_of_nonneg_right (add_le_add (add_le_add h0
    (mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 by norm_num)))
    (mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 by norm_num))) (sq_nonneg W)
  rw [iterate_stream_quadratic_normalization hκ,
    iterate_stream_quadratic_normalization hκ, iterate_stream_linear_normalization hκ]
  apply hb.trans
  convert hm using 1 <;> ring

end AVenhance.Infra.Section4
