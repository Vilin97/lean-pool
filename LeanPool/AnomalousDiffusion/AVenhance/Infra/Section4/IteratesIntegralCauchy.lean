/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesOscillatory

/-! Integral Cauchy bounds without dividing by the initial-data norm. -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace AVenhance.Infra.Section4

/-- Cauchy-Schwarz in squared integral form, including zero-energy factors. -/
theorem iterate_integral_cauchy_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  let A := ∫ x, f x ^ 2 ∂μ
  let B := ∫ x, g x ^ 2 ∂μ
  let R := ∫ x, f x * g x ∂μ
  have hA : 0 ≤ A := integral_nonneg (fun _ => sq_nonneg _)
  change R ^ 2 ≤ A * B
  have hp (t : ℝ) : 0 ≤ t ^ 2 * A - 2 * t * R + B := by
    have he : (fun x => t ^ 2 * f x ^ 2 - 2 * t * (f x * g x) + g x ^ 2) =
        (fun x => (t * f x - g x) ^ 2) := by funext x; ring
    have hn : 0 ≤ ∫ x, (t * f x - g x) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
    have hs := integral_add ((hf.const_mul (t ^ 2)).sub (hfg.const_mul (2 * t))) hg
    have ht := integral_sub (hf.const_mul (t ^ 2)) (hfg.const_mul (2 * t))
    dsimp only [Pi.sub_apply, Pi.add_apply] at hs ht
    rw [← he, hs, ht, integral_const_mul, integral_const_mul] at hn
    exact hn
  by_cases ha : A = 0
  · have hr : R = 0 := by
      by_contra hR
      have ht := hp ((B + 1) / (2 * R))
      rw [ha] at ht
      have he : 2 * ((B + 1) / (2 * R)) * R = B + 1 := by field_simp
      rw [he] at ht
      linarith only [ht]
    simp only [ha, hr, zero_pow (by norm_num : 2 ≠ 0), zero_mul, le_refl]
  · have hap : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    have ht := hp (R / A)
    have hm := mul_nonneg (sq_nonneg A) ht
    have he : A ^ 2 * ((R / A) ^ 2 * A - 2 * (R / A) * R + B) =
        A * (A * B - R ^ 2) := by field_simp; ring
    rw [he] at hm
    have hh := (mul_nonneg_iff_of_pos_left hap).mp hm
    exact sub_nonneg.mp hh

/-- Quantitative L2 bounds give a linear pairing bound, including A=0 or B=0. -/
theorem iterate_integral_pairing_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hAf : (∫ x, f x ^ 2 ∂μ) ≤ A ^ 2) (hBg : (∫ x, g x ^ 2 ∂μ) ≤ B ^ 2) :
    |∫ x, f x * g x ∂μ| ≤ A * B := by
  have hs := iterate_integral_cauchy_sq hf hg hfg
  have hm := mul_le_mul hAf hBg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg A)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA hB)).mp
  simpa only [sq_abs, mul_pow] using hs.trans hm

end AVenhance.Infra.Section4
