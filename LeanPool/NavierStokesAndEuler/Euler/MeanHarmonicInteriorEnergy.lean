/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanInteriorCutoffs

@[expose] public section

/-! Two local energy steps for smooth harmonic functions on the unit ball. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff

def outerDerivativeBound : ℝ := derivativeBound outerCutoff outer_compact outer_smooth 1
def middleDerivativeBound : ℝ := derivativeBound middleCutoff middle_compact middle_smooth 1
def innerDerivativeBound : ℝ := derivativeBound innerCutoff inner_compact inner_smooth 1
def innerSecondBound : ℝ := derivativeBound innerCutoff inner_compact inner_smooth 2

theorem outer_bound_nonneg : 0 ≤ outerDerivativeBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)
theorem middle_bound_nonneg : 0 ≤ middleDerivativeBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)
theorem inner_bound_nonneg : 0 ≤ innerDerivativeBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)
theorem inner_second_nonneg : 0 ≤ innerSecondBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)

theorem outer_gradient_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0) :
    (∫ x, outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) ≤
      4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2 := by
  have hi : Integrable (fun x => (1 : ℝ) ^ 2 * h x ^ 2) := by
    simpa only [one_pow, one_mul] using (memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).1 hLp
  have hb (x : Space) : ‖gradient outerCutoff x‖ ^ 2 ≤
      outerDerivativeBound ^ 2 * (1 : ℝ) ^ 2 := by
    simpa only [one_pow, mul_one, outerDerivativeBound] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_gradient_le_derivativeBound outerCutoff outer_compact outer_smooth x) 2
  have H := caccioppoli_weighted_bound outerCutoff (fun _ => 1) h outerDerivativeBound
    outer_compact outer_smooth hh
    (fun x hx => hharmonic x (outer_support_unitBall hx)) hi hb
  simpa only [one_pow, one_mul, ← lpNorm_sq_eq_integral_sq h hLp] using H

theorem outer_partial_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    (∫ x, outerCutoff x ^ 2 * partialDerivative h i x ^ 2) ≤
      4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2 := by
  have hcomp : (∫ x, outerCutoff x ^ 2 * partialDerivative h i x ^ 2) ≤
      ∫ x, outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2 :=
    integral_mono
      (integrable_weighted_square _ _ outer_compact outer_smooth.continuous
        (contDiff_partialDerivative h hh i).continuous)
      (integrable_weighted_gradient_square _ _ outer_compact outer_smooth.continuous hh)
      (fun x => mul_le_mul_of_nonneg_left (partialDerivative_sq_le_gradient_sq h i x)
        (sq_nonneg (outerCutoff x)))
  exact hcomp.trans (outer_gradient_energy_le h hh hLp hharmonic)

theorem middle_second_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    (∫ x, middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2) ≤
      16 * middleDerivativeBound ^ 2 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2 := by
  have hhi := contDiff_partialDerivative h hh i
  have H := caccioppoli_weighted_bound middleCutoff outerCutoff (partialDerivative h i)
    middleDerivativeBound middle_compact middle_smooth hhi
    (fun x hx => partialDerivative_harmonic_on h hh _ Metric.isOpen_ball hharmonic i x
      (middle_support_unitBall hx))
    (integrable_weighted_square _ _ outer_compact outer_smooth.continuous hhi.continuous)
    (cutoff_gradient_majorant middleCutoff outerCutoff middleDerivativeBound
      (norm_gradient_le_derivativeBound _ middle_compact middle_smooth)
      (fun _ hx => outer_one_on_middle_support hx))
  calc
    _ ≤ 4 * middleDerivativeBound ^ 2 *
        (∫ x, outerCutoff x ^ 2 * partialDerivative h i x ^ 2) := H
    _ ≤ 4 * middleDerivativeBound ^ 2 *
        (4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2) :=
      mul_le_mul_of_nonneg_left (outer_partial_energy_le h hh hLp hharmonic i) (by positivity)
    _ = _ := by ring

end EulerMeanHarmonic
