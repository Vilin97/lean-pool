/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicInteriorEnergy
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicCutoffEnergy
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarProductDerivatives
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarSobolev
import Mathlib.Algebra.Order.Star.Real

/-! The actual second-derivative estimate for the localized harmonic function. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff

theorem localized_second_pointwise (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (i : Fin 3) (x : Space) :
    partialDerivative (partialDerivative (innerCutoff * h) i) i x ^ 2 ≤
      3 * (innerSecondBound ^ 2 * h x ^ 2 +
        4 * innerDerivativeBound ^ 2 * (outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) +
        middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2) := by
  have hη₂ : partialDerivative (partialDerivative innerCutoff i) i x ^ 2 ≤
      innerSecondBound ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (abs_secondPartial_le_derivativeBound innerCutoff inner_compact inner_smooth i x) 2
    simpa only [sq_abs, innerSecondBound] using h
  have hη₁ : partialDerivative innerCutoff i x ^ 2 ≤
      innerDerivativeBound ^ 2 * outerCutoff x ^ 2 :=
    (partialDerivative_sq_le_gradient_sq innerCutoff i x).trans
      (cutoff_gradient_majorant innerCutoff outerCutoff innerDerivativeBound
        (norm_gradient_le_derivativeBound innerCutoff inner_compact inner_smooth)
        (fun _ hx => outer_one_on_inner_support hx) x)
  have hη₀ : innerCutoff x ^ 2 ≤ middleCutoff x ^ 2 :=
    cutoff_square_majorant innerCutoff middleCutoff abs_inner_le_one
      (fun _ hx => middle_one_on_inner_support hx) x
  have ha : (h x * partialDerivative (partialDerivative innerCutoff i) i x) ^ 2 ≤
      innerSecondBound ^ 2 * h x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hη₂ (sq_nonneg (h x))]
  have hb : (2 * partialDerivative innerCutoff i x * partialDerivative h i x) ^ 2 ≤
      4 * innerDerivativeBound ^ 2 * (outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) := by
    have H := mul_le_mul hη₁ (partialDerivative_sq_le_gradient_sq h i x)
      (sq_nonneg (partialDerivative h i x)) (by positivity)
    nlinarith
  have hc : (innerCutoff x * partialDerivative (partialDerivative h i) i x) ^ 2 ≤
      middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2 := by
    have H := mul_le_mul hη₀ (partialDerivative_sq_le_gradient_sq (partialDerivative h i) i x)
      (sq_nonneg _) (sq_nonneg _)
    nlinarith
  rw [secondPartial_mul innerCutoff h inner_smooth hh i x]
  have H := sq_add_three_le
    (h x * partialDerivative (partialDerivative innerCutoff i) i x)
    (2 * partialDerivative innerCutoff i x * partialDerivative h i x)
    (innerCutoff x * partialDerivative (partialDerivative h i) i x)
  nlinarith

/-- Interior second energy constant, constructed using `3`. -/
def interiorSecondEnergyConstant : ℝ :=
  3 * (innerSecondBound ^ 2 + 16 * innerDerivativeBound ^ 2 * outerDerivativeBound ^ 2 +
    16 * middleDerivativeBound ^ 2 * outerDerivativeBound ^ 2)

theorem interiorSecondEnergyConstant_nonneg : 0 ≤ interiorSecondEnergyConstant := by
  unfold interiorSecondEnergyConstant
  positivity

theorem localized_second_memLp (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (i : Fin 3) :
    MemLp (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume := by
  have hc : HasCompactSupport (innerCutoff * h) := inner_compact.mul_right (f' := h)
  have hc₁ : HasCompactSupport (partialDerivative (innerCutoff * h) i) :=
    hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hc₂ : HasCompactSupport (partialDerivative (partialDerivative (innerCutoff * h) i) i) :=
    hc₁.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  exact (contDiff_partialDerivative _
    (contDiff_partialDerivative _ (inner_smooth.mul hh) i) i).continuous.memLp_of_hasCompactSupport
        hc₂

theorem localized_second_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    (lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume) ^ 2 ≤
      interiorSecondEnergyConstant * (lpNorm h 2 volume) ^ 2 := by
  have hL := localized_second_memLp h hh i
  have hiL := (memLp_two_iff_integrable_sq hL.aestronglyMeasurable).1 hL
  have hi₀ := (memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).1 hLp
  have hi₁ := integrable_weighted_gradient_square outerCutoff h outer_compact
      outer_smooth.continuous hh
  have hi₂ := integrable_weighted_gradient_square middleCutoff (partialDerivative h i)
    middle_compact middle_smooth.continuous (contDiff_partialDerivative h hh i)
  have hiA := hi₀.const_mul (innerSecondBound ^ 2)
  have hiB := hi₁.const_mul (4 * innerDerivativeBound ^ 2)
  have hiAB : Integrable (fun x => innerSecondBound ^ 2 * h x ^ 2 +
      4 * innerDerivativeBound ^ 2 * (outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2)) := hiA.add hiB
  have H := integral_mono hiL ((hiAB.add hi₂).const_mul 3)
    (fun x => localized_second_pointwise h hh i x)
  simp only [Pi.add_apply] at H
  rw [integral_const_mul, integral_add hiAB hi₂, integral_add hiA hiB,
    integral_const_mul, integral_const_mul, ← lpNorm_sq_eq_integral_sq h hLp] at H
  rw [lpNorm_sq_eq_integral_sq _ hL]
  calc
    _ ≤ 3 * (innerSecondBound ^ 2 * (lpNorm h 2 volume) ^ 2 +
        4 * innerDerivativeBound ^ 2 *
          (∫ x, outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) +
        ∫ x, middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2) := H
    _ ≤ 3 * (innerSecondBound ^ 2 * (lpNorm h 2 volume) ^ 2 +
        4 * innerDerivativeBound ^ 2 *
          (4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2) +
        16 * middleDerivativeBound ^ 2 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2) := by
      gcongr
      · exact outer_gradient_energy_le h hh hLp hharmonic
      · exact middle_second_energy_le h hh hLp hharmonic i
    _ = _ := by unfold interiorSecondEnergyConstant; ring

end EulerMeanHarmonic
