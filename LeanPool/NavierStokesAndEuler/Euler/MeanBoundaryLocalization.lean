/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanWeakHarmonicScaling

@[expose] public section

/-! The source localization estimate for the constructed nonlocal boundary operator. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerMeanCurlTensor

def boundaryLocalizationC1 : ℝ := 36 * (2 + 4 * weakHarmonicSmallBallConstant)
def boundaryLocalizationC2 : ℝ := 4 * weakHarmonicSmallBallConstant

theorem boundaryLocalizationC1_nonneg : 0 ≤ boundaryLocalizationC1 := by
  unfold boundaryLocalizationC1
  have hc := weakHarmonicSmallBallConstant_nonneg
  positivity

theorem boundaryLocalizationC2_nonneg : 0 ≤ boundaryLocalizationC2 := by
  unfold boundaryLocalizationC2
  exact mul_nonneg (by norm_num) weakHarmonicSmallBallConstant_nonneg

theorem norm_sub_sq_le_twice_L2 (z w : L2) :
    ‖z-w‖^2 ≤ 2*‖z‖^2 + 2*‖w‖^2 := by
  have h := norm_sub_le z w
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hzw := norm_nonneg (z-w)
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

/-- The literal local mass estimate (8), with fixed dimensional constants. -/
theorem boundary_localization (χ : Cutoff) (R : ℝ) (hR : 0 < R) (z : L2)
    (hz : z ∈ solenoidalSpace)
    (hχ : ∀ x ∈ Metric.ball (0 : Space) R, χ.field x = 1)
    (r : ℝ) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4) :
    localL2Energy (Metric.ball (0 : Space) (R*r)) z ≤
      boundaryLocalizationC1 * ‖weakPotential χ z‖^2 +
      boundaryLocalizationC2 * r^3 * ‖z‖^2 := by
  let w := harmonicPart χ z
  have hh : WeakHarmonicOn (Metric.ball (0 : Space) R) (z-w) :=
    weakHarmonicOn_sub_harmonicPart χ _ z hz hχ
  have hloc := weakHarmonic_scaled_smallBall_energy (z-w) R hR hh r hr hrquarter
  have hw : ‖w‖^2 ≤ 36 * ‖weakPotential χ z‖^2 := by
    have H := pow_le_pow_left₀ (norm_nonneg w) (harmonicPart_norm_le χ z) 2
    simpa only [mul_pow, show (6:ℝ)^2 = 36 by norm_num] using H
  have hc := weakHarmonicSmallBallConstant_nonneg
  have hr3 : 0 ≤ r^3 := pow_nonneg hr _
  have hr31 : r^3 ≤ 1 := by
    have H := pow_le_pow_left₀ hr (show r ≤ (1:ℝ) by linarith) 3
    simpa only [one_pow] using H
  have hsplit := norm_sub_sq_le_twice_L2 z w
  calc
    _ ≤ 2 * localL2Energy (Metric.ball (0 : Space) (R*r)) (z-w) + 2 * ‖w‖^2 :=
      localL2Energy_le_of_decomposition _ z w
    _ ≤ 2 * (weakHarmonicSmallBallConstant * r^3 * ‖z-w‖^2) + 2 * ‖w‖^2 := by
      linarith
    _ ≤ 2 * (weakHarmonicSmallBallConstant * r^3 * (2*‖z‖^2+2*‖w‖^2)) +
        2 * ‖w‖^2 := by
      have H := mul_le_mul_of_nonneg_left hsplit (mul_nonneg hc hr3)
      linarith only [H]
    _ = 4 * weakHarmonicSmallBallConstant * r^3 * ‖z‖^2 +
        (2 + 4 * weakHarmonicSmallBallConstant * r^3) * ‖w‖^2 := by ring
    _ ≤ 4 * weakHarmonicSmallBallConstant * r^3 * ‖z‖^2 +
        (2 + 4 * weakHarmonicSmallBallConstant) * ‖w‖^2 := by
      have hfactor : 2 + 4 * weakHarmonicSmallBallConstant * r^3 ≤
          2 + 4 * weakHarmonicSmallBallConstant := by
        have H := mul_le_mul_of_nonneg_left hr31
          (show 0 ≤ 4 * weakHarmonicSmallBallConstant by positivity)
        linarith only [H]
      have H := mul_le_mul_of_nonneg_right hfactor (sq_nonneg ‖w‖)
      linarith only [H]
    _ ≤ 4 * weakHarmonicSmallBallConstant * r^3 * ‖z‖^2 +
        (2 + 4 * weakHarmonicSmallBallConstant) * (36 * ‖weakPotential χ z‖^2) := by
      have H := mul_le_mul_of_nonneg_left hw
        (show 0 ≤ 2 + 4 * weakHarmonicSmallBallConstant by positivity)
      linarith only [H]
    _ = _ := by unfold boundaryLocalizationC1 boundaryLocalizationC2; ring

/-- The same estimate directly in terms of the actual boundary quadratic form. -/
theorem boundary_localization_form (χ : Cutoff) (R : ℝ) (hR : 0 < R) (z : L2)
    (hz : z ∈ solenoidalSpace)
    (hχ : ∀ x ∈ Metric.ball (0 : Space) R, χ.field x = 1)
    (r : ℝ) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4) :
    localL2Energy (Metric.ball (0 : Space) (R*r)) z ≤
      boundaryLocalizationC1 * ⟪boundaryOperator χ z, z⟫_ℝ +
      boundaryLocalizationC2 * r^3 * ‖z‖^2 := by
  rw [boundaryOperator_energy]
  exact boundary_localization χ R hR z hz hχ r hr hrquarter

end EulerMeanHarmonic
