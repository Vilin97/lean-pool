/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryLocalization
public import LeanPool.NavierStokesAndEuler.Euler.MeanLocalizedQuadraticBound
public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledCutoff

@[expose] public section

/-! The concrete boundary lower bound used in the mean time-variational solve. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerLiftedPressure
open scoped NNReal

/-- The actual localized boundary operator compensates for the core's negative gradient. -/
theorem mean_boundary_lower_bound (χ : Cutoff) (R : ℝ) (hR : 0 < R)
    (hχ : ∀ x ∈ Metric.ball (0 : Space) R, χ.field x = 1)
    (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
    (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
    (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
    (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
    (hext : ∀ x, x ∉ Metric.ball (0 : Space) (R*r) →
      ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (hcore : ∀ x, x ∈ Metric.ball (0 : Space) (R*r) →
      ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (z : L2) (hz : z ∈ solenoidalSpace) :
    -(Be + boundaryLocalizationC2 * Bc * r^3) * ‖z‖^2 ≤
      ⟪coefficientOperator M hM C hC z, z⟫_ℝ + L * ⟪boundaryOperator χ z, z⟫_ℝ := by
  have hcoeff := localized_coefficient_lower M hM C hC
    (Metric.ball (0 : Space) (R*r)) Metric.isOpen_ball.measurableSet Be Bc hBe hext hcore z
  have hloc := mul_le_mul_of_nonneg_left
    (boundary_localization_form χ R hR z hz hχ r hr hrquarter) hBc
  have hcomp := mul_le_mul_of_nonneg_right hL (boundaryOperator_positive χ z)
  nlinarith only [hcoeff, hloc, hcomp]

/-- The exact cutoff and physical-label core from source (7)–(8). -/
theorem scaled_mean_boundary_lower_bound (ℓ : ℝ) (hℓ : 0 < ℓ)
    (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
    (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
    (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
    (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
    (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (z : L2) (hz : z ∈ solenoidalSpace) :
    -(Be + boundaryLocalizationC2 * Bc * r^3) * ‖z‖^2 ≤
      ⟪coefficientOperator M hM C hC z, z⟫_ℝ +
        L * ⟪boundaryOperator (scaledCutoff ℓ hℓ) z, z⟫_ℝ := by
  apply mean_boundary_lower_bound (scaledCutoff ℓ hℓ) ℓ⁻¹ (inv_pos.mpr hℓ)
    (scaledCutoff_one_on_ball ℓ hℓ) M hM C hC Be Bc L r hBe hBc hL hr hrquarter
    ?_ ?_ z hz
  · intro x hx
    apply hext x
    rw [← physical_ball_eq ℓ r hℓ] at hx
    exact le_of_not_gt hx
  · intro x hx
    apply hcore x
    rw [← physical_ball_eq ℓ r hℓ] at hx
    exact hx

end EulerMeanHarmonic
