/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanWeakHarmonicInterior
public import LeanPool.NavierStokesAndEuler.Euler.MeanL2Scaling

@[expose] public section

/-! Scale-independent local L² control of weak harmonic fields on ordinary R³. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal

theorem weakScalarHarmonic_pointwise_scaled (f : Space → ℝ) (hf : MemLp f 2 volume)
    (R : ℝ) (hR : 0 < R) (hh : ScalarWeakHarmonicOn (Metric.ball (0 : Space) R) f) :
    ∀ᵐ x ∂volume, x ∈ Metric.closedBall (0 : Space) (R/4) →
      f x ^ 2 ≤ (harmonicQuarterBallConstant * (R^3)⁻¹) * lpNorm f 2 volume ^ 2 := by
  have hs := weakScalarHarmonic_pointwise (fun x => f (R • x))
    (memLp_dilation f hf R hR.ne') (scalarWeakHarmonicOn_dilation f R hR hh)
  have ht := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hR.ne')).ae hs
  filter_upwards [ht] with x hx
  intro hxball
  have hxsmall : R⁻¹ • x ∈ Metric.closedBall (0 : Space) (1/4 : ℝ) := by
    simp only [Metric.mem_closedBall, dist_zero_right] at hxball ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc
      R⁻¹ * ‖x‖ ≤ R⁻¹ * (R/4) := mul_le_mul_of_nonneg_left hxball (inv_nonneg.mpr hR.le)
      _ = 1/4 := by field_simp
  have H := hx hxsmall
  have heval : R • (R⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [heval, lpNorm_dilation_sq f hf R hR] at H
  simpa only [mul_assoc] using H

theorem weakHarmonic_pointwise_scaled (u : L2) (R : ℝ) (hR : 0 < R)
    (hu : WeakHarmonicOn (Metric.ball (0 : Space) R) u) :
    ∀ᵐ x ∂volume, x ∈ Metric.closedBall (0 : Space) (R/4) →
      ‖u x‖^2 ≤ (harmonicQuarterBallConstant * (R^3)⁻¹) * ‖u‖^2 := by
  have H := ae_vector_bound_of_component_bounds (u : Space → Space) (Lp.memLp u)
    (Metric.closedBall (0 : Space) (R/4)) (harmonicQuarterBallConstant * (R^3)⁻¹)
    (fun i => weakScalarHarmonic_pointwise_scaled (fun x => u x i)
      (scalar_component_memLp u (Lp.memLp u) i) R hR
      (scalarWeakHarmonicOn_of_vector_tests _ u hu i))
  simpa only [lpNorm_coe_L2] using H

/-- The radius R of the ambient harmonic ball cancels exactly from the local-energy estimate. -/
theorem weakHarmonic_scaled_smallBall_energy (u : L2) (R : ℝ) (hR : 0 < R)
    (hu : WeakHarmonicOn (Metric.ball (0 : Space) R) u)
    (r : ℝ) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4) :
    localL2Energy (Metric.ball (0 : Space) (R*r)) u ≤
      weakHarmonicSmallBallConstant * r^3 * ‖u‖^2 := by
  have hrr : R*r ≤ R/4 := by nlinarith
  have hb : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Space) (R*r) →
      ‖u x‖^2 ≤ (harmonicQuarterBallConstant * (R^3)⁻¹) * ‖u‖^2 := by
    filter_upwards [weakHarmonic_pointwise_scaled u R hR hu] with x hx
    intro hxball
    exact hx ((Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hrr)) hxball)
  have H := localL2Energy_ball_le_of_ae_bound u
    ((harmonicQuarterBallConstant * (R^3)⁻¹) * ‖u‖^2) (R*r) (mul_nonneg hR.le hr) hb
  have heq : (Real.pi * 4 / 3) * (R*r)^3 *
      ((harmonicQuarterBallConstant * (R^3)⁻¹) * ‖u‖^2) =
      weakHarmonicSmallBallConstant * r^3 * ‖u‖^2 := by
    unfold weakHarmonicSmallBallConstant
    field_simp
  exact H.trans_eq heq

end EulerMeanHarmonic
