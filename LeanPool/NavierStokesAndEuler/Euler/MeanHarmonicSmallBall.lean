/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicInterior
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-! A dimensional r³ localization estimate, derived from the interior bound. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit
open scoped ContDiff

def harmonicSmallBallConstant : ℝ :=
  (Real.pi * 4 / 3) * harmonicInteriorConstant ^ 2

theorem harmonicSmallBallConstant_nonneg : 0 ≤ harmonicSmallBallConstant := by
  unfold harmonicSmallBallConstant
  positivity

theorem volume_ball_toReal (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : Space) r)).toReal = r ^ 3 * (Real.pi * 4 / 3) := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]

/-- The mass on a ball of radius r is bounded by r³ times the global L² mass. -/
theorem harmonic_smallBall_energy (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    (∫ x in Metric.ball (0 : Space) r, h x ^ 2) ≤
      harmonicSmallBallConstant * r ^ 3 * lpNorm h 2 volume ^ 2 := by
  have hi : Integrable (fun x => h x ^ 2) volume :=
    (memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).1 hLp
  have hbound : ∀ x ∈ Metric.ball (0 : Space) r,
      h x ^ 2 ≤ (harmonicInteriorConstant * lpNorm h 2 volume) ^ 2 := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : Space) (1/2 : ℝ) :=
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrhalf)) hx
    have H := harmonic_pointwise_halfBall h hh hLp hharmonic x hx'
    calc
      h x ^ 2 = |h x| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) H 2
  calc
    _ ≤ ∫ _x in Metric.ball (0 : Space) r,
        (harmonicInteriorConstant * lpNorm h 2 volume) ^ 2 := by
      apply setIntegral_mono_on hi.integrableOn (integrableOn_const (measure_ball_lt_top.ne))
        Metric.isOpen_ball.measurableSet hbound
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul]
      change (volume (Metric.ball (0 : Space) r)).toReal * _ = _
      rw [volume_ball_toReal r hr]
      unfold harmonicSmallBallConstant
      ring

end EulerMeanHarmonic
