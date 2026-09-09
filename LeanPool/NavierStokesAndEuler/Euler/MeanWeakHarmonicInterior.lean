/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDecomposition
public import LeanPool.NavierStokesAndEuler.Euler.MeanLocalL2Energy
public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicScaling
public import LeanPool.NavierStokesAndEuler.Euler.MeanMollifierLimit
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicComponents
import LeanPool.NavierStokesAndEuler.Euler.MeanMollificationHarmonic

/-! The proved harmonic interior bound for the actual weak L² solution. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal

/-- A scalar distributionally harmonic L² field has a uniform a.e. interior bound. -/
theorem weakScalarHarmonic_pointwise (f : Space → ℝ) (hf : MemLp f 2 volume)
    (hh : ScalarWeakHarmonicOn (Metric.ball (0 : Space) 1) f) :
    ∀ᵐ x ∂volume, x ∈ Metric.closedBall (0 : Space) (1/4 : ℝ) →
      f x ^ 2 ≤ harmonicQuarterBallConstant * lpNorm f 2 volume ^ 2 := by
  apply ae_bound_of_scalarMollification_bound f hf
  intro n x hx
  calc
    _ ≤ harmonicQuarterBallConstant *
        lpNorm (scalarMollification (interiorMollifier n) f) 2 volume ^ 2 :=
      harmonic_pointwise_quarterBall_sq _
        (scalarMollification_smooth (interiorMollifier n) f hf)
        (scalarMollification_memLp (interiorMollifier n) f hf)
        (interiorMollifier_harmonic f hf hh n) x hx
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (scalarMollification_energy_le (interiorMollifier n) f hf)
      harmonicQuarterBallConstant_nonneg

/-- The same bound for an actual vector L² field, without assuming a smooth representative. -/
theorem weakHarmonic_pointwise (u : L2) (hu : WeakHarmonicOn (Metric.ball (0 : Space) 1) u) :
    ∀ᵐ x ∂volume, x ∈ Metric.closedBall (0 : Space) (1/4 : ℝ) →
      ‖u x‖ ^ 2 ≤ harmonicQuarterBallConstant * ‖u‖ ^ 2 := by
  have H := ae_vector_bound_of_component_bounds (u : Space → Space) (Lp.memLp u)
    (Metric.closedBall (0 : Space) (1/4 : ℝ)) harmonicQuarterBallConstant
    (fun i => weakScalarHarmonic_pointwise (fun x => u x i)
      (scalar_component_memLp u (Lp.memLp u) i)
      (scalarWeakHarmonicOn_of_vector_tests _ u hu i))
  simpa only [lpNorm_coe_L2] using H

/-- Weak harmonic small ball constant, given by `(Real.pi * 4 / 3) *
harmonicQuarterBallConstant`. -/
def weakHarmonicSmallBallConstant : ℝ := (Real.pi * 4 / 3) * harmonicQuarterBallConstant

theorem weakHarmonicSmallBallConstant_nonneg : 0 ≤ weakHarmonicSmallBallConstant := by
  unfold weakHarmonicSmallBallConstant
  exact mul_nonneg (by positivity) harmonicQuarterBallConstant_nonneg

/-- Source localization for weakly harmonic fields: the radius enters with the genuine power 3. -/
theorem weakHarmonic_smallBall_energy (u : L2)
    (hu : WeakHarmonicOn (Metric.ball (0 : Space) 1) u)
    (r : ℝ) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4) :
    localL2Energy (Metric.ball (0 : Space) r) u ≤
      weakHarmonicSmallBallConstant * r^3 * ‖u‖^2 := by
  have hb : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Space) r →
      ‖u x‖^2 ≤ harmonicQuarterBallConstant * ‖u‖^2 := by
    filter_upwards [weakHarmonic_pointwise u hu] with x hx
    intro hxball
    exact hx ((Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hrquarter)) hxball)
  have H := localL2Energy_ball_le_of_ae_bound u
    (harmonicQuarterBallConstant * ‖u‖^2) r hr hb
  unfold weakHarmonicSmallBallConstant
  convert H using 1
  ring

end EulerMeanHarmonic
