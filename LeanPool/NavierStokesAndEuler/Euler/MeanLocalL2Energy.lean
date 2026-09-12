/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicSmallBall
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarSobolev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Local energies of actual L² fields, including the decomposition estimate. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal

/-- Local L² energy, given by `∫ x in s, ‖u x‖ ^ 2`. -/
def localL2Energy (s : Set Space) (u : L2) : ℝ := ∫ x in s, ‖u x‖ ^ 2

theorem lpNorm_coe_L2 (u : L2) : lpNorm (u : Space → Space) 2 volume = ‖u‖ := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.memLp u).aestronglyMeasurable]

theorem integrable_norm_sq_L2 (u : L2) : Integrable (fun x => ‖u x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq (Lp.memLp u).norm.aestronglyMeasurable).1 (Lp.memLp u).norm

theorem integral_norm_sq_L2 (u : L2) : (∫ x, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
  rw [← lpNorm_sq_eq_integral_norm_sq _ (Lp.memLp u), lpNorm_coe_L2]

theorem localL2Energy_nonneg (s : Set Space) (u : L2) : 0 ≤ localL2Energy s u :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem localL2Energy_le (s : Set Space) (u : L2) : localL2Energy s u ≤ ‖u‖ ^ 2 := by
  rw [← integral_norm_sq_L2]
  exact setIntegral_le_integral (integrable_norm_sq_L2 u)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

theorem norm_add_sq_le_twice (a b : Space) :
    ‖a+b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a+b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

theorem localL2Energy_add_le (s : Set Space) (u v : L2) :
    localL2Energy s (u+v) ≤ 2 * localL2Energy s u + 2 * localL2Energy s v := by
  have hu := (integrable_norm_sq_L2 u).integrableOn (s := s)
  have hv := (integrable_norm_sq_L2 v).integrableOn (s := s)
  calc
    _ ≤ ∫ x in s, 2 * ‖u x‖^2 + 2 * ‖v x‖^2 := by
      apply integral_mono_ae (integrable_norm_sq_L2 (u+v)).integrableOn
        ((hu.const_mul 2).add (hv.const_mul 2))
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_add u v)] with x hx
      rw [hx]
      exact norm_add_sq_le_twice (u x) (v x)
    _ = _ := by
      rw [integral_add (hu.const_mul 2) (hv.const_mul 2), integral_const_mul, integral_const_mul]
      rfl

theorem localL2Energy_le_of_decomposition (s : Set Space) (z w : L2) :
    localL2Energy s z ≤ 2 * localL2Energy s (z-w) + 2 * ‖w‖^2 := by
  have H := localL2Energy_add_le s (z-w) w
  rw [sub_add_cancel] at H
  have hw := localL2Energy_le s w
  linarith

theorem localL2Energy_ball_le_of_ae_bound (u : L2) (C r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Space) r → ‖u x‖ ^ 2 ≤ C) :
    localL2Energy (Metric.ball (0 : Space) r) u ≤ (Real.pi * 4 / 3) * r^3 * C := by
  calc
    _ ≤ ∫ _x in Metric.ball (0 : Space) r, C := by
      apply integral_mono_ae (integrable_norm_sq_L2 u).integrableOn
        (integrableOn_const (measure_ball_lt_top.ne))
      exact (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 hbound
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul]
      change (volume (Metric.ball (0 : Space) r)).toReal * C = _
      rw [volume_ball_toReal r hr]
      ring

end EulerMeanHarmonic
