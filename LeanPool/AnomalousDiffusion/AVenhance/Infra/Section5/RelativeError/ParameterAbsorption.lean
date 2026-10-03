/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.Combination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!# RelativeError: isolate the small-scale exponential absorption

The parameter estimate is stated separately from the scalar low/high
recombination.  Its numeric hypothesis records the choice of the scale
parameter and the eventual domination of a polynomial loss by an exponential.
-/

@[expose] public section

namespace AVenhance.Infra.Section5.RelativeError

/-- Convert the scale-ratio and diffusivity bounds into the explicit
exponential absorption used by `e44_combine_low_mode_and_analytic_tail`. -/
theorem e44_parameter_exponential_absorption
    {ε p δ c A Cν ν r R : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hA : 0 < A) (hCν : 0 ≤ Cν)
    (hr : 0 < r)
    (hν : (Real.sqrt ν)⁻¹ ≤ Cν * Real.rpow ε (-p))
    (hscale : Real.rpow ε (-δ) ≤ R / r)
    (hnumeric : Cν * Real.rpow ε (-p) *
      Real.exp (-c * A * Real.rpow ε (-δ)) ≤ 1) :
    (Real.sqrt ν)⁻¹ * Real.exp (-c * R * (A / r)) ≤ 1 := by
  have hCA : 0 ≤ c * A := mul_nonneg hc.le hA.le
  have hscale' := mul_le_mul_of_nonneg_left hscale hCA
  have hscaleExp : -c * R * (A / r) ≤ -c * A * Real.rpow ε (-δ) := by
    have hratio : c * A * Real.rpow ε (-δ) ≤ c * R * (A / r) := by
      calc
        c * A * Real.rpow ε (-δ) ≤ c * A * (R / r) := hscale'
        _ = c * R * (A / r) := by field_simp [ne_of_gt hr]
    linarith
  have hexp := Real.exp_le_exp.mpr hscaleExp
  have hpow : 0 ≤ Real.rpow ε (-p) := Real.rpow_nonneg hε.le _
  calc
    (Real.sqrt ν)⁻¹ * Real.exp (-c * R * (A / r)) ≤
        (Cν * Real.rpow ε (-p)) *
          Real.exp (-c * R * (A / r)) :=
      mul_le_mul_of_nonneg_right hν (Real.exp_nonneg _)
    _ ≤ Cν * Real.rpow ε (-p) *
          Real.exp (-c * A * Real.rpow ε (-δ)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hCν hpow)
    _ ≤ 1 := hnumeric

end AVenhance.Infra.Section5.RelativeError
