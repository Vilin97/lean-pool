/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Tail Layer-Cake Formula

A real-valued specialization of the layer-cake formula for nonnegative random variables.

## Main definitions

This module introduces no new definitions.

## Main results

* `lintegral_eq_lintegral_tail`: a nonnegative function is the integral of its upper tails.
-/

open MeasureTheory Set Real Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected value of a non-negative random variable equals the integral
    of its tail probabilities. This is the layer-cake formula. -/
theorem lintegral_eq_lintegral_tail {μ : Measure Ω} {X : Ω → ℝ}
    (hX_meas : AEMeasurable X μ) (hX_nonneg : 0 ≤ᵐ[μ] X) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ∫⁻ t in Ioi 0, μ {ω | t ≤ X ω} :=
  lintegral_eq_lintegral_meas_le μ hX_nonneg hX_meas


end
