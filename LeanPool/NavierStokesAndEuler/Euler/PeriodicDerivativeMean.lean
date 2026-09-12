/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The mean of a genuine derivative of a periodic field is zero. -/

@[expose] public section


noncomputable section

namespace EulerPeriodicDerivativeMean

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_derivative_eq_zero (P : ℝ) (f f' : ℝ → E)
    (hf : ∀ θ, HasDerivAt f (f' θ) θ) (hf' : Continuous f')
    (hper : Function.Periodic f P) : (∫ θ in 0..P, f' θ)=0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hf θ)
    (hf'.intervalIntegrable 0 P)]
  simpa only [zero_add] using sub_eq_zero.mpr (hper 0)

/-- A coefficient independent of angle cannot change this zero-mean conclusion. -/
theorem integral_constant_smul_derivative_eq_zero (P c : ℝ) (f f' : ℝ → E)
    (hf : ∀ θ, HasDerivAt f (f' θ) θ) (hf' : Continuous f')
    (hper : Function.Periodic f P) : (∫ θ in 0..P, c • f' θ)=0 := by
  rw [intervalIntegral.integral_smul, integral_derivative_eq_zero P f f' hf hf' hper,
    smul_zero]

end EulerPeriodicDerivativeMean
