/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic


/-!
# The kernel integral on `L^∞`

This file proves the real-valued `L^∞` contraction estimate for integration
against a sub-Markov kernel preserving a subinvariant measure.  The operator
itself is packaged as a continuous linear map by `kernelLpTop` in
`Kernel/Lp.lean`.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- Integrating a function bounded almost everywhere by `C` against a
sub-Markov kernel measure preserves that bound. -/
theorem enorm_kernelIntegral_le_of_ae {κ : ProbabilityTheory.Kernel α α}
    (hκ : IsSubMarkovKernel κ) {f : α → ℝ} {C : ℝ≥0∞} {x : α}
    (hf : ∀ᵐ y ∂κ x, ‖f y‖ₑ ≤ C) :
    ‖kernelIntegral κ f x‖ₑ ≤ C := by
  calc
    ‖kernelIntegral κ f x‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ ∂κ x :=
      enorm_integral_le_lintegral_enorm f
    _ ≤ ∫⁻ _y, C ∂κ x := lintegral_mono_ae hf
    _ = C * κ x Set.univ := lintegral_const C
    _ ≤ C * 1 := mul_le_mul_right (hκ.measure_le_one x Set.univ) C
    _ = C := mul_one C

/-- The essential-supremum bound for `f` bounds its kernel integral almost
everywhere under subinvariance. -/
theorem enorm_kernelIntegral_ae_le_eLpNormEssSup {μ : Measure α}
    {κ : ProbabilityTheory.Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (f : α → ℝ) :
    ∀ᵐ x ∂μ, ‖kernelIntegral κ f x‖ₑ ≤ eLpNormEssSup f μ := by
  filter_upwards
    [ae_ae_kernel_of_comp_le hκμ (enorm_ae_le_eLpNormEssSup f μ)] with x hx
  exact enorm_kernelIntegral_le_of_ae hκ hx

/-- Integration against a sub-Markov kernel is a contraction for the raw
`L^∞` seminorm under subinvariance. -/
theorem eLpNorm_kernelIntegral_top_le {μ : Measure α}
    {κ : ProbabilityTheory.Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (f : α → ℝ) :
    eLpNorm (kernelIntegral κ f) ∞ μ ≤ eLpNorm f ∞ μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [eLpNorm_exponent_top (AEStronglyMeasurable.kernelIntegral hf hκμ), eLpNorm_exponent_top hf]
    exact eLpNormEssSup_le_of_ae_enorm_bound
      (enorm_kernelIntegral_ae_le_eLpNormEssSup hκ hκμ f)
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top

/-- Integration against a sub-Markov kernel sends `L^∞` functions to
`L^∞` functions under subinvariance. -/
theorem MemLp.kernelIntegral_top {μ : Measure α}
    {κ : ProbabilityTheory.Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} (hf : MemLp f ∞ μ) :
    MemLp (kernelIntegral κ f) ∞ μ := by
  exact (eLpNorm_kernelIntegral_top_le hκ hκμ f).trans_lt hf.eLpNorm_lt_top

end MarkovProcess
