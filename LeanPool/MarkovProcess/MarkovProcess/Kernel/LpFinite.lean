/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite-exponent contraction for sub-Markov kernels

This file proves the scalar subprobability estimate behind contraction of a
sub-Markov kernel on finite `Lᵖ` spaces, and its fibrewise integrated form.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- On a finite measure of mass at most one, the `L¹` seminorm is bounded by
every finite `Lᵖ` seminorm with `p ≥ 1`. -/
theorem eLpNorm_one_le_of_measure_univ_le_one {ν : Measure α} {f : α → ℝ}
     {p : NNReal} (hp : 1 ≤ p) (hν : ν Set.univ ≤ 1)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 1 ν ≤ eLpNorm f p ν := by
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := ν) (f := f) (p := (1 : ℝ≥0∞)) (q := (p : ℝ≥0∞))
    (by exact_mod_cast hp) hf
  calc
    eLpNorm f 1 ν
        ≤ eLpNorm f p ν * ν Set.univ ^ (1 - 1 / (p : ℝ)) := by
          simpa using hcompare
    _ ≤ eLpNorm f p ν * 1 := by
          gcongr
          calc
            ν Set.univ ^ (1 - 1 / (p : ℝ))
                ≤ (1 : ℝ≥0∞) ^ (1 - 1 / (p : ℝ)) := by
                  exact ENNReal.rpow_le_rpow hν (by
                    rw [sub_nonneg, div_le_one (by exact_mod_cast zero_lt_one.trans_le hp)]
                    exact_mod_cast hp)
            _ = 1 := ENNReal.one_rpow _
    _ = eLpNorm f p ν := mul_one _

/-- Jensen's power estimate for a finite subprobability measure.  This form is
well suited to fibrewise use because both sides take values in `ℝ≥0∞`. -/
theorem enorm_integral_rpow_le_lintegral_enorm_rpow
    {ν : Measure α} {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hν : ν Set.univ ≤ 1) (hf : MemLp f p ν) :
    ‖∫ y, f y ∂ν‖ₑ ^ (p : ℝ) ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂ν := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hnorm : ‖∫ y, f y ∂ν‖ₑ ≤ eLpNorm f p ν := by
    calc
      ‖∫ y, f y ∂ν‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm f
      _ = eLpNorm f 1 ν := (eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable).symm
      _ ≤ eLpNorm f p ν := eLpNorm_one_le_of_measure_univ_le_one hp hν hf.aestronglyMeasurable
  calc
    ‖∫ y, f y ∂ν‖ₑ ^ (p : ℝ) ≤ eLpNorm f p ν ^ (p : ℝ) := by
      exact ENNReal.rpow_le_rpow hnorm (by positivity)
    _ = ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂ν := eLpNorm_nnreal_pow_eq_lintegral hp0 hf.aestronglyMeasurable

/-- The integrated fibrewise power estimate for a sub-Markov kernel. -/
theorem lintegral_enorm_kernelIntegral_rpow_le
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ∂μ
      ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ := by
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  have hfComp : MemLp f p (κ ∘ₘ μ) := hf.mono_measure hκμ
  have hfFiber : ∀ᵐ x ∂μ, MemLp f p (κ x) := by
    have hFiberEq := Measure.ae_ae_of_ae_comp hfComp.aestronglyMeasurable.ae_eq_mk
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
    have hpowInt := hfComp.integrable_norm_rpow hp0 ENNReal.coe_ne_top
    have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
    filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
    have hxEq' : f =ᵐ[κ x] hfComp.aestronglyMeasurable.mk f := hxEq
    have hxMeas : AEStronglyMeasurable f (κ x) :=
      hfComp.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq'.symm
    exact (integrable_norm_rpow_iff hxMeas hp0 ENNReal.coe_ne_top).mp hxInt
  calc
    ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ∂μ
        ≤ ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂κ x ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hfFiber] with x hx
          exact enorm_integral_rpow_le_lintegral_enorm_rpow hp (hκ x) hx
    _ = ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂(κ ∘ₘ μ) := by
          symm
          exact Measure.lintegral_bind (Kernel.aemeasurable κ)
            (hfComp.aestronglyMeasurable.enorm.pow_const (p : ℝ))
    _ ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ :=
      lintegral_mono' hκμ le_rfl

/-- A sub-Markov kernel which is subinvariant for `μ` is contractive on every
finite `Lᵖ` seminorm, `1 ≤ p < ∞`. -/
theorem eLpNorm_kernelIntegral_le
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    eLpNorm (kernelIntegral κ f) p μ ≤ eLpNorm f p μ := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  rw [eLpNorm_nnreal_eq_lintegral hp0 (AEStronglyMeasurable.kernelIntegral
      hf.aestronglyMeasurable hκμ),
    eLpNorm_nnreal_eq_lintegral hp0 hf.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow
  · exact lintegral_enorm_kernelIntegral_rpow_le hκ hκμ hp hf
  · positivity

/-- The kernel integral of an `Lᵖ` function is again in `Lᵖ` for every finite
exponent `p ≥ 1`. -/
theorem MemLp.kernelIntegral
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    MemLp (kernelIntegral κ f) p μ := by
  exact (eLpNorm_kernelIntegral_le hκ hκμ hp hf).trans_lt hf.eLpNorm_lt_top

end MarkovProcess
