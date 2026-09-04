/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.OneSidedDensity
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Nonnegative density convolution

The closure of log-concavity under convolution is the one-dimensional case
of the Prékopa theorem.  Mathlib does not currently provide that theorem.
This file establishes its measure-theoretic convolution layer; the required
one-dimensional closure is proved by the TP2/Cauchy--Binet argument in
`Feige.TranslationTP2` and instantiated for the insertion common laws in
`Feige.FiniteSignedExp`.
-/

open MeasureTheory
open scoped ENNReal

namespace Feige
namespace LikelihoodRatio

/-- Lebesgue convolution of two nonnegative densities on the line. -/
noncomputable def densityConvolution (f g : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  f ⋆ₗ[volume] g

theorem densityConvolution_apply (f g : ℝ → ℝ≥0∞) (x : ℝ) :
    densityConvolution f g x = ∫⁻ y, f y * g (x - y) := by
  simp [densityConvolution, lconvolution_def, sub_eq_add_neg, add_comm]

theorem measurable_densityConvolution {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (densityConvolution f g) := by
  exact measurable_lconvolution volume hf hg

theorem densityConvolution_assoc {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    densityConvolution (densityConvolution f g) h =
      densityConvolution f (densityConvolution g h) := by
  exact (lconvolution_assoc hf hg hh).symm

/-- The integral of a nonnegative convolution is the product of the two
integrals.  No finiteness assumptions are needed. -/
theorem lintegral_densityConvolution {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, densityConvolution f g x =
      (∫⁻ x, f x) * ∫⁻ x, g x := by
  have hinner (y : ℝ) :
      (∫⁻ x, f y * g (-y + x)) = f y * ∫⁻ x, g x := by
    rw [lintegral_const_mul'' _ (by fun_prop),
      lintegral_add_left_eq_self]
  simp only [densityConvolution, lconvolution_def]
  rw [lintegral_lintegral_swap]
  · simp_rw [hinner]
    exact lintegral_mul_const'' _ hf.aemeasurable
  · fun_prop

/-- Convolution preserves normalization of nonnegative densities. -/
theorem lintegral_densityConvolution_eq_one {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf_one : ∫⁻ x, f x = 1) (hg_one : ∫⁻ x, g x = 1) :
    ∫⁻ x, densityConvolution f g x = 1 := by
  rw [lintegral_densityConvolution hf hg, hf_one, hg_one, one_mul]

/-- Convolving densities agrees with convolving their absolutely continuous
measures. -/
theorem conv_withDensity_eq_withDensity_densityConvolution
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    volume.withDensity f ∗ volume.withDensity g =
      volume.withDensity (densityConvolution f g) := by
  exact conv_withDensity_eq_lconvolution hf hg

end LikelihoodRatio
end Feige
