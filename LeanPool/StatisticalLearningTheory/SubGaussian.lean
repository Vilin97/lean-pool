/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import LeanPool.HansonWright.Probability.Process.SubGaussian

/-!
# Sub-Gaussian compatibility API

This file preserves the scalar sub-Gaussian API used by the statistical-learning
development while delegating its implementation to `LeanPool.HansonWright`.
-/

noncomputable section

namespace LeanPool.StatisticalLearningTheory

open MeasureTheory
open _root_.ProbabilityTheory
open scoped NNReal

/-- A real random variable with a Gaussian moment-generating-function bound. -/
abbrev IsSubGaussian {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (σ_sq : ℝ)
    (μ : Measure Ω) : Prop :=
  _root_.LeanPool.IsSubGaussian X σ_sq μ

/-- Monotonicity of the MGF sub-Gaussian parameter. -/
lemma hasSubgaussianMGF_mono_param {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    {μ : Measure Ω} {c d : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    (hcd : (c : ℝ) ≤ d) : HasSubgaussianMGF X d μ :=
  _root_.LeanPool.hasSubgaussianMGF_mono_param h hcd

/-- A sub-Gaussian random variable has integrable exponential tilts. -/
lemma IsSubGaussian.integrable_exp_mul {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {σ_sq : ℝ} {μ : Measure Ω}
    (h_sg : IsSubGaussian X σ_sq μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * X x)) μ :=
  _root_.LeanPool.IsSubGaussian.integrable_exp_mul h_sg t

/-- Compatibility name for exponential integrability of sub-Gaussian random variables. -/
lemma sub_gaussian_integrable {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {σ_sq : ℝ} {μ : Measure Ω}
    (h_sg : IsSubGaussian X σ_sq μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * X x)) μ :=
  h_sg.integrable_exp_mul t

/-- A sub-Gaussian real random variable is integrable. -/
lemma IsSubGaussian.integrable {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {σ_sq : ℝ} {μ : Measure Ω}
    (h_sg : IsSubGaussian X σ_sq μ) : Integrable X μ :=
  _root_.LeanPool.IsSubGaussian.integrable h_sg

/-- A finite supremum of absolute values of integrable functions is integrable. -/
lemma integrable_ciSup_abs_of_fintype {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Finite ι] [Nonempty ι] {Y : ι → Ω → ℝ} {μ : Measure Ω}
    (h_int : ∀ i, Integrable (Y i) μ) : Integrable (fun x => ⨆ i, |Y i x|) μ :=
  _root_.LeanPool.integrable_ciSup_abs_of_fintype h_int

end LeanPool.StatisticalLearningTheory
