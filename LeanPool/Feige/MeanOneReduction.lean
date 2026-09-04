/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.KStatistic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Reduction from means at most one to means exactly one

This is the final mean-normalization reduction in the proof of Theorem 2.1.
-/

open MeasureTheory ProbabilityTheory Set Filter

namespace Feige

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {n : ℕ} (Y : Fin n → Ω → ℝ)

/-- Normalize a positive-mean coordinate by its mean; replace a zero-mean
coordinate by the constant one. -/
def meanOneNormalize (μ : Measure Ω) (i : Fin n) (ω : Ω) : ℝ :=
  if (∫ ω', Y i ω' ∂μ) = 0 then 1
  else Y i ω / ∫ ω', Y i ω' ∂μ

theorem meanOneNormalize_measurable
    (hY : ∀ i, Measurable (Y i)) (i : Fin n) :
    Measurable (meanOneNormalize Y μ i) := by
  unfold meanOneNormalize
  split_ifs
  · exact measurable_const
  · exact (hY i).div_const _

theorem meanOneNormalize_integrable
    [IsFiniteMeasure μ]
    (hY : ∀ i, Integrable (Y i) μ) (i : Fin n) :
    Integrable (meanOneNormalize Y μ i) μ := by
  unfold meanOneNormalize
  split_ifs
  · exact integrable_const 1
  · exact (hY i).div_const _

theorem meanOneNormalize_nonneg
    (hY : ∀ i ω, 0 ≤ Y i ω) (i : Fin n) (ω : Ω) :
    0 ≤ meanOneNormalize Y μ i ω := by
  unfold meanOneNormalize
  split_ifs with hm
  · norm_num
  · have hmean : 0 < ∫ ω', Y i ω' ∂μ := lt_of_le_of_ne
      (integral_nonneg (hY i)) (Ne.symm hm)
    exact div_nonneg (hY i ω) hmean.le

theorem meanOneNormalize_mean
    [IsProbabilityMeasure μ]
    (i : Fin n) :
    (∫ ω, meanOneNormalize Y μ i ω ∂μ) = 1 := by
  unfold meanOneNormalize
  split_ifs with hm
  · simp
  · simp_rw [div_eq_inv_mul]
    rw [integral_const_mul, inv_mul_cancel₀ hm]

theorem meanOneNormalize_iIndepFun
    (hYindep : iIndepFun Y μ) :
    iIndepFun (meanOneNormalize Y μ) μ := by
  have h := hYindep.comp
    (fun i x ↦ if (∫ ω, Y i ω ∂μ) = 0 then 1
      else x / ∫ ω, Y i ω ∂μ)
    (fun i ↦ by
      split_ifs
      · exact measurable_const
      · fun_prop)
  change iIndepFun
    (fun i x ↦ if (∫ ω, Y i ω ∂μ) = 0 then 1
      else Y i x / ∫ ω, Y i ω ∂μ) μ
  exact h

theorem ae_le_meanOneNormalize
    (hYint : ∀ i, Integrable (Y i) μ)
    (hYnonneg : ∀ i ω, 0 ≤ Y i ω)
    (hYmean : ∀ i, (∫ ω, Y i ω ∂μ) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ i, Y i ω ≤ meanOneNormalize Y μ i ω := by
  rw [ae_all_iff]
  intro i
  by_cases hm : (∫ ω, Y i ω ∂μ) = 0
  · have hz : Y i =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (hYnonneg i) (hYint i)).1 hm
    filter_upwards [hz] with ω hω
    simp [meanOneNormalize, hm, hω]
  · have hpos : 0 < ∫ ω, Y i ω ∂μ :=
      lt_of_le_of_ne (integral_nonneg (hYnonneg i)) (Ne.symm hm)
    filter_upwards [] with ω
    rw [meanOneNormalize, ite_eq_right hm]
    apply (le_div_iff₀ hpos).2
    nlinarith [hYnonneg i ω, hYmean i]

/-- The rejection event for the original variables is almost-everywhere
contained in that for their mean-one normalization. -/
theorem ae_rejection_subset_normalized
    (hYint : ∀ i, Integrable (Y i) μ)
    (hYnonneg : ∀ i ω, 0 ≤ Y i ω)
    (hYmean : ∀ i, (∫ ω, Y i ω ∂μ) ≤ 1)
    (α : ℝ) :
    {ω | dirichletK (fun i ↦ Y i ω) ≤ α} ≤ᵐ[μ]
      {ω | dirichletK (fun i ↦ meanOneNormalize Y μ i ω) ≤ α} := by
  filter_upwards [ae_le_meanOneNormalize Y hYint hYnonneg hYmean] with ω hω
  intro hreject
  exact (dirichletK_antitone hω).trans hreject

/-- Consequently, normalization can only increase the rejection
probability. -/
theorem rejection_probability_le_normalized
    [IsFiniteMeasure μ]
    (hYint : ∀ i, Integrable (Y i) μ)
    (hYnonneg : ∀ i ω, 0 ≤ Y i ω)
    (hYmean : ∀ i, (∫ ω, Y i ω ∂μ) ≤ 1)
    (α : ℝ) :
    μ.real {ω | dirichletK (fun i ↦ Y i ω) ≤ α} ≤
      μ.real {ω | dirichletK (fun i ↦ meanOneNormalize Y μ i ω) ≤ α} := by
  exact ENNReal.toReal_mono (by finiteness)
    (measure_mono_ae (ae_rejection_subset_normalized Y hYint hYnonneg hYmean α))

end

end Feige
