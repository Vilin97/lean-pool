/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Integral seminorms without measurability assumptions -/

@[expose] public section

namespace Homogenization.Gagliardo

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {E : Type*} [ENorm E]

/-- The integral seminorm, including nonmeasurable functions, with the essential
supremum at infinity. This keeps the manuscript's integral definition independent
of the measurability convention in Mathlib's `eLpNorm`. -/
def integralLpSeminorm {α : Type*} [MeasurableSpace α]
    (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ

/-- For measurable functions the integral seminorm agrees with Mathlib's norm. -/
theorem integralLpSeminorm_eq_eLpNorm {α : Type*} [MeasurableSpace α]
    (f : α → E) (p : ℝ≥0∞) (μ : Measure α) [TopologicalSpace E] (hf : AEStronglyMeasurable f μ) :
    integralLpSeminorm f p μ = eLpNorm f p μ := by
  simp only [integralLpSeminorm, eLpNorm, if_pos hf]

/-- Negation leaves the integral seminorm unchanged, without measurability assumptions. -/
theorem integralLpSeminorm_neg {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    integralLpSeminorm (-f) p μ = integralLpSeminorm f p μ := by
  simp only [integralLpSeminorm, eLpNormEssSup_eq_essSup_enorm,
    Pi.neg_apply, enorm_neg, eLpNorm'_neg]

/-- Almost everywhere equal functions have equal integral seminorms. -/
theorem integralLpSeminorm_congr_ae {α : Type*} [MeasurableSpace α]
    {f g : α → E} {p : ℝ≥0∞} {μ : Measure α} (h : f =ᵐ[μ] g) :
    integralLpSeminorm f p μ = integralLpSeminorm g p μ := by
  simp only [integralLpSeminorm, eLpNormEssSup_congr_ae h, eLpNorm'_congr_ae h]

/-- Scaling a measure scales the finite-exponent integral seminorm. -/
theorem integralLpSeminorm_smul_measure {α : Type*} [MeasurableSpace α]
    (f : α → E) {p : ℝ≥0∞} (hp : p ≠ ∞) (μ : Measure α) (c : ℝ≥0∞) :
    integralLpSeminorm f p (c • μ) = c ^ (1 / p).toReal * integralLpSeminorm f p μ := by
  by_cases hp0 : p = 0
  · simp [integralLpSeminorm, hp0]
  · simp only [integralLpSeminorm, if_neg hp0, if_neg hp]
    simpa only [one_div, ENNReal.toReal_inv] using
      eLpNorm'_smul_measure (f := f) (μ := μ) ENNReal.toReal_nonneg c

/-- Restricting to a set containing the support preserves the integral seminorm,
including for functions that are not measurable. -/
theorem integralLpSeminorm_restrict_eq_of_support_subset
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {s : Set α} {f : α → E}
    (hsf : f.support ⊆ s) :
    integralLpSeminorm f p (μ.restrict s) = integralLpSeminorm f p μ := by
  by_cases hp0 : p = 0
  · simp only [integralLpSeminorm, if_pos hp0]
  by_cases hpt : p = ∞
  · simp only [integralLpSeminorm, if_neg hp0, if_pos hpt,
      eLpNormEssSup_eq_essSup_enorm]
    exact ENNReal.essSup_restrict_eq_of_support_subset fun x hx ↦ hsf <| enorm_ne_zero.1 hx
  · simp only [integralLpSeminorm, if_neg hp0, if_neg hpt,
      eLpNorm'_eq_lintegral_enorm]
    congr 1
    apply setLIntegral_eq_of_support_subset
    have hp : ¬p.toReal ≤ 0 := not_le.mpr (ENNReal.toReal_pos hp0 hpt)
    simpa [hp] using hsf

/-- The integral seminorm is bounded by Mathlib's norm even without measurability. -/
theorem integralLpSeminorm_le_eLpNorm {α : Type*} [MeasurableSpace α]
    [TopologicalSpace E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    integralLpSeminorm f p μ ≤ eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact (integralLpSeminorm_eq_eLpNorm f p μ hf).le
  · simp only [eLpNorm, if_neg hf, le_top]

end

end Homogenization.Gagliardo
