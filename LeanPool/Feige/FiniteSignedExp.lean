/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TranslationTP2
import Mathlib.Probability.Distributions.Exponential

/-!
# Finite signed exponential sums

The common part of a genuine insertion edge is a distinguished rate-one
exponential together with finitely many positive or negative scaled
rate-one exponentials.  This file gives that law an explicit normalized
density and derives its four-point log-concavity from translation TP2
closure under convolution.
-/

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace Feige
namespace LikelihoodRatio

noncomputable section

lemma rightExponentialDensity_eq_exponentialPDF
    {a : ℝ} (ha : 0 < a) :
    rightExponentialDensity a = exponentialPDF a⁻¹ := by
  funext x
  by_cases hx : 0 ≤ x
  · rw [rightExponentialDensity, ite_eq_left hx,
      exponentialPDF_of_nonneg hx]
    congr 1
    field_simp [ha.ne']
  · rw [rightExponentialDensity, ite_eq_right hx,
      exponentialPDF_of_neg (lt_of_not_ge hx)]

lemma lintegral_rightExponentialDensity
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, rightExponentialDensity a x = 1 := by
  rw [rightExponentialDensity_eq_exponentialPDF ha]
  exact lintegral_exponentialPDF_eq_one (inv_pos.mpr ha)

lemma lintegral_leftExponentialDensity
    {b : ℝ} (hb : 0 < b) :
    ∫⁻ x, leftExponentialDensity b x = 1 := by
  unfold leftExponentialDensity
  rw [lintegral_neg_eq_self]
  exact lintegral_rightExponentialDensity hb

lemma rightExponentialDensity_ne_top (a x : ℝ) :
    rightExponentialDensity a x ≠ ∞ := by
  unfold rightExponentialDensity
  split_ifs <;> simp

lemma leftExponentialDensity_ne_top (b x : ℝ) :
    leftExponentialDensity b x ≠ ∞ :=
  rightExponentialDensity_ne_top b (-x)

lemma rightExponentialDensity_le_rate
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    rightExponentialDensity a x ≤ ENNReal.ofReal a⁻¹ := by
  by_cases hx : 0 ≤ x
  · rw [rightExponentialDensity, ite_eq_left hx]
    have hexp : Real.exp (-x / a) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) ha.le
    rw [show Real.exp (-x / a) / a =
        a⁻¹ * Real.exp (-x / a) by field_simp [ha.ne']]
    rw [ENNReal.ofReal_mul (inv_pos.mpr ha).le]
    exact mul_le_of_le_one_right'
      (ENNReal.ofReal_le_one.mpr hexp)
  · rw [rightExponentialDensity, ite_eq_right hx]
    exact bot_le

lemma leftExponentialDensity_le_rate
    {b : ℝ} (hb : 0 < b) (x : ℝ) :
    leftExponentialDensity b x ≤ ENNReal.ofReal b⁻¹ :=
  rightExponentialDensity_le_rate hb (-x)

/-- The sign of one nondegenerate scaled exponential summand. -/
inductive ExpDirection
  | positive
  | negative
  deriving DecidableEq

/-- One positive or negative scaled rate-one exponential summand. -/
structure SignedExpFactor where
  /-- Whether the exponential summand is positive or negative. -/
  direction : ExpDirection
  /-- The positive scale of the summand. -/
  scale : ℝ
  scale_pos : 0 < scale

namespace SignedExpFactor

/-- The one-sided exponential density associated with a signed factor. -/
def density (F : SignedExpFactor) : ℝ → ℝ≥0∞ :=
  match F.direction with
  | .positive => rightExponentialDensity F.scale
  | .negative => leftExponentialDensity F.scale

lemma measurable_density (F : SignedExpFactor) :
    Measurable F.density := by
  cases h : F.direction
  · simpa [density, h] using
      measurable_rightExponentialDensity F.scale
  · simpa [density, h] using
      measurable_leftExponentialDensity F.scale

lemma density_ne_top (F : SignedExpFactor) (x : ℝ) :
    F.density x ≠ ∞ := by
  cases h : F.direction
  · simpa [density, h] using
      rightExponentialDensity_ne_top F.scale x
  · simpa [density, h] using
      leftExponentialDensity_ne_top F.scale x

lemma lintegral_density (F : SignedExpFactor) :
    ∫⁻ x, F.density x = 1 := by
  cases h : F.direction
  · simpa [density, h] using
      lintegral_rightExponentialDensity F.scale_pos
  · simpa [density, h] using
      lintegral_leftExponentialDensity F.scale_pos

lemma density_le_rate (F : SignedExpFactor) (x : ℝ) :
    F.density x ≤ ENNReal.ofReal F.scale⁻¹ := by
  cases h : F.direction
  · simpa [density, h] using
      rightExponentialDensity_le_rate F.scale_pos x
  · simpa [density, h] using
      leftExponentialDensity_le_rate F.scale_pos x

lemma translationTP2_density (F : SignedExpFactor) :
    TranslationTP2 F.density := by
  cases h : F.direction
  · simpa [density, h] using
      (fourPointLogConcave_rightExponentialDensity
        F.scale_pos).translationTP2
  · simpa [density, h] using
      (fourPointLogConcave_leftExponentialDensity
        F.scale_pos).translationTP2

end SignedExpFactor

/--
Density of a distinguished rate-one exponential convolved with finitely
many signed scaled exponentials.
-/
def finiteSignedExpSumDensity :
    List SignedExpFactor → ℝ → ℝ≥0∞
  | [] => rightExponentialDensity 1
  | F :: Fs =>
      densityConvolution F.density (finiteSignedExpSumDensity Fs)

lemma measurable_finiteSignedExpSumDensity :
    ∀ Fs : List SignedExpFactor,
      Measurable (finiteSignedExpSumDensity Fs)
  | [] => measurable_rightExponentialDensity 1
  | F :: Fs =>
      measurable_densityConvolution F.measurable_density
        (measurable_finiteSignedExpSumDensity Fs)

lemma lintegral_finiteSignedExpSumDensity :
    ∀ Fs : List SignedExpFactor,
      ∫⁻ x, finiteSignedExpSumDensity Fs x = 1
  | [] => lintegral_rightExponentialDensity zero_lt_one
  | F :: Fs =>
      lintegral_densityConvolution_eq_one F.measurable_density
        (measurable_finiteSignedExpSumDensity Fs)
        F.lintegral_density
        (lintegral_finiteSignedExpSumDensity Fs)

lemma densityConvolution_le_of_left_bound
    {f g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {C : ℝ≥0∞} (hfC : ∀ x, f x ≤ C)
    (hgInt : ∫⁻ x, g x = 1) (x : ℝ) :
    densityConvolution f g x ≤ C := by
  rw [densityConvolution_apply]
  calc
    (∫⁻ y, f y * g (x - y)) ≤
        ∫⁻ y, C * g (x - y) := by
      exact lintegral_mono fun y ↦
        mul_le_mul_left (hfC y) (g (x - y))
    _ = C * ∫⁻ y, g (x - y) := by
      rw [lintegral_const_mul]
      fun_prop
    _ = C * ∫⁻ y, g y := by
      rw [lintegral_sub_left_eq_self]
    _ = C := by rw [hgInt, mul_one]

lemma finiteSignedExpSumDensity_ne_top :
    ∀ (Fs : List SignedExpFactor) (x : ℝ),
      finiteSignedExpSumDensity Fs x ≠ ∞
  | [], x => rightExponentialDensity_ne_top 1 x
  | F :: Fs, x => by
      apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
      exact densityConvolution_le_of_left_bound
        (measurable_finiteSignedExpSumDensity Fs)
        F.density_le_rate
        (lintegral_finiteSignedExpSumDensity Fs) x

/-- Finite signed exponential convolution remains translation TP2. -/
theorem translationTP2_finiteSignedExpSumDensity :
    ∀ Fs : List SignedExpFactor,
      TranslationTP2 (finiteSignedExpSumDensity Fs)
  | [] =>
      (fourPointLogConcave_rightExponentialDensity
        zero_lt_one).translationTP2
  | F :: Fs =>
      F.translationTP2_density.convolution
        F.measurable_density
        (measurable_finiteSignedExpSumDensity Fs)
        F.density_ne_top
        (finiteSignedExpSumDensity_ne_top Fs)
        (translationTP2_finiteSignedExpSumDensity Fs)

/-- The explicit four-point log-concavity needed by the local exponential
transfer step. -/
theorem fourPointLogConcave_finiteSignedExpSumDensity
    (Fs : List SignedExpFactor) :
    FourPointLogConcave (finiteSignedExpSumDensity Fs) :=
  (translationTP2_finiteSignedExpSumDensity Fs).fourPointLogConcave

instance instIsProbabilityMeasureWithDensityFiniteSignedExpSum
    (Fs : List SignedExpFactor) :
    IsProbabilityMeasure
      (volume.withDensity (finiteSignedExpSumDensity Fs)) where
  measure_univ := by
    rw [withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,
      lintegral_finiteSignedExpSumDensity Fs]

/-- The same finite signed-exponential law constructed directly by
successive convolution of its absolutely continuous factor laws. -/
def finiteSignedExpSumMeasure :
    List SignedExpFactor → Measure ℝ
  | [] => volume.withDensity (rightExponentialDensity 1)
  | F :: Fs =>
      (volume.withDensity F.density) ∗
        finiteSignedExpSumMeasure Fs

/-- The recursively convolved law has exactly the explicit TP2 density. -/
theorem finiteSignedExpSumMeasure_eq_withDensity :
    ∀ Fs : List SignedExpFactor,
      finiteSignedExpSumMeasure Fs =
        volume.withDensity (finiteSignedExpSumDensity Fs)
  | [] => rfl
  | F :: Fs => by
      rw [finiteSignedExpSumMeasure, finiteSignedExpSumDensity,
        finiteSignedExpSumMeasure_eq_withDensity Fs,
        conv_withDensity_eq_withDensity_densityConvolution
          F.measurable_density
          (measurable_finiteSignedExpSumDensity Fs)]

instance instIsProbabilityMeasureFiniteSignedExpSumMeasure
    (Fs : List SignedExpFactor) :
    IsProbabilityMeasure (finiteSignedExpSumMeasure Fs) := by
  rw [finiteSignedExpSumMeasure_eq_withDensity Fs]
  infer_instance

end
end LikelihoodRatio
end Feige
