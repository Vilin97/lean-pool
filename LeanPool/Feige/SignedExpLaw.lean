/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.FiniteSignedExp

/-!
# Probability laws of signed scaled exponentials

This file identifies the explicit one-sided densities with pushforwards of
a rate-one exponential.  It is the first bridge from the original product
of exponential coordinates in `dirichletK` to the finite convolution law
used by the TP2 proof.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Feige
namespace LikelihoodRatio

noncomputable section

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

lemma expMeasure_inv_eq_withDensity_rightExponentialDensity
    {a : ℝ} (ha : 0 < a) :
    expMeasure a⁻¹ =
      volume.withDensity (rightExponentialDensity a) := by
  rw [rightExponentialDensity_eq_exponentialPDF ha]
  rfl

/-- Scaling a rate-one exponential by `a > 0` gives the density of `aE`. -/
theorem map_mul_expMeasure_one
    {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x : ℝ ↦ a * x) (expMeasure 1) =
      volume.withDensity (rightExponentialDensity a) := by
  rw [← expMeasure_inv_eq_withDensity_rightExponentialDensity ha]
  let : IsProbabilityMeasure (expMeasure a⁻¹) :=
    isProbabilityMeasure_expMeasure (inv_pos.mpr ha)
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre :
      (fun t : ℝ ↦ a * t) ⁻¹' Iic x = Iic (x / a) := by
    ext t
    simp only [mem_preimage, mem_Iic]
    constructor
    · intro h
      apply (le_div_iff₀ ha).2
      simpa [mul_comm] using h
    · intro h
      have h' := (le_div_iff₀ ha).1 h
      simpa [mul_comm] using h'
  rw [hpre, ← ofReal_cdf, ← ofReal_cdf]
  congr 1
  rw [cdf_expMeasure_eq one_pos, cdf_expMeasure_eq (inv_pos.mpr ha)]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left (div_nonneg hx ha.le)]
    congr 2
    field_simp [ha.ne']
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [ite_eq_right hx, ite_eq_right (not_le.mpr (div_neg_of_neg_of_pos hx' ha))]

/-- Reflection transports a density by precomposition with negation. -/
theorem map_neg_withDensity
    (f : ℝ → ℝ≥0∞) :
    Measure.map (fun x : ℝ ↦ -x) (volume.withDensity f) =
      volume.withDensity (fun x ↦ f (-x)) := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs,
    withDensity_apply _ (hs.preimage measurable_neg),
    withDensity_apply _ hs,
    ← lintegral_indicator (hs.preimage measurable_neg),
    ← lintegral_indicator hs]
  let h : ℝ → ℝ≥0∞ :=
    fun x ↦ s.indicator (fun y ↦ f (-y)) x
  have hneg := lintegral_neg_eq_self (μ := volume) h
  calc
    (∫⁻ x, ((fun y : ℝ ↦ -y) ⁻¹' s).indicator f x) =
        ∫⁻ x, h (-x) := by
      apply lintegral_congr
      intro x
      by_cases hx : -x ∈ s
      · have hxpre : x ∈ (fun y : ℝ ↦ -y) ⁻¹' s := hx
        have hh : h (-x) = f x := by
          dsimp only [h]
          rw [Set.indicator_of_mem hx, neg_neg]
        rw [Set.indicator_of_mem hxpre, hh]
      · have hxpre : x ∉ (fun y : ℝ ↦ -y) ⁻¹' s := hx
        have hh : h (-x) = 0 := by
          dsimp only [h]
          rw [Set.indicator_of_notMem hx]
        rw [Set.indicator_of_notMem hxpre, hh]
    _ = ∫⁻ x, h x := hneg
    _ = ∫⁻ x, s.indicator (fun y ↦ f (-y)) x := rfl

/-- The reflected pushforward is the density of `-bE`. -/
theorem map_neg_mul_expMeasure_one
    {b : ℝ} (hb : 0 < b) :
    Measure.map (fun x : ℝ ↦ -(b * x)) (expMeasure 1) =
      volume.withDensity (leftExponentialDensity b) := by
  calc
    Measure.map (fun x : ℝ ↦ -(b * x)) (expMeasure 1) =
        Measure.map (fun y : ℝ ↦ -y)
          (Measure.map (fun x : ℝ ↦ b * x) (expMeasure 1)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map (fun y : ℝ ↦ -y)
          (volume.withDensity (rightExponentialDensity b)) := by
      rw [map_mul_expMeasure_one hb]
    _ = volume.withDensity (leftExponentialDensity b) := by
      rw [map_neg_withDensity (rightExponentialDensity b)]
      rfl

/-- Every signed factor density is the law of its signed scale times a
rate-one exponential. -/
theorem SignedExpFactor.map_expMeasure_one (F : SignedExpFactor) :
    Measure.map
        (fun x : ℝ ↦
          match F.direction with
          | .positive => F.scale * x
          | .negative => -(F.scale * x))
        (expMeasure 1) =
      volume.withDensity F.density := by
  cases h : F.direction
  · simpa [SignedExpFactor.density, h] using
      map_mul_expMeasure_one F.scale_pos
  · simpa [SignedExpFactor.density, h] using
      map_neg_mul_expMeasure_one F.scale_pos

/-- The pushforward law of one signed factor. -/
def SignedExpFactor.sourceLaw (F : SignedExpFactor) : Measure ℝ :=
  Measure.map
    (fun x : ℝ ↦
      match F.direction with
      | .positive => F.scale * x
      | .negative => -(F.scale * x))
    (expMeasure 1)

lemma SignedExpFactor.sourceLaw_eq_withDensity
    (F : SignedExpFactor) :
    F.sourceLaw = volume.withDensity F.density :=
  F.map_expMeasure_one

/--
An explicit independent-sum construction of the distinguished exponential
and every signed factor.  Convolution is the pushforward of the product law
under addition, so this is an actual random-sum law rather than merely a
density recursion.
-/
def finiteSignedExpSumSourceMeasure :
    List SignedExpFactor → Measure ℝ
  | [] => Measure.map (fun x : ℝ ↦ x) (expMeasure 1)
  | F :: Fs =>
      F.sourceLaw ∗ finiteSignedExpSumSourceMeasure Fs

theorem finiteSignedExpSumSourceMeasure_eq :
    ∀ Fs : List SignedExpFactor,
      finiteSignedExpSumSourceMeasure Fs =
        finiteSignedExpSumMeasure Fs
  | [] => by
      rw [finiteSignedExpSumSourceMeasure, finiteSignedExpSumMeasure]
      change Measure.map id (expMeasure 1) =
        volume.withDensity (rightExponentialDensity 1)
      rw [Measure.map_id]
      simpa using
        (expMeasure_inv_eq_withDensity_rightExponentialDensity
          (a := (1 : ℝ)) zero_lt_one)
  | F :: Fs => by
      rw [finiteSignedExpSumSourceMeasure, finiteSignedExpSumMeasure,
        F.sourceLaw_eq_withDensity,
        finiteSignedExpSumSourceMeasure_eq Fs]

end
end LikelihoodRatio
end Feige
