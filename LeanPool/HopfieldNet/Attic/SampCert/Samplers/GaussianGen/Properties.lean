/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Samplers.GaussianGen.Code
import LeanPool.HopfieldNet.SampCert.Samplers.Gaussian.Properties
import LeanPool.HopfieldNet.SampCert.Util.Gaussian.DiscreteGaussian
import LeanPool.HopfieldNet.SampCert.Util.Gaussian.GaussPeriodicity

/-!
# ``DiscreteGaussianGenSample`` Properties

This file proves evaluation and normalization properties of ``DiscreteGaussianGenSample``.
-/
noncomputable section

open Classical PMF Nat Real

namespace SLang

lemma if_simple_GaussianGen (x_1 x μ : ℤ) :
  (@ite ENNReal (x_1 = x - μ) (propDecidable (x_1 = x - μ)) 0
  (@ite ENNReal (x = x_1 + μ) (x.instDecidableEq (x_1 + μ))
  (ENNReal.ofReal (gauss_term_ℝ (↑↑num / ↑↑den) 0 ↑x_1 / ∑' (x : ℤ), gauss_term_ℝ (↑↑num / ↑↑den) 0 ↑x)) 0)) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      simp at h1
    · simp

/--
``SLang`` general discrete gaussian term evaluates according to the mathematical ``discrete_gaussian`` distribution.
-/
theorem DiscreteGaussianGenSample_apply (num : PNat) (den : PNat) (μ x : ℤ) :
  (DiscreteGaussianGenSample num den μ) x =
  ENNReal.ofReal (discrete_gaussian ((num : ℝ) / (den : ℝ)) μ x) := by
  have A : (num : ℝ) / (den : ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, cast_eq_zero, PNat.ne_zero, or_self, not_false_eq_true]
  simp [DiscreteGaussianGenSample, discrete_gaussian]
  rw [ENNReal.tsum_eq_add_tsum_ite (x - μ)]
  simp
  conv =>
    left
    right
    right
    intro y
    rw [if_simple_GaussianGen]
  simp only [tsum_zero, add_zero]
  congr 2
  · simp [gauss_term_ℝ]
  · rw [shifted_gauss_sum_0 A]

/--
DiscreteGaussianGen has sum 1
-/
theorem DiscreteGaussianGen_sum (num : PNat) (den : PNat) (μ : ℤ) : HasSum (DiscreteGaussianGenSample num den μ) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  conv =>
    lhs
    arg 1
    intro b
    rw [DiscreteGaussianGenSample_apply]

  have Hnz : (num / den : ℝ) ≠ 0 := by simp
  have Hcoe : (OfNat.ofNat 1 = ENNReal.ofReal (OfNat.ofNat 1)) := by simp
  rw [Hcoe]
  rw [<- (discrete_gaussian_normalizes Hnz μ)]
  symm
  apply (ENNReal.ofReal_tsum_of_nonneg ?hf_nonneg ?hf)
  · exact fun n => discrete_gaussian_nonneg Hnz (↑μ) n
  · apply discrete_gaussian_summable'
    apply Hnz

/--
DiscreteGaussianGen as a PMF
-/
def DiscreteGaussianGenPMF (num : PNat) (den : PNat) (μ : ℤ) : PMF ℤ :=
  ⟨ DiscreteGaussianGenSample num den μ , DiscreteGaussianGen_sum num den μ ⟩




end SLang
