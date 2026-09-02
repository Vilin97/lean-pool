/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1Division
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.NormalizedCoefficients

/-!
# Analytic quotient and remainder coefficient sequences

This file feeds the normalized moving coefficient sequence into the
`\ell^1(\mathbb N)` division theorem.  The resulting quotient and remainder
depend analytically on the base variables.  At the base origin, exact order
forces the remainder to vanish and the quotient to have constant coefficient
one.
-/

open Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace ClassicalComplexWPT

/-- The small perturbation of the normalized distinguished monomial. -/
noncomputable irreducible_def normalizedPreparationTail {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  fun z ↦ analyticNormalizedCoefficientMap p r hr d z - monomialSeq d

/-- The quotient produced by dividing the degree-`d` monomial by the
normalized moving coefficient sequence. -/
noncomputable irreducible_def normalizedPreparationQuotient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  fun z ↦ seqDivisionQuotientGlobal d
    (normalizedPreparationTail p r hr d z, monomialSeq d)

/-- The low-degree remainder produced by the same division. -/
noncomputable irreducible_def normalizedPreparationRemainder {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  fun z ↦ seqDivisionRemainderGlobal d
    (normalizedPreparationTail p r hr d z, monomialSeq d)

theorem analyticAt_normalizedPreparationTail {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    AnalyticAt ℂ (normalizedPreparationTail p r hr d) 0 := by
  have hfun : normalizedPreparationTail p r hr d = fun z ↦
      analyticNormalizedCoefficientMap p r hr d z - monomialSeq d := by
    funext z
    rw [normalizedPreparationTail_def]
  have hconst : AnalyticAt ℂ (fun _ : Base n ↦ monomialSeq d) 0 :=
    analyticAt_const
  have hraw : AnalyticAt ℂ (fun z : Base n ↦
      analyticNormalizedCoefficientMap p r hr d z - monomialSeq d) 0 :=
    (analyticAt_analyticNormalizedCoefficientMap p r hr d).sub hconst
  exact hfun.symm ▸ hraw

theorem analyticAt_normalizedPreparationQuotient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0 := by
  have hfun : normalizedPreparationQuotient p r hr d = fun z ↦
      seqDivisionQuotientGlobal d
        (normalizedPreparationTail p r hr d z, monomialSeq d) := by
    funext z
    rw [normalizedPreparationQuotient_def]
  have hin : AnalyticAt ℂ (fun z : Base n ↦
      (normalizedPreparationTail p r hr d z, monomialSeq d)) 0 :=
    (analyticAt_normalizedPreparationTail p r hr d).prod analyticAt_const
  have hsmall' : ‖(normalizedPreparationTail p r hr d 0, monomialSeq d).1‖ < 1 :=
    hsmall
  have hraw : AnalyticAt ℂ (fun z : Base n ↦
      seqDivisionQuotientGlobal d
        (normalizedPreparationTail p r hr d z, monomialSeq d)) 0 := by
    have hcomp := AnalyticAt.comp (x := (0 : Base n))
      (analyticAt_seqDivisionQuotientGlobal d
        (normalizedPreparationTail p r hr d 0, monomialSeq d) hsmall') hin
    simpa only [Function.comp_def] using hcomp
  exact hfun.symm ▸ hraw

theorem analyticAt_normalizedPreparationRemainder {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    AnalyticAt ℂ (normalizedPreparationRemainder p r hr d) 0 := by
  have hfun : normalizedPreparationRemainder p r hr d = fun z ↦
      seqDivisionRemainderGlobal d
        (normalizedPreparationTail p r hr d z, monomialSeq d) := by
    funext z
    rw [normalizedPreparationRemainder_def]
  have hin : AnalyticAt ℂ (fun z : Base n ↦
      (normalizedPreparationTail p r hr d z, monomialSeq d)) 0 :=
    (analyticAt_normalizedPreparationTail p r hr d).prod analyticAt_const
  have hsmall' : ‖(normalizedPreparationTail p r hr d 0, monomialSeq d).1‖ < 1 :=
    hsmall
  have hraw : AnalyticAt ℂ (fun z : Base n ↦
      seqDivisionRemainderGlobal d
        (normalizedPreparationTail p r hr d z, monomialSeq d)) 0 := by
    have hcomp := AnalyticAt.comp (x := (0 : Base n))
      (analyticAt_seqDivisionRemainderGlobal d
        (normalizedPreparationTail p r hr d 0, monomialSeq d) hsmall') hin
    simpa only [Function.comp_def] using hcomp
  exact hfun.symm ▸ hraw

/-- Convolution with the degree-`d` monomial inserts `d` leading zero
coefficients. -/
theorem convolution_monomialSeq (q : OriginSeq) (d : ℕ) :
    convolution q (monomialSeq d) = seqLowShift d q := by
  apply lp.ext
  funext n
  rw [convolution_apply]
  by_cases hn : n < d
  · rw [seqLowShift_apply_of_lt d q hn]
    apply Finset.sum_eq_zero
    intro ij hij
    have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    have hne : ij.2 ≠ d := by omega
    rw [monomialSeq_apply_ne hne, mul_zero]
  · have hdn : d ≤ n := Nat.le_of_not_gt hn
    rw [seqLowShift_apply_of_le d q hdn]
    rw [Finset.sum_eq_single (n - d, d)]
    · rw [monomialSeq_apply_same, mul_one]
    · intro ij hij hne
      have hdne : ij.2 ≠ d := by
        intro heq
        apply hne
        have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        apply Prod.ext
        · simp only
          omega
        · simpa only [Prod.snd] using heq
      rw [monomialSeq_apply_ne hdne, mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_antidiagonal]
      omega

lemma convolution_apply_eq_zero_of_right {q p : OriginSeq} {n : ℕ}
    (hp : ∀ k ≤ n, p k = 0) : convolution q p n = 0 := by
  rw [convolution_apply]
  apply Finset.sum_eq_zero
  intro ij hij
  have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [hp ij.2 (by omega), mul_zero]

lemma normalizedPreparationTail_zero_of_le {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : (r : ℝ≥0∞) < p.radius) {k : ℕ} (hk : k ≤ d) :
    normalizedPreparationTail p r hr d 0 k = 0 := by
  rw [normalizedPreparationTail_def, analyticNormalizedCoefficientMap_zero]
  by_cases hkd : k < d
  · change normalizedOriginCoeffs p r hr d k - monomialSeq d k = 0
    rw [normalizedOriginCoeffs_apply]
    have hcoeff : lastTaylorCoefficient p k 0 = 0 :=
      ((exactOrderInLastVariable_iff_lastTaylorCoefficients p hp).mp horder).1 k hkd
    rw [hcoeff, mul_zero, mul_zero]
    rw [monomialSeq_apply_ne (ne_of_lt hkd), sub_zero]
  · have hkeq : k = d := le_antisymm hk (Nat.le_of_not_gt hkd)
    subst k
    change normalizedOriginCoeffs p r hr d d - monomialSeq d d = 0
    rw [normalizedOriginCoeffs_apply, monomialSeq_apply_same]
    have htop : (r : ℂ) ^ d * lastTaylorCoefficient p d 0 ≠ 0 := by
      have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      exact mul_ne_zero (pow_ne_zero _ hrC)
        ((exactOrderInLastVariable_iff_lastTaylorCoefficients p hp).mp horder).2
    rw [inv_mul_cancel₀ htop, sub_self]

theorem eventually_normalizedPreparation_factorization {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hclose : ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ <
      (1 : ℝ) / 2) :
    ∀ᶠ z in 𝓝 (0 : Base n),
      monomialSeq d = convolution (normalizedPreparationQuotient p r hr d z)
          (analyticNormalizedCoefficientMap p r hr d z) +
        normalizedPreparationRemainder p r hr d z ∧
      seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0 := by
  have hsmall := eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
    (weightedCoefficientSeries p r).sum (originWeightedCoeffs p r hr d)
    (analyticAt_weightedCoefficientSeries_sum p r hr) hclose
  filter_upwards [hsmall] with z hz
  let tail := normalizedPreparationTail p r hr d z
  let q := normalizedPreparationQuotient p r hr d z
  let rem := normalizedPreparationRemainder p r hr d z
  have hz' : ‖tail‖ < 1 := by
    dsimp only [tail]
    rw [normalizedPreparationTail_def]
    exact hz
  have hfac := seqDivisionGlobal_factorization d tail (monomialSeq d) hz'
  have hsupp := seqHighShift_divisionRemainderGlobal d tail (monomialSeq d) hz'
  have hG : analyticNormalizedCoefficientMap p r hr d z = monomialSeq d + tail := by
    dsimp only [tail]
    rw [normalizedPreparationTail_def]
    abel
  have hconv : convolution q (analyticNormalizedCoefficientMap p r hr d z) =
      seqLowShift d q + convolution q tail := by
    rw [hG, convolution_add_right, convolution_monomialSeq]
  refine ⟨?_, ?_⟩
  · rw [hconv]
    simpa only [q, rem, tail, normalizedPreparationQuotient_def,
      normalizedPreparationRemainder_def, add_assoc] using hfac
  · simpa only [rem, tail, normalizedPreparationRemainder_def] using hsupp

theorem normalizedPreparationRemainder_zero {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    normalizedPreparationRemainder p r hr d 0 = 0 := by
  rw [normalizedPreparationRemainder_def, seqDivisionRemainderGlobal_eq d _ _ hsmall]
  apply lp.ext
  funext k
  by_cases hk : k < d
  · rw [seqDivisionRemainder, seqLowCut_apply_of_lt d _ hk]
    change monomialSeq d k - convolution
      (seqDivisionQuotient d (normalizedPreparationTail p r hr d 0) hsmall
        (monomialSeq d)) (normalizedPreparationTail p r hr d 0) k = 0
    rw [monomialSeq_apply_ne (ne_of_lt hk)]
    rw [convolution_apply_eq_zero_of_right (fun j hj ↦
      normalizedPreparationTail_zero_of_le p hp horder r hr0 hr (hj.trans hk.le))]
    exact sub_zero 0
  · rw [seqDivisionRemainder, seqLowCut_apply_of_le d _ (Nat.le_of_not_gt hk)]
    rfl

theorem normalizedPreparationQuotient_zero_apply_zero {n d : ℕ}
    {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    normalizedPreparationQuotient p r hr d 0 0 = 1 := by
  rw [normalizedPreparationQuotient_def, seqDivisionQuotientGlobal_eq d _ _ hsmall]
  have heq := seqDivisionQuotient_equation d
    (normalizedPreparationTail p r hr d 0) hsmall (monomialSeq d)
  have hconv : convolution
      (seqDivisionQuotient d (normalizedPreparationTail p r hr d 0) hsmall
        (monomialSeq d)) (normalizedPreparationTail p r hr d 0) d = 0 := by
    exact convolution_apply_eq_zero_of_right (fun j hj ↦
      normalizedPreparationTail_zero_of_le p hp horder r hr0 hr hj)
  have hcoord := congrArg (fun s : OriginSeq ↦ s 0) heq
  simp only [lp.coeFn_add, Pi.add_apply, seqHighShift_apply, zero_add] at hcoord
  rw [hconv, monomialSeq_apply_same, add_zero] at hcoord
  exact hcoord

/-- Exact order yields a radius and analytic quotient/remainder coefficient
maps with the preparation factorization, vanishing origin remainder, and
unit-normalized origin quotient. -/
theorem exists_normalizedPreparationSequences {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
      AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0 ∧
      AnalyticAt ℂ (normalizedPreparationRemainder p r hr d) 0 ∧
      (∀ᶠ z in 𝓝 (0 : Base n),
        monomialSeq d = convolution (normalizedPreparationQuotient p r hr d z)
            (analyticNormalizedCoefficientMap p r hr d z) +
          normalizedPreparationRemainder p r hr d z ∧
        seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0) ∧
      normalizedPreparationRemainder p r hr d 0 = 0 ∧
      normalizedPreparationQuotient p r hr d 0 0 = 1 := by
  obtain ⟨r, hr, hr0, htop, han, hclose, hevent⟩ :=
    exists_normalizedAnalyticCoefficientMap p hp horder
  have hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1 := by
    rw [normalizedPreparationTail_def]
    exact hclose.trans (by norm_num)
  refine ⟨r, hr, hr0, htop,
    analyticAt_normalizedPreparationQuotient p r hr d hsmall,
    analyticAt_normalizedPreparationRemainder p r hr d hsmall,
    eventually_normalizedPreparation_factorization p r hr hclose,
    normalizedPreparationRemainder_zero p hp horder r hr0 hr hsmall,
    normalizedPreparationQuotient_zero_apply_zero p hp horder r hr0 hr hsmall⟩

end ClassicalComplexWPT
