/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.PreparationSequences
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedEvaluation
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1PolynomialEvaluation
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedGermEvaluation

/-!
# Public existence from analytic sequence preparation

This file reconstructs the public analytic unit and distinguished polynomial
from the normalized `ℓ¹(ℕ)` quotient/remainder supplied by
`PreparationSequences`.
-/

open Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace ClassicalComplexWPT

@[simp] theorem evalL1PowerSeries_zero (a : L1Sequence) :
    evalL1PowerSeries a 0 = a 0 := by
  rw [evalL1PowerSeries_eq_tsum a (by norm_num)]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

theorem evalL1PowerSeries_add (a b : L1Sequence) (w : ℂ) :
    evalL1PowerSeries (a + b) w =
      evalL1PowerSeries a w + evalL1PowerSeries b w := by
  change l1EvalOperator w (a + b) = _
  exact map_add (l1EvalOperator w) a b

lemma weighted_scaled_pow (r : ℂ) (hr : r ≠ 0) {d i : ℕ} (hi : i ≤ d)
    (w : ℂ) :
    r ^ (d - i) * w ^ i = r ^ d * (r⁻¹ * w) ^ i := by
  rw [pow_sub₀ r hr hi, mul_pow, inv_pow]
  ring

/-- Lower coefficients of the reconstructed distinguished polynomial. -/
noncomputable def preparationCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) (i : Fin d) : Base n → ℂ :=
  fun z ↦ -((r : ℂ) ^ (d - (i : ℕ))) * normalizedPreparationRemainder p r hr d z i

/-- Evaluation of the normalized division quotient in the original
distinguished variable. -/
noncomputable def preparationQuotientEval {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Ambient n → ℂ :=
  fun x ↦ evalL1PowerSeries (normalizedPreparationQuotient p r hr d x.1)
    ((r : ℂ)⁻¹ * x.2)

/-- The reconstructed analytic unit. -/
noncomputable def preparationUnit {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Ambient n → ℂ :=
  fun x ↦ (originWeightedCoeffs p r hr d * (r : ℂ)⁻¹ ^ d) *
    (preparationQuotientEval p r hr d x)⁻¹

theorem analyticAt_preparationCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hq : AnalyticAt ℂ (normalizedPreparationRemainder p r hr d) 0)
    (i : Fin d) : AnalyticAt ℂ (preparationCoefficient p r hr d i) 0 := by
  have hi : AnalyticAt ℂ (fun z : Base n ↦ normalizedPreparationRemainder p r hr d z i) 0 :=
    by
      change AnalyticAt ℂ
        (fun z : Base n ↦ coefficientEval (i : ℕ)
          (normalizedPreparationRemainder p r hr d z)) 0
      simpa [Function.comp_def] using
        ((coefficientEval (i : ℕ)).analyticAt _).comp hq
  exact analyticAt_const.mul hi

theorem preparationCoefficient_zero {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hrem : normalizedPreparationRemainder p r hr d 0 = 0)
    (i : Fin d) : preparationCoefficient p r hr d i 0 = 0 := by
  simp [preparationCoefficient, hrem]

theorem preparedPolynomial_preparationCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) (hr0 : 0 < r)
    (z : Base n) (w : ℂ) :
    preparedPolynomial d (preparationCoefficient p r hr d) (z, w) =
      (r : ℂ) ^ d *
        ((r : ℂ)⁻¹ ^ d * w ^ d -
          ∑ i : Fin d, normalizedPreparationRemainder p r hr d z i *
            ((r : ℂ)⁻¹ * w) ^ (i : ℕ)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hrpow : (r : ℂ) ^ d * (r : ℂ)⁻¹ ^ d = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hrC, one_pow]
  have hlead : (r : ℂ) ^ d * ((r : ℂ)⁻¹ ^ d * w ^ d) = w ^ d := by
    rw [← mul_assoc, hrpow, one_mul]
  rw [preparedPolynomial]
  simp only [preparationCoefficient]
  rw [mul_sub, hlead, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hs := weighted_scaled_pow (r : ℂ) hrC i.isLt.le w
  calc
    (-((r : ℂ) ^ (d - (i : ℕ))) *
          normalizedPreparationRemainder p r hr d z i) * w ^ (i : ℕ) =
        -(normalizedPreparationRemainder p r hr d z i *
          ((r : ℂ) ^ (d - (i : ℕ)) * w ^ (i : ℕ))) := by ring
    _ = -(normalizedPreparationRemainder p r hr d z i *
          ((r : ℂ) ^ d * ((r : ℂ)⁻¹ * w) ^ (i : ℕ))) := by rw [hs]
    _ = -((r : ℂ) ^ d *
          (normalizedPreparationRemainder p r hr d z i *
            ((r : ℂ)⁻¹ * w) ^ (i : ℕ))) := by ring

theorem analyticAt_preparationQuotientEval {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hq : AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0) :
    AnalyticAt ℂ (preparationQuotientEval p r hr d) 0 := by
  exact ClassicalComplexWPT.AnalyticAt.evalL1PowerSeries hq (r : ℂ)⁻¹

theorem preparationQuotientEval_zero {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    preparationQuotientEval p r hr d 0 =
      normalizedPreparationQuotient p r hr d 0 0 := by
  simp [preparationQuotientEval, ambient_zero_eq]

theorem analyticAt_preparationUnit {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hq : AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0)
    (hq0 : normalizedPreparationQuotient p r hr d 0 0 = 1) :
    AnalyticAt ℂ (preparationUnit p r hr d) 0 := by
  have hQ := analyticAt_preparationQuotientEval p r hr d hq
  have hQ0 : preparationQuotientEval p r hr d 0 ≠ 0 := by
    rw [preparationQuotientEval_zero, hq0]
    exact one_ne_zero
  exact analyticAt_const.mul (hQ.inv hQ0)

theorem preparationUnit_zero_ne {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hr0 : 0 < r) (htop : originWeightedCoeffs p r hr d ≠ 0)
    (hq0 : normalizedPreparationQuotient p r hr d 0 0 = 1) :
    preparationUnit p r hr d 0 ≠ 0 := by
  rw [preparationUnit, preparationQuotientEval_zero, hq0, inv_one, mul_one]
  exact mul_ne_zero htop (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hr0.ne')))

/-- Pointwise reconstruction once sequence division and convergence are
available.  Keeping the convergence hypotheses explicit makes this lemma
reusable for both the public existence and uniqueness arguments. -/
theorem preparation_factorization_of_sequence_factorization {n d : ℕ}
    {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (hr0 : 0 < r)
    (htop : originWeightedCoeffs p r hr d ≠ 0)
    (z : Base n) (w : ℂ)
    (hfac : monomialSeq d =
      convolution (normalizedPreparationQuotient p r hr d z)
        (analyticNormalizedCoefficientMap p r hr d z) +
          normalizedPreparationRemainder p r hr d z)
    (hsupp : seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0)
    (hw : ‖(r : ℂ)⁻¹ * w‖ < 1)
    (hrecon : evalL1PowerSeries ((weightedCoefficientSeries p r).sum z)
        ((r : ℂ)⁻¹ * w) = f (z, w))
    (hQne : preparationQuotientEval p r hr d (z, w) ≠ 0) :
    f (z, w) = preparationUnit p r hr d (z, w) *
      preparedPolynomial d (preparationCoefficient p r hr d) (z, w) := by
  let t : ℂ := (r : ℂ)⁻¹ * w
  let q : OriginSeq := normalizedPreparationQuotient p r hr d z
  let rem : OriginSeq := normalizedPreparationRemainder p r hr d z
  let C : OriginSeq := (weightedCoefficientSeries p r).sum z
  let D : ℂ := originWeightedCoeffs p r hr d
  have hD : D ≠ 0 := htop
  have hEvalFac := congrArg (fun a : OriginSeq ↦ evalL1PowerSeries a t) hfac
  have hG : analyticNormalizedCoefficientMap p r hr d z = D⁻¹ • C := rfl
  have hseries :
      t ^ d = evalL1PowerSeries q t * (D⁻¹ * evalL1PowerSeries C t) +
        ∑ i : Fin d, rem i * t ^ (i : ℕ) := by
    rw [evalL1PowerSeries_monomialSeq d hw, evalL1PowerSeries_add,
      evalL1PowerSeries_convolution _ _ hw, hG, evalL1PowerSeries_smul,
      evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero d rem hsupp hw] at hEvalFac
    simpa only [q, rem] using hEvalFac
  rw [preparedPolynomial_preparationCoefficient p r hr d hr0 z w]
  rw [← hrecon]
  simp only [preparationUnit, preparationQuotientEval]
  rw [← mul_pow]
  change evalL1PowerSeries C t =
    (D * (r : ℂ)⁻¹ ^ d) * (evalL1PowerSeries q t)⁻¹ *
      ((r : ℂ) ^ d * (t ^ d - ∑ i : Fin d, rem i * t ^ (i : ℕ)))
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hQ : evalL1PowerSeries q t ≠ 0 := hQne
  let R : ℂ := ∑ i : Fin d, rem i * t ^ (i : ℕ)
  calc
    evalL1PowerSeries C t =
        D * (evalL1PowerSeries q t)⁻¹ * (t ^ d - R) := by
      rw [hseries]
      field_simp [hD, hQ]
      ring
    _ = (D * (r : ℂ)⁻¹ ^ d) * (evalL1PowerSeries q t)⁻¹ *
        ((r : ℂ) ^ d * (t ^ d - R)) := by
      have hrpow : (r : ℂ) ^ d * (r : ℂ)⁻¹ ^ d = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hrC, one_pow]
      calc
        D * (evalL1PowerSeries q t)⁻¹ * (t ^ d - R) =
            D * (evalL1PowerSeries q t)⁻¹ * (1 * (t ^ d - R)) := by rw [one_mul]
        _ = _ := by rw [← hrpow]; ring

/-- The existence half of classical complex Weierstrass preparation, in the
exact public predicate. -/
theorem exists_isWeierstrassPreparation {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f d a u := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨r, hr, hr0, htop, hq, hrem, hfac, hrem0, hq0⟩ :=
    exists_normalizedPreparationSequences p hp horder
  let a : Fin d → Base n → ℂ := preparationCoefficient p r hr d
  let u : Ambient n → ℂ := preparationUnit p r hr d
  refine ⟨a, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact analyticAt_preparationCoefficient p r hr d hrem i
  · intro i
    exact preparationCoefficient_zero p r hr d hrem0 i
  · exact analyticAt_preparationUnit p r hr d hq hq0
  · exact preparationUnit_zero_ne p r hr d hr0 htop hq0
  · have hfac' : ∀ᶠ x : Ambient n in 𝓝 0,
        monomialSeq d = convolution (normalizedPreparationQuotient p r hr d x.1)
            (analyticNormalizedCoefficientMap p r hr d x.1) +
              normalizedPreparationRemainder p r hr d x.1 ∧
        seqHighShift d (normalizedPreparationRemainder p r hr d x.1) = 0 :=
      (continuousAt_fst : ContinuousAt (fun x : Ambient n ↦ x.1) 0).eventually hfac
    have hrecon :=
      eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
        p r hp hr0 hr
    have hscaled : ∀ᶠ x : Ambient n in 𝓝 0, ‖(r : ℂ)⁻¹ * x.2‖ < 1 := by
      have hc : ContinuousAt (fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0 := by
        fun_prop
      have hb := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
      have hb' : Metric.ball (0 : ℂ) 1 ∈
          nhds ((fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0) := by
        simpa [ambient_zero_eq] using hb
      have he := hc.eventually hb'
      simpa only [Metric.mem_ball, dist_zero_right] using he
    have hQne : ∀ᶠ x : Ambient n in 𝓝 0,
        preparationQuotientEval p r hr d x ≠ 0 := by
      have hQa := analyticAt_preparationQuotientEval p r hr d hq
      apply hQa.continuousAt.eventually_ne
      rw [preparationQuotientEval_zero, hq0]
      exact one_ne_zero
    filter_upwards [hfac', hrecon, hscaled, hQne] with x hx hrec hxw hxQ
    simpa only [a, u] using
      preparation_factorization_of_sequence_factorization p r hr hr0 htop
        x.1 x.2 hx.1 hx.2 hxw hrec hxQ

end ClassicalComplexWPT
