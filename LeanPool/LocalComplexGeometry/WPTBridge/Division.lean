/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.WPTBridge.DivisionCore

/-!
# Analytic Weierstrass division

This file reconstructs function-level analytic quotients and polynomial
remainders from the sequence-level division operators.
-/

open Filter
open scoped BigOperators ENNReal NNReal Topology

namespace LocalComplexGeometry.WPTBridge

open ClassicalComplexWPT
open DivisionCore

noncomputable section

/-- The analytic quotient reconstructed in the original distinguished variable. -/
def analyticDivisionQuotient {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (x : Ambient n) : ℂ :=
  (((r : ℂ) ^ d)⁻¹) *
    evalL1PowerSeries (quotientSeq p r a x.1) ((r : ℂ)⁻¹ * x.2)

/-- The `i`-th remainder coefficient, rescaled back to the original variable. -/
def analyticDivisionRemainderCoefficient {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (i : Fin d) (z : Base n) : ℂ :=
  remainderSeq p r a z (i : ℕ) * (r : ℂ)⁻¹ ^ (i : ℕ)

theorem analyticAt_analyticDivisionQuotient {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    AnalyticAt ℂ (analyticDivisionQuotient p r a) 0 := by
  have heval := (analyticAt_quotientSeq p r hrp a ha ha0).evalL1PowerSeries
    ((r : ℂ)⁻¹)
  exact analyticAt_const.mul heval

theorem analyticAt_analyticDivisionRemainderCoefficient {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (i : Fin d) :
    AnalyticAt ℂ (analyticDivisionRemainderCoefficient p r a i) 0 := by
  have hrem := analyticAt_remainderSeq p r hrp a ha ha0
  have hcoord : AnalyticAt ℂ (fun z : Base n ↦ remainderSeq p r a z (i : ℕ)) 0 := by
    change AnalyticAt ℂ
      (fun z : Base n ↦ coefficientEval (i : ℕ) (remainderSeq p r a z)) 0
    exact ((coefficientEval (i : ℕ)).analyticAt _).comp hrem
  exact hcoord.mul analyticAt_const

theorem analyticDivision_pointwise {n d : ℕ}
    {h : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr0 : 0 < r)
    (a : Fin d → Base n → ℂ)
    (z : Base n) (w : ℂ)
    (hsmall : ‖preparedTailSeq r d a z‖ < 1)
    (hw : ‖(r : ℂ)⁻¹ * w‖ < 1)
    (hreconstruct :
      evalL1PowerSeries ((weightedCoefficientSeries p r).sum z)
        ((r : ℂ)⁻¹ * w) = h (z, w)) :
    h (z, w) =
      analyticDivisionQuotient p r a (z, w) * preparedPolynomial d a (z, w) +
        ∑ i : Fin d, analyticDivisionRemainderCoefficient p r a i z * w ^ (i : ℕ) := by
  let tail : L1Sequence := preparedTailSeq r d a z
  let dividend : L1Sequence := (weightedCoefficientSeries p r).sum z
  let quotient : L1Sequence := quotientSeq p r a z
  let remainder : L1Sequence := remainderSeq p r a z
  let t : ℂ := (r : ℂ)⁻¹ * w
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hrt : (r : ℂ) * t = w := by
    simp [t, hrC]
  have hseq : dividend =
      seqLowShift d quotient + convolution quotient tail + remainder := by
    simpa only [tail, dividend, quotient, remainder, quotientSeq, remainderSeq,
      divisionInput] using
      seqDivisionGlobal_factorization d (preparedTailSeq r d a z)
        ((weightedCoefficientSeries p r).sum z) hsmall
  have hdivisorSeq :
      seqLowShift d quotient + convolution quotient tail =
        convolution quotient (seqLowShift d constantOneSeq + tail) := by
    rw [← convolution_monomialSeq quotient d, ← seqLowShift_constantOneSeq d,
      convolution_add_right]
  have hquotientEval :
      evalL1PowerSeries (seqLowShift d quotient + convolution quotient tail) t =
        evalL1PowerSeries quotient t * (((r : ℂ) ^ d)⁻¹) *
          preparedPolynomial d a (z, w) := by
    rw [hdivisorSeq, evalL1PowerSeries_convolution _ _ hw,
      eval_preparedPolynomialSeq r hr0 a z hw, hrt]
    ring
  have hremainderSupport : seqHighShift d remainder = 0 := by
    simpa only [tail, dividend, remainder, remainderSeq, divisionInput] using
      seqHighShift_divisionRemainderGlobal d (preparedTailSeq r d a z)
        ((weightedCoefficientSeries p r).sum z) hsmall
  have hremainderEval :
      evalL1PowerSeries remainder t =
        ∑ i : Fin d,
          analyticDivisionRemainderCoefficient p r a i z * w ^ (i : ℕ) := by
    rw [evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero d remainder
      hremainderSupport hw]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [analyticDivisionRemainderCoefficient, remainder]
    rw [mul_pow]
    ring
  calc
    h (z, w) = evalL1PowerSeries dividend t := by
      simpa only [dividend, t] using hreconstruct.symm
    _ = evalL1PowerSeries
        (seqLowShift d quotient + convolution quotient tail + remainder) t := by
      rw [hseq]
    _ = evalL1PowerSeries (seqLowShift d quotient + convolution quotient tail) t +
          evalL1PowerSeries remainder t := by
      rw [evalL1PowerSeries_add_local]
    _ = analyticDivisionQuotient p r a (z, w) *
          preparedPolynomial d a (z, w) +
          ∑ i : Fin d,
            analyticDivisionRemainderCoefficient p r a i z * w ^ (i : ℕ) := by
      rw [hquotientEval, hremainderEval]
      simp only [analyticDivisionQuotient, quotient, t]
      ring

/--
Fixed-radius analytic Weierstrass division by a prepared polynomial.  The
radius and ambient power-series witness remain explicit so downstream germ
bridges can reuse the constructed quotient and remainder functions.
-/
theorem analyticWeierstrassDivision_fixedRadius {n d : ℕ}
    {h : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt h p 0)
    (r : ℝ≥0) (hr0 : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius)
    (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    AnalyticAt ℂ (analyticDivisionQuotient p r a) 0 ∧
      (∀ i, AnalyticAt ℂ (analyticDivisionRemainderCoefficient p r a i) 0) ∧
      h =ᶠ[𝓝 0] fun x ↦
        analyticDivisionQuotient p r a x * preparedPolynomial d a x +
          ∑ i : Fin d,
            analyticDivisionRemainderCoefficient p r a i x.1 * x.2 ^ (i : ℕ) := by
  refine ⟨analyticAt_analyticDivisionQuotient p r hrp a ha ha0,
    fun i ↦ analyticAt_analyticDivisionRemainderCoefficient p r hrp a ha ha0 i, ?_⟩
  have hsmallBase : ∀ᶠ z in 𝓝 (0 : Base n), ‖preparedTailSeq r d a z‖ < 1 :=
    eventually_norm_preparedTailSeq_lt_one r a ha ha0
  have hsmall : ∀ᶠ x in 𝓝 (0 : Ambient n),
      ‖preparedTailSeq r d a x.1‖ < 1 := by
    exact (continuousAt_fst : ContinuousAt (fun x : Ambient n ↦ x.1) 0).eventually
      hsmallBase
  have hw : ∀ᶠ x in 𝓝 (0 : Ambient n), ‖(r : ℂ)⁻¹ * x.2‖ < 1 := by
    have hc : ContinuousAt (fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0 := by
      fun_prop
    have hb := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
    have hb' : Metric.ball (0 : ℂ) 1 ∈
        𝓝 ((fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0) := by
      simpa [ambient_zero_eq] using hb
    have he := hc.eventually hb'
    simpa only [Metric.mem_ball, dist_zero_right] using he
  have hreconstruct :=
    eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
      p r hp hr0 hrp
  filter_upwards [hsmall, hw, hreconstruct] with x hxsmall hxw hxreconstruct
  simpa using analyticDivision_pointwise p r hr0 a x.1 x.2 hxsmall hxw hxreconstruct

/--
Arbitrary-dividend analytic Weierstrass division.  This is the function-level
adapter missing from the pinned WPT public surface: it returns an analytic
quotient and analytic coefficients of a remainder of distinguished degree
strictly below `d`.
-/
theorem exists_analyticWeierstrassDivision {n d : ℕ}
    (h : Ambient n → ℂ) (hh : AnalyticAt ℂ h 0)
    (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    ∃ (q : Ambient n → ℂ) (remainder : Fin d → Base n → ℂ),
      AnalyticAt ℂ q 0 ∧
      (∀ i, AnalyticAt ℂ (remainder i) 0) ∧
      h =ᶠ[𝓝 0] fun x ↦
        q x * preparedPolynomial d a x +
          ∑ i : Fin d, remainder i x.1 * x.2 ^ (i : ℕ) := by
  obtain ⟨p, hp⟩ := hh
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos with ⟨r, hr0E, hrp⟩
  have hr0 : 0 < r := by exact_mod_cast hr0E
  let q : Ambient n → ℂ := analyticDivisionQuotient p r a
  let remainder : Fin d → Base n → ℂ :=
    fun i ↦ analyticDivisionRemainderCoefficient p r a i
  have hdivision := analyticWeierstrassDivision_fixedRadius p hp r hr0 hrp a ha ha0
  exact ⟨q, remainder, hdivision.1, hdivision.2.1, hdivision.2.2⟩

end

end LocalComplexGeometry.WPTBridge
