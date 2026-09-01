/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1Division
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1PowerSeries
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Basic
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1PolynomialEvaluation
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.PreparationSequences
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The algebraic uniqueness layer for Weierstrass preparation

The analytic preparation proof eventually reduces, at every nearby base point,
to division in the weighted coefficient algebra `ℓ¹(ℕ)`.  This file records the
precise uniqueness consequences of the division theorem, independently of the
construction of the analytic coefficient maps.

The important application has two normal-form decompositions of the same
coefficient sequence with respect to `w^d + p`:

* the quotient is the weighted coefficient sequence of the ratio of two units
  and the remainder is zero;
* the quotient is the constant sequence `1` and the remainder is the
  difference of the two prepared polynomials.

Since both remainders are supported in degrees below `d`, uniqueness of
division identifies both the quotient and the remainder.
-/

open Filter
open scoped ENNReal NNReal Topology

noncomputable section


namespace ClassicalComplexWPT

/-- The coefficient sequence of the constant power series `1`. -/
noncomputable def constantOneSeq : L1Coeff ℕ := lp.single 1 0 1

@[simp] theorem constantOneSeq_apply (k : ℕ) :
    constantOneSeq k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [constantOneSeq, lp.single_apply]
  · simp [constantOneSeq, lp.single_apply, hk]

/-- The constant sequence is the multiplicative identity for Cauchy
convolution. -/
@[simp] theorem convolution_constantOneSeq (q : L1Coeff ℕ) :
    convolution constantOneSeq q = q := by
  apply lp.ext
  funext n
  rw [convolution_apply]
  simp only [constantOneSeq_apply]
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    have hi : i ≠ 0 := by
      intro hi
      subst i
      have hj : j = n := by simpa using Finset.mem_antidiagonal.mp hij
      exact hne (Prod.ext rfl hj)
    simp [hi]
  · simp

/-- The normalized weighted low-degree tail of a prepared polynomial.  Its
`i`-th coordinate is `r^i / r^d * a_i(z)`; adding the shifted constant
sequence gives the coefficients of `r^{-d} P(z,rw)`. -/
noncomputable def preparedTailSeq {n : ℕ} (r : ℝ≥0) (d : ℕ)
    (a : Fin d → Base n → ℂ) (z : Base n) : L1Sequence :=
  ∑ i : Fin d, (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) •
    lp.single 1 (i : ℕ) (a i z)

@[simp] theorem preparedTailSeq_apply_fin {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) (i : Fin d) :
    preparedTailSeq r d a z (i : ℕ) =
      (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) * a i z := by
  classical
  change (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ))
    (∑ j : Fin d, (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (j : ℕ)) •
      lp.single 1 (j : ℕ) (a j z)) = _
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul]
    change (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) *
      ((lp.single 1 (i : ℕ) (a i z) : L1Sequence) (i : ℕ)) = _
    rw [lp.single_apply_self]
  · intro j hj hji
    have hval : (j : ℕ) ≠ (i : ℕ) := by
      exact fun h ↦ hji (Fin.ext h)
    rw [map_smul]
    change _ * ((lp.single 1 (j : ℕ) (a j z) : L1Sequence) (i : ℕ)) = 0
    have hs : ((lp.single 1 (j : ℕ) (a j z) : L1Sequence) (i : ℕ)) = 0 :=
      lp.single_apply_ne (E := fun _ : ℕ ↦ ℂ) 1 (j : ℕ) (a j z) hval.symm
    rw [hs, mul_zero]
  · simp

/-- Prepared tails have no coefficients in degrees at least `d`. -/
@[simp] theorem seqHighShift_preparedTailSeq {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) :
    seqHighShift d (preparedTailSeq r d a z) = 0 := by
  classical
  apply lp.ext
  funext k
  change (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 (k + d))
    (∑ i : Fin d, (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) •
      lp.single 1 (i : ℕ) (a i z)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : (i : ℕ) ≠ k + d := by omega
  rw [map_smul]
  change _ * ((lp.single 1 (i : ℕ) (a i z) : L1Sequence) (k + d)) = 0
  have hs : ((lp.single 1 (i : ℕ) (a i z) : L1Sequence) (k + d)) = 0 :=
    lp.single_apply_ne (E := fun _ : ℕ ↦ ℂ) 1 (i : ℕ) (a i z) hne.symm
  rw [hs, mul_zero]

/-- The prepared tail varies analytically with the base point. -/
theorem analyticAt_preparedTailSeq {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (preparedTailSeq r d a) 0 := by
  classical
  have hsum : AnalyticAt ℂ
      (∑ i : Fin d, fun z ↦ (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) •
        (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ)) (a i z)) 0 := by
    apply Finset.univ.analyticAt_sum
    intro i hi
    let single : ℂ →L[ℂ] L1Sequence :=
      lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ)
    have hs : AnalyticAt ℂ (fun z ↦ single (a i z)) 0 :=
      (single.analyticAt (a i 0)).comp (f := a i) (ha i)
    have hscaled : AnalyticAt ℂ
        (((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) •
          (fun z ↦ single (a i z))) 0 := hs.const_smul
    have heq : (((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) •
          (fun z ↦ single (a i z))) =
        (fun z ↦ ((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) • single (a i z)) := by
      rfl
    change AnalyticAt ℂ
      (fun z ↦ ((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) • single (a i z)) 0
    rw [← heq]
    exact hscaled
  change AnalyticAt ℂ (fun z ↦ preparedTailSeq r d a z) 0
  have heq : (fun z ↦ preparedTailSeq r d a z) =
      ∑ i : Fin d, fun z ↦ (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) •
        (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ)) (a i z) := by
    funext z
    simp only [preparedTailSeq, Finset.sum_apply,
      lp.singleContinuousLinearMap_apply]
  rw [heq]
  exact hsum

/-- Since all prepared coefficients vanish at the base origin, every fixed
positive weighted tail is small on a sufficiently small base neighborhood. -/
theorem eventually_norm_preparedTailSeq_lt_one {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0) :
    ∀ᶠ z in nhds (0 : Base n), ‖preparedTailSeq r d a z‖ < 1 := by
  have hzero : preparedTailSeq r d a 0 = 0 := by
    classical
    unfold preparedTailSeq
    simp [ha0]
  have hcont := (analyticAt_preparedTailSeq r a ha).continuousAt
  have hopen : Metric.ball (0 : L1Sequence) 1 ∈
      nhds (preparedTailSeq r d a 0) := by
    rw [hzero]
    exact Metric.isOpen_ball.mem_nhds (by simp)
  filter_upwards [hcont.eventually hopen] with z hz
  simpa [Metric.mem_ball, dist_zero_right] using hz

/-- Equality of normalized prepared tails recovers equality of every
coefficient when the weight is positive. -/
theorem preparedTailSeq_eq_iff {n d : ℕ} {r : ℝ≥0} (hr : 0 < r)
    (a a' : Fin d → Base n → ℂ) (z : Base n) :
    preparedTailSeq r d a z = preparedTailSeq r d a' z ↔
      ∀ i, a i z = a' i z := by
  constructor
  · intro h i
    have hi := congrArg (fun q : L1Sequence ↦ q (i : ℕ)) h
    rw [preparedTailSeq_apply_fin, preparedTailSeq_apply_fin] at hi
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hc : (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) ≠ 0 :=
      mul_ne_zero (inv_ne_zero (pow_ne_zero _ hrC)) (pow_ne_zero _ hrC)
    exact mul_left_cancel₀ hc hi
  · intro h
    unfold preparedTailSeq
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i]

theorem seqLowShift_constantOneSeq (d : ℕ) :
    seqLowShift d constantOneSeq = monomialSeq d := by
  rw [← convolution_monomialSeq constantOneSeq d, convolution_constantOneSeq]

theorem evalL1PowerSeries_add_local (a b : L1Sequence) (w : ℂ) :
    evalL1PowerSeries (a + b) w =
      evalL1PowerSeries a w + evalL1PowerSeries b w := by
  change l1EvalOperator w (a + b) = _
  exact map_add _ _ _

/-- Evaluation of the normalized prepared-polynomial coefficient sequence. -/
theorem eval_preparedPolynomialSeq {n d : ℕ} (r : ℝ≥0) (hr : 0 < r)
    (a : Fin d → Base n → ℂ) (z : Base n) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (seqLowShift d constantOneSeq + preparedTailSeq r d a z) w =
      (((r : ℂ) ^ d)⁻¹) * preparedPolynomial d a (z, (r : ℂ) * w) := by
  rw [evalL1PowerSeries_add_local, seqLowShift_constantOneSeq,
    evalL1PowerSeries_monomialSeq d hw]
  rw [evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero d _
    (seqHighShift_preparedTailSeq r a z) hw]
  rw [preparedPolynomial]
  simp only [preparedTailSeq_apply_fin, mul_pow]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hrC), one_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The analytic function on the unit disc represented by an `ℓ¹` sequence
determines every coefficient.  The hypothesis is stated as germ equality,
which is exactly what is available after shrinking the common analytic
neighborhood in preparation uniqueness. -/
theorem eq_of_evalL1PowerSeries_eventuallyEq (a b : L1Sequence)
    (h : (fun w ↦ evalL1PowerSeries a w) =ᶠ[nhds 0]
      (fun w ↦ evalL1PowerSeries b w)) : a = b := by
  let appA : (L1Sequence →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ a
  let appB : (L1Sequence →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ b
  let pA : FormalMultilinearSeries ℂ ℂ ℂ :=
    appA.compFormalMultilinearSeries l1OperatorSeries
  let pB : FormalMultilinearSeries ℂ ℂ ℂ :=
    appB.compFormalMultilinearSeries l1OperatorSeries
  have hrad : (0 : ℝ≥0∞) < l1OperatorSeries.radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le one_le_radius_l1OperatorSeries
  have hA : HasFPowerSeriesAt (fun w ↦ evalL1PowerSeries a w) pA 0 := by
    have hball := appA.comp_hasFPowerSeriesOnBall
      (l1OperatorSeries.hasFPowerSeriesOnBall hrad)
    exact hball.hasFPowerSeriesAt.congr (by
      filter_upwards
      intro w
      rfl)
  have hB : HasFPowerSeriesAt (fun w ↦ evalL1PowerSeries b w) pB 0 := by
    have hball := appB.comp_hasFPowerSeriesOnBall
      (l1OperatorSeries.hasFPowerSeriesOnBall hrad)
    exact hball.hasFPowerSeriesAt.congr (by
      filter_upwards
      intro w
      rfl)
  have hp : pA = pB := hA.eq_formalMultilinearSeries_of_eventually hB h
  apply lp.ext
  funext k
  have hk := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p k (fun _ ↦ (1 : ℂ))) hp
  simpa [pA, pB, appA, appB, l1OperatorSeries, coefficientEval, lp.evalCLM,
    ContinuousLinearMap.compFormalMultilinearSeries_apply] using hk

/-- Any two quotient/remainder decompositions for the same small normalized
divisor agree.  This is the form of `seqDivision_existsUnique` used by germ
uniqueness. -/
theorem seqDivision_factorizations_unique (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f q₁ r₁ q₂ r₂ : L1Coeff ℕ)
    (hfac₁ : f = seqLowShift d q₁ + convolution q₁ p + r₁)
    (hr₁ : seqHighShift d r₁ = 0)
    (hfac₂ : f = seqLowShift d q₂ + convolution q₂ p + r₂)
    (hr₂ : seqHighShift d r₂ = 0) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have hq₁ : q₁ = seqDivisionQuotient d p hp f :=
    seqDivisionQuotient_unique d p hp f q₁ r₁ hfac₁ hr₁
  have hq₂ : q₂ = seqDivisionQuotient d p hp f :=
    seqDivisionQuotient_unique d p hp f q₂ r₂ hfac₂ hr₂
  have hq : q₁ = q₂ := hq₁.trans hq₂.symm
  refine ⟨hq, ?_⟩
  have hfac₁' : f = seqLowShift d q₂ + convolution q₂ p + r₁ := by
    simpa only [hq] using hfac₁
  have hsum : (seqLowShift d q₂ + convolution q₂ p) + r₁ =
      (seqLowShift d q₂ + convolution q₂ p) + r₂ := by
    simpa only [add_assoc] using hfac₁'.symm.trans hfac₂
  exact add_left_cancel hsum

/-- Specialized two-factorization principle used in preparation uniqueness:
if one decomposition has zero remainder and another has a low-degree
remainder, then the quotients agree and that remainder vanishes. -/
theorem seqDivision_zero_remainder_unique (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f q q' r : L1Coeff ℕ)
    (hfac : f = seqLowShift d q + convolution q p)
    (hfac' : f = seqLowShift d q' + convolution q' p + r)
    (hr : seqHighShift d r = 0) :
    q = q' ∧ r = 0 := by
  have hz : seqHighShift d (0 : L1Coeff ℕ) = 0 := by
    apply lp.ext
    funext k
    rfl
  have hfac₀ : f = seqLowShift d q + convolution q p + (0 : L1Coeff ℕ) := by
    simpa using hfac
  have h := seqDivision_factorizations_unique d p hp f q 0 q' r hfac₀ hz hfac' hr
  exact ⟨h.1, h.2.symm⟩

/-- Abstract uniqueness of a prepared polynomial.  Here `p` and `p'` are the
low-degree tails of two monic degree-`d` polynomials, while `v` is the
coefficient sequence of the ratio of their analytic units.  The displayed
identity says `(w^d + p) = v * (w^d + p')` in weighted coefficients.

This theorem is deliberately independent of how the coefficient sequences
were extracted from analytic germs. -/
theorem seqPreparedPolynomial_unique (d : ℕ) (p p' v : L1Coeff ℕ)
    (hp' : ‖p'‖ < 1)
    (hpLow : seqHighShift d p = 0)
    (hp'Low : seqHighShift d p' = 0)
    (hfactor :
      seqLowShift d constantOneSeq + p =
        seqLowShift d v + convolution v p') :
    p = p' ∧ v = constantOneSeq := by
  let f := seqLowShift d constantOneSeq + p
  have hfacRatio : f = seqLowShift d v + convolution v p' := hfactor
  have hfacOne : f =
      seqLowShift d constantOneSeq + convolution constantOneSeq p' + (p - p') := by
    dsimp only [f]
    rw [convolution_constantOneSeq]
    abel
  have hremLow : seqHighShift d (p - p') = 0 := by
    change seqHighShiftCLM d (p - p') = 0
    rw [map_sub]
    change seqHighShift d p - seqHighShift d p' = 0
    rw [hpLow, hp'Low, sub_self]
  have huniq := seqDivision_zero_remainder_unique d p' hp' f v constantOneSeq
    (p - p') hfacRatio hfacOne hremLow
  refine ⟨?_, huniq.1⟩
  exact sub_eq_zero.mp huniq.2

/-- Evaluation-level form of `seqPreparedPolynomial_unique`.  This avoids any
need for a multivariable uniqueness theorem: after fixing the base point, the
ordinary one-variable uniqueness theorem identifies the two `ℓ¹` coefficient
sequences. -/
theorem seqPreparedPolynomial_unique_of_eventually_eval (d : ℕ)
    (p p' v : L1Coeff ℕ)
    (hp' : ‖p'‖ < 1)
    (hpLow : seqHighShift d p = 0)
    (hp'Low : seqHighShift d p' = 0)
    (heval :
      (fun w ↦ evalL1PowerSeries (seqLowShift d constantOneSeq + p) w) =ᶠ[nhds 0]
        (fun w ↦ evalL1PowerSeries
          (seqLowShift d v + convolution v p') w)) :
    p = p' ∧ v = constantOneSeq := by
  have hfactor :
      seqLowShift d constantOneSeq + p =
        seqLowShift d v + convolution v p' :=
    eq_of_evalL1PowerSeries_eventuallyEq _ _ heval
  exact seqPreparedPolynomial_unique d p p' v hp' hpLow hp'Low hfactor

/-- Full germ uniqueness of Weierstrass preparation witnesses. -/
theorem isWeierstrassPreparation_unique {n d : ℕ} {f : Ambient n → ℂ}
    {a a' : Fin d → Base n → ℂ} {u u' : Ambient n → ℂ}
    (h : IsWeierstrassPreparation f d a u)
    (h' : IsWeierstrassPreparation f d a' u') :
    (∀ i, a i =ᶠ[nhds 0] a' i) ∧ u =ᶠ[nhds 0] u' := by
  rcases h with ⟨ha, ha0, hu, hu0, hfu⟩
  rcases h' with ⟨ha', ha0', hu', hu0', hfu'⟩
  let v : Ambient n → ℂ := fun x ↦ u' x * (u x)⁻¹
  have hv : AnalyticAt ℂ v 0 := by
    exact hu'.mul (hu.inv hu0)
  obtain ⟨pv, hpv⟩ := hv
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hpv.radius_pos with ⟨r, hr0E, hrp⟩
  have hr0 : 0 < r := by exact_mod_cast hr0E
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  let V : Base n → L1Sequence := (weightedCoefficientSeries pv r).sum
  have hVrecon :
      (fun x : Ambient n ↦ evalL1PowerSeries (V x.1) ((r : ℂ)⁻¹ * x.2))
        =ᶠ[nhds 0] v := by
    exact eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
      pv r hpv hr0 hrp
  have hu_ne : ∀ᶠ x in nhds (0 : Ambient n), u x ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  have hpoly :
      (fun x : Ambient n ↦ preparedPolynomial d a x) =ᶠ[nhds 0]
        (fun x ↦ v x * preparedPolynomial d a' x) := by
    filter_upwards [hfu, hfu', hu_ne] with x hx hx' hux
    have heq : u x * preparedPolynomial d a x =
        u' x * preparedPolynomial d a' x := hx.symm.trans hx'
    dsimp only [v]
    apply (mul_left_cancel₀ hux)
    rw [heq]
    field_simp [hux]
  let S : Ambient n → Ambient n := fun x ↦ (x.1, (r : ℂ) * x.2)
  have hS : Tendsto S (nhds 0) (nhds 0) := by
    have hc : ContinuousAt S 0 := by
      dsimp only [S]
      fun_prop
    simpa [S, ambient_zero_eq] using hc.tendsto
  have hpolyS := hpoly.comp_tendsto hS
  have hVreconS := hVrecon.comp_tendsto hS
  have hpolyCurry := hpolyS.curry_nhds
  have hVCurry := hVreconS.curry_nhds
  have hsmall := eventually_norm_preparedTailSeq_lt_one r a' ha' ha0'
  have hbase : ∀ᶠ z in nhds (0 : Base n),
      preparedTailSeq r d a z = preparedTailSeq r d a' z ∧
        V z = constantOneSeq := by
    filter_upwards [hpolyCurry, hVCurry, hsmall] with z hzpoly hzV hzsmall
    have heval :
        (fun w ↦ evalL1PowerSeries
          (seqLowShift d constantOneSeq + preparedTailSeq r d a z) w) =ᶠ[nhds 0]
          (fun w ↦ evalL1PowerSeries
            (seqLowShift d (V z) + convolution (V z) (preparedTailSeq r d a' z)) w) := by
      have hunit : ∀ᶠ w : ℂ in nhds 0, ‖w‖ < 1 := by
        have hb := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
        filter_upwards [hb] with w hw
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      filter_upwards [hzpoly, hzV, hunit] with w hwpoly hwV hw
      have hwV' : evalL1PowerSeries (V z) w = v (z, (r : ℂ) * w) := by
        simpa [V, S, hrC] using hwV
      change preparedPolynomial d a (z, (r : ℂ) * w) =
        v (z, (r : ℂ) * w) * preparedPolynomial d a' (z, (r : ℂ) * w) at hwpoly
      have hright : evalL1PowerSeries
          (seqLowShift d (V z) + convolution (V z) (preparedTailSeq r d a' z)) w =
          evalL1PowerSeries (V z) w *
            evalL1PowerSeries
              (seqLowShift d constantOneSeq + preparedTailSeq r d a' z) w := by
        rw [← evalL1PowerSeries_convolution _ _ hw]
        congr 1
        rw [convolution_add_right, seqLowShift_constantOneSeq,
          convolution_monomialSeq]
      rw [eval_preparedPolynomialSeq r hr0 a z hw,
        hright, eval_preparedPolynomialSeq r hr0 a' z hw, hwV']
      rw [hwpoly]
      ring
    exact seqPreparedPolynomial_unique_of_eventually_eval d
      (preparedTailSeq r d a z) (preparedTailSeq r d a' z) (V z)
      hzsmall (seqHighShift_preparedTailSeq r a z)
      (seqHighShift_preparedTailSeq r a' z) heval
  refine ⟨?_, ?_⟩
  · intro i
    filter_upwards [hbase] with z hz
    exact (preparedTailSeq_eq_iff hr0 a a' z).mp hz.1 i
  · have hVbase : ∀ᶠ x : Ambient n in nhds 0, V x.1 = constantOneSeq :=
      by
        have hfst : Tendsto (fun x : Ambient n ↦ x.1) (nhds 0) (nhds 0) := by
          simpa using
            (continuousAt_fst.tendsto : Tendsto (fun x : Ambient n ↦ x.1)
              (nhds 0) (nhds ((0 : Ambient n).1)))
        exact hfst.eventually (hbase.mono fun z hz ↦ hz.2)
    have hscaled : ∀ᶠ x : Ambient n in nhds 0, ‖(r : ℂ)⁻¹ * x.2‖ < 1 := by
      have hc : ContinuousAt (fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0 := by
        fun_prop
      have hc' : Tendsto (fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2)
          (nhds 0) (nhds 0) := by simpa [ambient_zero_eq] using hc.tendsto
      have he := hc'.eventually
        (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
      filter_upwards [he] with x hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    filter_upwards [hVrecon, hVbase, hscaled, hu_ne] with x hxV hxone hxw hux
    have hone : evalL1PowerSeries constantOneSeq ((r : ℂ)⁻¹ * x.2) = 1 := by
      rw [evalL1PowerSeries_eq_tsum _ hxw, tsum_eq_single 0]
      · simp [constantOneSeq_apply]
      · intro k hk
        simp [constantOneSeq_apply, hk]
    have hvone : v x = 1 := by
      rw [← hxV, hxone, hone]
    dsimp only [v] at hvone
    rw [← div_eq_mul_inv] at hvone
    exact ((div_eq_one_iff_eq hux).mp hvone).symm

end ClassicalComplexWPT
