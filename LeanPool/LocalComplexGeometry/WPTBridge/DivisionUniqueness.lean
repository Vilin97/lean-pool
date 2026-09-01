/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.WPTBridge.Division

/-!
# Uniqueness in analytic Weierstrass division

This file proves germ-level uniqueness of the analytic quotient and the
finite-degree remainder coefficients.
-/

open Filter
open scoped BigOperators ENNReal NNReal Topology

namespace LocalComplexGeometry.WPTBridge

open ClassicalComplexWPT

noncomputable section

/-- Evaluation of a normalized finite prepared tail in physical coordinates. -/
theorem eval_preparedTailSeq_physical {n d : ℕ} (r : ℝ≥0)
    (b : Fin d → Base n → ℂ) (z : Base n) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (preparedTailSeq r d b z) w =
      (((r : ℂ) ^ d)⁻¹) *
        ∑ i : Fin d, b i z * ((r : ℂ) * w) ^ (i : ℕ) := by
  rw [evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero d _
    (seqHighShift_preparedTailSeq r b z) hw]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [preparedTailSeq_apply_fin, mul_pow]
  ring

/-- Evaluation of a quotient sequence times the normalized prepared divisor. -/
theorem eval_sequenceProduct_preparedPolynomial {n d : ℕ} (r : ℝ≥0)
    (hr0 : 0 < r) (a : Fin d → Base n → ℂ) (z : Base n)
    (q : L1Sequence) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries
        (seqLowShift d q + convolution q (preparedTailSeq r d a z)) w =
      evalL1PowerSeries q w * (((r : ℂ) ^ d)⁻¹) *
        preparedPolynomial d a (z, (r : ℂ) * w) := by
  have hseq : seqLowShift d q + convolution q (preparedTailSeq r d a z) =
      convolution q (seqLowShift d constantOneSeq + preparedTailSeq r d a z) := by
    rw [← convolution_monomialSeq q d, ← seqLowShift_constantOneSeq d,
      convolution_add_right]
  rw [hseq, evalL1PowerSeries_convolution _ _ hw,
    eval_preparedPolynomialSeq r hr0 a z hw]
  ring

/--
Function-germ uniqueness in analytic Weierstrass division: two analytic
quotients and analytic degree-`< d` remainders representing the same germ have
the same quotient germ and the same coefficient germs.
-/
theorem analyticWeierstrassDivision_unique {n d : ℕ}
    (h q q' : Ambient n → ℂ)
    (remainder remainder' : Fin d → Base n → ℂ)
    (a : Fin d → Base n → ℂ)
    (hq : AnalyticAt ℂ q 0) (hq' : AnalyticAt ℂ q' 0)
    (hremainder : ∀ i, AnalyticAt ℂ (remainder i) 0)
    (hremainder' : ∀ i, AnalyticAt ℂ (remainder' i) 0)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hfactor : h =ᶠ[𝓝 0] fun x ↦
      q x * preparedPolynomial d a x +
        ∑ i : Fin d, remainder i x.1 * x.2 ^ (i : ℕ))
    (hfactor' : h =ᶠ[𝓝 0] fun x ↦
      q' x * preparedPolynomial d a x +
        ∑ i : Fin d, remainder' i x.1 * x.2 ^ (i : ℕ)) :
    q =ᶠ[𝓝 0] q' ∧ ∀ i, remainder i =ᶠ[𝓝 0] remainder' i := by
  let qdiff : Ambient n → ℂ := fun x ↦ q x - q' x
  let remainderDiff : Fin d → Base n → ℂ :=
    fun i z ↦ remainder i z - remainder' i z
  have hqdiff : AnalyticAt ℂ qdiff 0 := hq.sub hq'
  have hremainderDiff : ∀ i, AnalyticAt ℂ (remainderDiff i) 0 :=
    fun i ↦ (hremainder i).sub (hremainder' i)
  have hzero : (fun x : Ambient n ↦
      qdiff x * preparedPolynomial d a x +
        ∑ i : Fin d, remainderDiff i x.1 * x.2 ^ (i : ℕ)) =ᶠ[𝓝 0]
      (fun _ ↦ 0) := by
    filter_upwards [hfactor, hfactor'] with x hx hx'
    have heq : q x * preparedPolynomial d a x +
          ∑ i : Fin d, remainder i x.1 * x.2 ^ (i : ℕ) =
        q' x * preparedPolynomial d a x +
          ∑ i : Fin d, remainder' i x.1 * x.2 ^ (i : ℕ) := hx.symm.trans hx'
    change (q x - q' x) * preparedPolynomial d a x +
      ∑ i : Fin d,
        (remainder i x.1 - remainder' i x.1) * x.2 ^ (i : ℕ) = 0
    have hsum :
        (∑ i : Fin d,
          (remainder i x.1 - remainder' i x.1) * x.2 ^ (i : ℕ)) =
        (∑ i : Fin d, remainder i x.1 * x.2 ^ (i : ℕ)) -
          ∑ i : Fin d, remainder' i x.1 * x.2 ^ (i : ℕ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    calc
      (q x - q' x) * preparedPolynomial d a x +
          (∑ i : Fin d, remainder i x.1 * x.2 ^ (i : ℕ) -
            ∑ i : Fin d, remainder' i x.1 * x.2 ^ (i : ℕ)) =
        (q x * preparedPolynomial d a x +
            ∑ i : Fin d, remainder i x.1 * x.2 ^ (i : ℕ)) -
          (q' x * preparedPolynomial d a x +
            ∑ i : Fin d, remainder' i x.1 * x.2 ^ (i : ℕ)) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  obtain ⟨p, hp⟩ := hqdiff
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos with ⟨r, hr0E, hrp⟩
  have hr0 : 0 < r := by exact_mod_cast hr0E
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  let quotientCoeffs : Base n → L1Sequence := (weightedCoefficientSeries p r).sum
  have hquotientReconstruct :
      (fun x : Ambient n ↦ evalL1PowerSeries (quotientCoeffs x.1)
        ((r : ℂ)⁻¹ * x.2)) =ᶠ[𝓝 0] qdiff :=
    eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
      p r hp hr0 hrp
  let scale : Ambient n → Ambient n := fun x ↦ (x.1, (r : ℂ) * x.2)
  have hscale : Tendsto scale (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt scale 0 := by
      dsimp only [scale]
      fun_prop
    simpa [scale, ambient_zero_eq] using hc.tendsto
  have hzeroScaled := hzero.comp_tendsto hscale
  have hquotientReconstructScaled := hquotientReconstruct.comp_tendsto hscale
  have hzeroCurry := hzeroScaled.curry_nhds
  have hquotientReconstructCurry := hquotientReconstructScaled.curry_nhds
  have hsmall := eventually_norm_preparedTailSeq_lt_one r a ha ha0
  have hbase : ∀ᶠ z in 𝓝 (0 : Base n),
      quotientCoeffs z = 0 ∧ preparedTailSeq r d remainderDiff z = 0 := by
    filter_upwards [hzeroCurry, hquotientReconstructCurry, hsmall] with
      z hzzero hzquotient hzsmall
    have heval :
        (fun w : ℂ ↦ evalL1PowerSeries (0 : L1Sequence) w) =ᶠ[𝓝 0]
          (fun w ↦ evalL1PowerSeries
            (seqLowShift d (quotientCoeffs z) +
              convolution (quotientCoeffs z) (preparedTailSeq r d a z) +
              preparedTailSeq r d remainderDiff z) w) := by
      have hunit : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ < 1 := by
        have hb := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
        filter_upwards [hb] with w hw
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      filter_upwards [hzzero, hzquotient, hunit] with w hwzero hwquotient hw
      have hquotientValue : evalL1PowerSeries (quotientCoeffs z) w =
          qdiff (z, (r : ℂ) * w) := by
        simpa [quotientCoeffs, scale, hrC] using hwquotient
      rw [evalL1PowerSeries_add_local,
        eval_sequenceProduct_preparedPolynomial r hr0 a z (quotientCoeffs z) hw,
        eval_preparedTailSeq_physical r remainderDiff z hw]
      have hscaledZero :
          qdiff (z, (r : ℂ) * w) * preparedPolynomial d a (z, (r : ℂ) * w) +
            ∑ i : Fin d,
              remainderDiff i z * ((r : ℂ) * w) ^ (i : ℕ) = 0 := by
        simpa [scale] using hwzero
      simp only [evalL1PowerSeries, map_zero]
      calc
        0 = (((r : ℂ) ^ d)⁻¹) *
            (qdiff (z, (r : ℂ) * w) * preparedPolynomial d a (z, (r : ℂ) * w) +
              ∑ i : Fin d,
                remainderDiff i z * ((r : ℂ) * w) ^ (i : ℕ)) := by
          rw [hscaledZero, mul_zero]
        _ = evalL1PowerSeries (quotientCoeffs z) w * (((r : ℂ) ^ d)⁻¹) *
              preparedPolynomial d a (z, (r : ℂ) * w) +
            (((r : ℂ) ^ d)⁻¹) *
              ∑ i : Fin d,
                remainderDiff i z * ((r : ℂ) * w) ^ (i : ℕ) := by
          rw [hquotientValue]
          ring
    have hfactorSeq : (0 : L1Sequence) =
        seqLowShift d (quotientCoeffs z) +
          convolution (quotientCoeffs z) (preparedTailSeq r d a z) +
          preparedTailSeq r d remainderDiff z :=
      eq_of_evalL1PowerSeries_eventuallyEq _ _ heval
    have hzeroFactor : (0 : L1Sequence) =
        seqLowShift d (0 : L1Sequence) +
          convolution (0 : L1Sequence) (preparedTailSeq r d a z) + 0 := by
      have hshift : seqLowShift d (0 : L1Sequence) = 0 := by
        apply lp.ext
        funext k
        by_cases hk : k < d
        · rw [seqLowShift_apply_of_lt d 0 hk]
          rfl
        · rw [seqLowShift_apply_of_le d 0 (Nat.le_of_not_gt hk)]
          rfl
      have hconv : convolution (0 : L1Sequence) (preparedTailSeq r d a z) = 0 := by
        apply lp.ext
        funext k
        rw [convolution_apply]
        simp
      rw [hshift, hconv, add_zero, zero_add]
    have hzeroSupport : seqHighShift d (0 : L1Sequence) = 0 := by
      change seqHighShiftCLM d (0 : L1Sequence) = 0
      exact map_zero _
    have huniq := seqDivision_factorizations_unique d (preparedTailSeq r d a z)
      hzsmall (0 : L1Sequence)
      (quotientCoeffs z) (preparedTailSeq r d remainderDiff z)
      0 0 hfactorSeq (seqHighShift_preparedTailSeq r remainderDiff z)
      hzeroFactor hzeroSupport
    exact huniq
  constructor
  · have hbaseAmbient : ∀ᶠ x in 𝓝 (0 : Ambient n), quotientCoeffs x.1 = 0 := by
      have hfst : Tendsto (fun x : Ambient n ↦ x.1) (𝓝 0) (𝓝 0) := by
        simpa using
          (continuousAt_fst.tendsto : Tendsto (fun x : Ambient n ↦ x.1)
            (𝓝 0) (𝓝 ((0 : Ambient n).1)))
      exact hfst.eventually (hbase.mono fun z hz ↦ hz.1)
    have hqdiffZero : qdiff =ᶠ[𝓝 0] (fun _ ↦ 0) := by
      filter_upwards [hquotientReconstruct, hbaseAmbient] with x hx hcoeff
      rw [hcoeff] at hx
      have hevalZero : evalL1PowerSeries (0 : L1Sequence) ((r : ℂ)⁻¹ * x.2) = 0 := by
        change l1EvalOperator ((r : ℂ)⁻¹ * x.2) (0 : L1Sequence) = 0
        exact map_zero _
      exact hx.symm.trans hevalZero
    filter_upwards [hqdiffZero] with x hx
    exact sub_eq_zero.mp hx
  · intro i
    filter_upwards [hbase] with z hz
    have htailEq : preparedTailSeq r d remainderDiff z =
        preparedTailSeq r d (fun _ _ ↦ 0) z := by
      calc
        preparedTailSeq r d remainderDiff z = 0 := hz.2
        _ = preparedTailSeq r d (fun _ _ ↦ 0) z := by
          symm
          classical
          unfold preparedTailSeq
          simp
    have hi := (preparedTailSeq_eq_iff hr0 remainderDiff (fun _ _ ↦ 0) z).mp
      htailEq i
    exact sub_eq_zero.mp (by simpa [remainderDiff] using hi)

end

end LocalComplexGeometry.WPTBridge
