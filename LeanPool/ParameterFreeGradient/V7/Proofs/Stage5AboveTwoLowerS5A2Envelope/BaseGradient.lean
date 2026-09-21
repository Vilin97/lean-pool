/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.OutsideGradient

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5AFinalRepair

/-- Frozen L07: either a query is outside and has full scaled norm, or it and
an optimizer both lie in the radius-four ball, where convexity converts the
S5-C value gap into the exact `1/128` gradient bound. -/
theorem _root_.V7.aboveLowerBaseGradient : AboveLowerBaseGradientStatement := by
  intro p hp d T data hassum t ht
  have hgapPack := V7.aboveLowerQueryGap p hp d T data hassum
  have houtPack := V7.aboveLowerOutsideGradient p hp d T data hassum
  rcases hassum with ⟨hcompletion, hobjectiveConvex, hobjectiveGradient⟩
  let base := data.toLowerCompletionData
  rcases hcompletion with
    ⟨hp', hd, hT, hTd, hx0, hkernel, hDelta, hdelta, hchi, hbeta,
      hqueries, hsteps, hcompletedValue, hcompletedGradient⟩
  have hpOne : 1 ≤ p := by linarith
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hDeltaPos : 0 < base.Delta := by rw [hDelta]; positivity
  have hDeltaLe : base.Delta ≤ 1 := by
    rw [hDelta]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith : 0 ≤ p))
  have hdeltaPos : 0 < base.delta := by rw [hdelta]; positivity
  have hchiPos : 0 < base.chi := by rw [hchi]; positivity
  have hbetaPos : 0 < base.beta := by rw [hbeta]; exact div_pos hchiPos hkernel.1
  let K : ℝ := 1 /
    (128 * base.kernel.Mpd * (T : ℝ) ^ (1 + 2 / p))
  have hconst16 := lower_gap_constant_identity (p := p) (T := T)
    (M := base.kernel.Mpd) (Delta := base.Delta) (chi := base.chi)
    (delta := base.delta) (beta := base.beta) (by linarith : 0 < p)
    hT hkernel.1 hDelta hdelta hchi hbeta
  have hK8 : 8 * K = base.beta * base.Delta / 4 := by
    dsimp [K]
    rw [hconst16]
    ring
  by_cases hq : lpNorm p (base.queries t) < 4
  · obtain ⟨minimizer, hmin, hqueryGap⟩ := hgapPack.2
    have hminRadius : lpNorm p minimizer < 4 := houtPack.2 minimizer hmin
    have hdistance : lpNorm p (base.queries t - minimizer) < 8 := by
      have htri := lpNorm_add_le hpOne (base.queries t) (-minimizer)
      have hneg : lpNorm p (-minimizer) = lpNorm p minimizer := by
        exact O3.lpNorm_neg p minimizer
      rw [hneg] at htri
      have hsub : base.queries t + -minimizer = base.queries t - minimizer := by module
      rw [hsub] at htri
      linarith
    have hfirst := O3.Stage3Anchor.firstOrderConvex_of_coordinateGradient
      hobjectiveConvex hobjectiveGradient (base.queries t) minimizer
    have hgapPair : data.completedOracle.value (base.queries t) -
        data.completedOracle.value minimizer ≤
      O3.pairing (data.completedOracle.gradient (base.queries t))
        (base.queries t - minimizer) := by
      simp only [O3.pairing, Pi.sub_apply, mul_sub,
        Finset.sum_sub_distrib] at hfirst ⊢
      linarith
    have hholder := O3.pairing_le_lpNorm_mul
      (O3.holderConjugate_conjugateExponent (by linarith : 1 < p)).symm
      (data.completedOracle.gradient (base.queries t))
      (base.queries t - minimizer)
    have hGnonneg := O3.lpNorm_nonneg (conjugateExponent p)
      (data.completedOracle.gradient (base.queries t))
    have hgap16 := hqueryGap t ht
    have hupper8 : data.completedOracle.value (base.queries t) -
        data.completedOracle.value minimizer ≤
      8 * lpNorm (conjugateExponent p)
        (data.completedOracle.gradient (base.queries t)) := by
      calc
        _ ≤ O3.pairing (data.completedOracle.gradient (base.queries t))
            (base.queries t - minimizer) := hgapPair
        _ ≤ lpNorm (conjugateExponent p)
            (data.completedOracle.gradient (base.queries t)) *
              lpNorm p (base.queries t - minimizer) := hholder
        _ ≤ 8 * lpNorm (conjugateExponent p)
            (data.completedOracle.gradient (base.queries t)) := by nlinarith
    change K ≤ lpNorm (conjugateExponent p)
      (data.completedOracle.gradient (base.queries t))
    have hgapK : 8 * K ≤
        data.completedOracle.value (base.queries t) -
          data.completedOracle.value minimizer := by
      calc
        8 * K = 1 / (16 * base.kernel.Mpd *
            (T : ℝ) ^ (1 + 2 / p)) := hK8.trans hconst16
        _ ≤ _ := hgap16
    nlinarith
  · have hqOutside : 4 ≤ lpNorm p (base.queries t) := le_of_not_gt hq
    have hfull := (houtPack.1 (base.queries t) hqOutside).2
    change K ≤ lpNorm (conjugateExponent p)
      (data.completedOracle.gradient (base.queries t))
    rw [hfull]
    nlinarith [hK8, mul_le_mul_of_nonneg_left hDeltaLe hbetaPos.le]

end V7.Stage5AboveTwoLowerS5A2Envelope
