/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingEntranceCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.ShapedWaitBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.TailCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingProfile

@[expose] public section

/-!
# One clean outgoing cone on one reset witness

The shaped-hold estimate below is obtained from the actual angular floor and
axial history. The later assembly keeps the same reset and corrected amplitude
through every interval. The true additional inequality starts at the shaped
hold; the early outgoing region only requires the relaxed cone.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.UniformAngularReset (ResetWitness)
open NavierStokes.OutgoingEntranceCone (coneA coneB coneRatio)

namespace NavierStokes.OutgoingCone

theorem coneA_eq_actualA {d : TailData} {K : ℝ} (w : ResetWitness d K) (y eta : ℝ) :
    coneA w (y, eta) = TailCone.actualA w y eta := by
  rw [OutgoingEntranceCone.coneA_eq_E_derivative]
  have hd := ((OutgoingHistories.dY_hasDerivAt (OutgoingHistories.E_smooth w) (y, eta)).log
    (OutgoingHistories.E_pos w (y, eta)).ne').deriv
  unfold TailCone.actualA
  rw [hd]
  ring

theorem coneB_eq_actualBs {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    coneB w Amp (y, eta) = TailCone.actualBs w Amp y eta := by
  rw [OutgoingEntranceCone.coneB, OutgoingHistories.dY_eq_deriv (OutgoingHistories.U_smooth d ha)]
  rfl

theorem hold_Qs_pos {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) {eta t : ℝ}
    (hh1 : d.h ≤ 1 / 100) (hhlam : d.h ≤ d.core.lam / 4)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (heta : |eta| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ d.core.wait) :
    0 < OutgoingHistories.Qs w Amp (d.core.holdStart + t, eta) := by
  have hf := ShapedWaitBounds.holdFloor_pos d.core.m
  have hl := ShapedWaitBounds.canonical_Qs_hold_lower w ha hh1 hhlam hhT heta ht htw
  have hp : 0 < ShapedWaitBounds.holdFloor d.core.m *
      (eta ^ 2 + d.core.lam + Real.exp (-(1 - d.core.lam) * t)) := by
    exact mul_pos hf (by nlinarith [sq_nonneg eta, d.core.lam_pos, Real.exp_pos (-(1 - d.core.lam)
      * t)])
  exact hp.trans_le hl

noncomputable def holdRatioConstant (P m : ℝ) : ℝ :=
  ShapedWaitBounds.axialWaitConstant P m / (2 * ShapedWaitBounds.holdFloor m)

theorem holdRatioConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < holdRatioConstant P m :=
  div_pos (ShapedWaitBounds.axialWaitConstant_pos hP m)
    (mul_pos (by norm_num) (ShapedWaitBounds.holdFloor_pos m))

/-- The Gaussian part of the genuine angular floor cancels the parameter
factor in the genuine axial history bound. -/
theorem hold_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) {eta t : ℝ}
    (hh1 : d.h ≤ 1 / 100) (hhlam : d.h ≤ d.core.lam / 4)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (heta : |eta| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ d.core.wait) :
    |coneRatio w Amp (d.core.holdStart + t, eta)| ≤
      holdRatioConstant d.core.P d.core.m * (1 + t) * Real.exp (d.core.lam * t / 2) := by
  have hc := ShapedWaitBounds.holdFloor_pos d.core.m
  have hC := ShapedWaitBounds.axialWaitConstant_pos d.core.P_pos d.core.m
  have hQ := hold_Qs_pos w ha hh1 hhlam hhT heta ht htw
  have hlo := ShapedWaitBounds.canonical_Qs_hold_lower w ha hh1 hhlam hhT heta ht htw
  have hN := ShapedWaitBounds.canonical_Ns_hold_ratio_bound w ha hh1 heta ht htw
  let s : ℝ := Real.exp (-(1 - d.core.lam) * t / 2)
  have hs : s ^ 2 = Real.exp (-(1 - d.core.lam) * t) := by
    dsimp [s]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : 2 * |eta| * s ≤ eta ^ 2 + Real.exp (-(1 - d.core.lam) * t) := by
    have hb := sq_nonneg (|eta| - s)
    nlinarith [hs, sq_abs eta]
  have hmul := mul_le_mul_of_nonneg_left hsq hc.le
  have hqeta : 2 * ShapedWaitBounds.holdFloor d.core.m * |eta| * s ≤
      OutgoingHistories.Qs w Amp (d.core.holdStart + t, eta) := by
    nlinarith [mul_pos hc d.core.lam_pos]
  have hfac : 0 ≤ holdRatioConstant d.core.P d.core.m * (1 + t) * Real.exp (d.core.lam * t / 2) :=
    mul_nonneg (mul_nonneg (holdRatioConstant_pos d.core.P_pos d.core.m).le (by linarith))
      (Real.exp_pos _).le
  have hb := mul_le_mul_of_nonneg_left hqeta hfac
  have hex : Real.exp (d.core.lam * t / 2) * s = Real.exp (-(1 / 2 - d.core.lam) * t) := by
    dsimp [s]
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : (holdRatioConstant d.core.P d.core.m * (1 + t) * Real.exp (d.core.lam * t / 2)) *
      (2 * ShapedWaitBounds.holdFloor d.core.m * |eta| * s) =
      ShapedWaitBounds.axialWaitConstant d.core.P d.core.m * |eta| * (1 + t) *
        Real.exp (-(1 / 2 - d.core.lam) * t) := by
    rw [← hex]
    dsimp [holdRatioConstant]
    field_simp [hc.ne']
  rw [hid] at hb
  unfold OutgoingEntranceCone.coneRatio
  rw [← div_div, abs_div, abs_of_pos hQ]
  exact (div_le_iff₀ hQ).mpr (hN.trans hb)

noncomputable def holdSmallConstant (P m : ℝ) : ℝ :=
  60 * Real.exp 30 * holdRatioConstant P m

theorem holdSmallConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < holdSmallConstant P m :=
  mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (holdRatioConstant_pos hP m)

theorem hold_sqrt_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) {eta t : ℝ}
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hh1 : d.h ≤ 1 / 100) (hhlam : d.h ≤ d.core.lam / 4)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (heta : |eta| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ d.core.wait) :
    Real.sqrt d.core.lam * |coneRatio w Amp (d.core.holdStart + t, eta)| ≤
      holdSmallConstant d.core.P d.core.m * PulseCone.coneRate d.core.lam := by
  have hlog : 0 ≤ Real.log (1 / d.core.lam) := Real.log_nonneg
    ((le_div_iff₀ d.core.lam_pos).mpr (by linarith [d.core.lam_lt]))
  have htlog : t ≤ 60 * Real.log (1 / d.core.lam) := by rwa [hwait] at htw
  have hlin : 1 + t ≤ 60 * (1 + Real.log (1 / d.core.lam)) := by linarith
  have hlambda := mul_le_mul_of_nonneg_left htlog d.core.lam_pos.le
  have harg : d.core.lam * t / 2 ≤ 30 := by nlinarith [TailCone.lambda_log_bound d]
  have hex := Real.exp_le_exp.mpr harg
  have hb := hold_ratio_bound w ha hh1 hhlam hhT heta ht htw
  have hC := (holdRatioConstant_pos d.core.P_pos d.core.m).le
  have hbound := mul_le_mul hlin hex (Real.exp_pos _).le (by positivity : 0 ≤ 60 * (1 + Real.log (1
    / d.core.lam)))
  have hm := mul_le_mul_of_nonneg_left hbound hC
  have hraw : |coneRatio w Amp (d.core.holdStart + t, eta)| ≤
      holdSmallConstant d.core.P d.core.m * (1 + Real.log (1 / d.core.lam)) := by
    dsimp [holdSmallConstant]
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg d.core.lam)
  have hr := (PulseCone.coneRate_parts d.core.lam_pos (by linarith [d.core.lam_lt])).2.2
  have hr' := mul_le_mul_of_nonneg_left hr (holdSmallConstant_pos d.core.P_pos d.core.m).le
  nlinarith

theorem exists_hold_threshold (P m : ℝ) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
      holdSmallConstant P m * PulseCone.coneRate lam ≤ 1 / 2 := by
  have ht := PulseCone.coneRate_tendsto_zero.const_mul (holdSmallConstant P m)
  have he : ∀ᶠ lam in 𝓝[>] (0 : ℝ), holdSmallConstant P m * PulseCone.coneRate lam < 1 / 2 :=
    ht.eventually (gt_mem_nhds (by norm_num : holdSmallConstant P m * (0 : ℝ) < 1 / 2))
  obtain ⟨delta, hd, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨delta, hd, fun lam hl hu => (hsub ⟨hl, hu⟩).le⟩

theorem hold_coneA {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : d.core.holdStart ≤ y) (hy' : y ≤ d.core.pulseStart) :
    coneA w (y, eta) = 2 + 2 * d.core.lam := by
  have hend : y < d.core.endpoint := by
    dsimp [OutgoingSchedule.Parameters.endpoint]
    linarith [d.core.pulseLength_pos]
  rw [OutgoingEntranceCone.coneA_before w hend]
  dsimp [OutgoingEntranceCone.radialA]
  rw [slope_hold d.core.dropLength_pos.le hy]
  ring

theorem hold_coneB {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.core.holdStart ≤ y) (hy' : y ≤ d.core.pulseStart) : coneB w Amp (y, eta) = 0 := by
  have hHB : d.core.holdStart < d.core.pulseStart := by
    dsimp [OutgoingSchedule.Parameters.pulseStart]
    linarith [d.core.wait_gt]
  have hz : HasDerivWithinAt (fun t => OutgoingHistories.U d Amp (t, eta)) 0
      (Icc d.core.holdStart d.core.pulseStart) y := by
    apply (hasDerivWithinAt_const y (Icc d.core.holdStart d.core.pulseStart) (0 : ℝ)).congr
    · intro t ht
      exact axial_shaped_wait d.core Amp eta ht.1 ht.2
    · exact axial_shaped_wait d.core Amp eta hy hy'
  have hd := (uniqueDiffOn_Icc hHB y ⟨hy, hy'⟩).eq_deriv _
    (OutgoingHistories.dY_hasDerivAt (OutgoingHistories.U_smooth d ha) (y, eta)).hasDerivWithinAt hz
  simp [OutgoingEntranceCone.coneB, hd]

theorem hold_source_criterion {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hh1 : d.h ≤ 1 / 100) (hhlam : d.h ≤ d.core.lam / 4)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (hsmall : holdSmallConstant d.core.P d.core.m * PulseCone.coneRate d.core.lam ≤ 1 / 2)
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.core.holdStart ≤ y) (hy' : y ≤ d.core.pulseStart) :
    0 < OutgoingHistories.Qs w Amp (y, eta) ∧
    0 < coneA w (y, eta) - coneB w Amp (y, eta) * coneRatio w Amp (y, eta) ∧
    2 * coneB w Amp (y, eta) * coneRatio w Amp (y, eta) +
      coneB w Amp (y, eta) ^ 2 / coneA w (y, eta) +
        (coneA w (y, eta) - 2) * coneRatio w Amp (y, eta) ^ 2 < 2 ∧
    2 < coneA w (y, eta) := by
  have ht : 0 ≤ y - d.core.holdStart := sub_nonneg.mpr hy
  have htw : y - d.core.holdStart ≤ d.core.wait := by
    dsimp [OutgoingSchedule.Parameters.pulseStart] at hy'
    linarith
  have hsum : d.core.holdStart + (y - d.core.holdStart) = y := by ring
  have hq := hold_Qs_pos w ha hh1 hhlam hhT heta ht htw
  rw [hsum] at hq
  have hr := (hold_sqrt_ratio_bound w ha hwait hh1 hhlam hhT heta ht htw).trans hsmall
  rw [hsum] at hr
  have hpow : d.core.lam * coneRatio w Amp (y, eta) ^ 2 ≤ 1 / 4 := by
    have hp := Real.sq_sqrt d.core.lam_pos.le
    have hab : |coneRatio w Amp (y, eta)| ^ 2 = coneRatio w Amp (y, eta) ^ 2 := sq_abs _
    have hnonneg := mul_nonneg (Real.sqrt_nonneg d.core.lam) (abs_nonneg (coneRatio w Amp (y, eta)))
    nlinarith [sq_nonneg (Real.sqrt d.core.lam * |coneRatio w Amp (y, eta)| - 1 / 2)]
  rw [hold_coneA w eta hy hy', hold_coneB w ha eta hy hy']
  refine ⟨hq, ?_, ?_, ?_⟩
  · simp only [zero_mul, sub_zero]
    linarith [d.core.lam_pos]
  · norm_num only [zero_mul, mul_zero, zero_pow, zero_div, zero_add, add_zero]
    nlinarith
  · linarith [d.core.lam_pos]

/-! ## Common actual cone coordinates and source tests -/

noncomputable def normalV {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  coneA w p * (1 + (coneB w Amp p / coneA w p) ^ 2)

noncomputable def normalP {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (XR : ℝ) (p : ℝ × ℝ) : ℝ :=
  OutgoingHistories.p1 XR w Amp p * (1 - coneB w Amp p * coneRatio w Amp p / coneA w p)

noncomputable def normalJ {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (XR : ℝ) (p : ℝ × ℝ) : ℝ :=
  OutgoingHistories.p1 XR w Amp p * (coneRatio w Amp p + coneB w Amp p / coneA w p)

structure SourceCriterion {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : ℝ × ℝ) : Prop where
  angular_positive : 0 < OutgoingHistories.Qs w Amp p
  radial_positive : 0 < coneA w p
  first_positive : 0 < coneA w p - coneB w Amp p * coneRatio w Amp p
  second_strict : 2 * coneB w Amp p * coneRatio w Amp p +
    coneB w Amp p ^ 2 / coneA w p + (coneA w p - 2) * coneRatio w Amp p ^ 2 < 2

structure RelaxedAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (XR : ℝ) (p : ℝ × ℝ) : Prop where
  angular_positive : 0 < OutgoingHistories.Qs w Amp p
  radial_positive : 0 < coneA w p
  stress_gt_two : 2 < normalP w Amp XR p
  root_strict : normalV w Amp p < ConeAlgebra.coneBound (normalP w Amp XR p) (normalJ w Amp XR p)

noncomputable def TrueAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (XR : ℝ) (p : ℝ × ℝ) : Prop :=
  RelaxedAt w Amp XR p ∧ 2 < normalV w Amp p

theorem normalV_gt_two_of_radial {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : ℝ × ℝ) (ha : 2 < coneA w p) : 2 < normalV w Amp p := by
  have hm := mul_nonneg (show 0 ≤ coneA w p by linarith) (sq_nonneg (coneB w Amp p / coneA w p))
  unfold normalV
  nlinarith

theorem sourceCriterion_before_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hh1 : d.h ≤ 1 / 100) (hhlam : d.h ≤ d.core.lam / 4)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (hP : Real.exp (d.core.dropLength + 1) ≤ d.core.P ^ 2)
    (hdrop : OutgoingEntranceCone.dropSpeed d.core.m ≤ OutgoingEntranceCone.dropThreshold)
    (hentrance : d.core.lam * OutgoingEntranceCone.entranceRatioBound d.core.P d.core.m ^ 2 ≤ 1 / 4)
    (hhold : holdSmallConstant d.core.P d.core.m * PulseCone.coneRate d.core.lam ≤ 1 / 2)
    (hpulse : ∀ eta t : ℝ, |eta| ≤ 1 → 0 ≤ t → t ≤ d.core.pulseLength →
      PulseCone.PulseConeAt w Amp (d.core.pulseStart + t, eta))
    {y eta : ℝ} (hy : y ≤ d.core.endpoint) (heta : |eta| ≤ 1) :
    SourceCriterion w Amp (y, eta) := by
  by_cases hy0 : y ≤ 0
  · have hi := OutgoingEntranceCone.actual_ideal_cone_margins w ha hy0 eta
    refine ⟨?_, ?_, hi.2.2.1, hi.2.2.2.trans_lt (by norm_num)⟩
    · exact (by norm_num : (0 : ℝ) < 1).trans_le
        (OutgoingEntranceCone.canonical_Qs_ideal_lower w ha hh1 hy0 heta)
    · rw [hi.1]; norm_num
  have hy0' : 0 ≤ y := (lt_of_not_ge hy0).le
  by_cases hyH : y ≤ d.core.holdStart
  · have hm := OutgoingEntranceCone.actual_preliminary_margins w ha hh1 hP hhT hdrop hentrance
      (show (y, eta) ∈ OutgoingEntranceCone.preliminaryWindow d from ⟨⟨hy0', hyH⟩, abs_le.mp heta⟩)
    refine ⟨OutgoingEntranceCone.canonical_Qs_pos w ha hh1 hy0' hyH heta hhT, ?_,
      (by norm_num : (0 : ℝ) < 4 / 5).trans_le hm.1, hm.2.trans_lt (by norm_num)⟩
    have he : y < d.core.endpoint := by
      dsimp [OutgoingSchedule.Parameters.endpoint]
      linarith [d.core.pulseStart_ge_hold, d.core.pulseLength_pos]
    rw [OutgoingEntranceCone.coneA_before w he]
    exact (by norm_num : (0 : ℝ) < 4 / 5).trans_le (OutgoingEntranceCone.radialA_bounds d.core y).1
  by_cases hyB : y ≤ d.core.pulseStart
  · have hh := hold_source_criterion w ha hwait hh1 hhlam hhT hhold heta (le_of_not_ge hyH) hyB
    exact ⟨hh.1, by linarith [hh.2.2.2], hh.2.1, hh.2.2.1⟩
  have ht : 0 ≤ y - d.core.pulseStart := by linarith
  have ht' : y - d.core.pulseStart ≤ d.core.pulseLength := by
    dsimp [OutgoingSchedule.Parameters.endpoint] at hy
    linarith
  have hp := hpulse eta (y - d.core.pulseStart) heta ht ht'
  rw [add_sub_cancel] at hp
  exact ⟨hp.angular_positive, by change 0 < PulseCone.radialA w (y, eta); linarith
    [hp.radial_gt_two],
    hp.true_criterion.1, hp.true_criterion.2.1⟩

theorem true_radial_before_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ)
    (hpulse : ∀ eta t : ℝ, |eta| ≤ 1 → 0 ≤ t → t ≤ d.core.pulseLength →
      PulseCone.PulseConeAt w Amp (d.core.pulseStart + t, eta))
    {y eta : ℝ} (hy : d.core.holdStart ≤ y) (hy' : y ≤ d.core.endpoint) (heta : |eta| ≤ 1) :
    2 < normalV w Amp (y, eta) := by
  apply normalV_gt_two_of_radial
  by_cases hyB : y ≤ d.core.pulseStart
  · rw [hold_coneA w eta hy hyB]
    linarith [d.core.lam_pos]
  · have hp := hpulse eta (y - d.core.pulseStart) heta (by linarith) (by
      dsimp [OutgoingSchedule.Parameters.endpoint] at hy'; linarith)
    rw [add_sub_cancel] at hp
    exact hp.radial_gt_two

noncomputable def preWindow (d : TailData) (left : ℝ) : Set (ℝ × ℝ) :=
  Icc left d.core.endpoint ×ˢ Icc (-1) 1

theorem actual_p1_pos {d : TailData} {K : ℝ} (w : ResetWitness d K) (Amp : ℝ → ℝ)
    {y eta : ℝ} (heta : |eta| ≤ 1) (hQ : 0 < OutgoingHistories.Qs w Amp (y, eta)) :
    0 < OutgoingHistories.p1 1 w Amp (y, eta) := by
  have heta2 : eta ^ 2 ≤ 1 := OutgoingEntranceCone.parameter_square_le_one heta
  have hL := CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half heta2
  change 0 < 1 * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta
  exact div_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hQ) hL

/-- Compactness is applied to actual smooth data after the source tests have
been established. It gives one radial scale for the whole pre-tail interval. -/
theorem compact_actual_pre_cone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (left : ℝ)
    (hsource : ∀ p ∈ preWindow d left, SourceCriterion w Amp p) :
    ∃ XR0 : ℝ, 0 < XR0 ∧ ∀ XR : ℝ, XR0 < XR → ∀ p ∈ preWindow d left, RelaxedAt w Amp XR p := by
  have hcompact : IsCompact (preWindow d left) := isCompact_Icc.prod isCompact_Icc
  have hratio : ContinuousOn (coneRatio w Amp) (preWindow d left) := by
    apply (OutgoingHistories.Ns_smooth w ha).continuous.continuousOn.div
      ((OutgoingHistories.E_smooth w).continuous.mul (OutgoingHistories.Qs_smooth w
        ha).continuous).continuousOn
    intro p hp
    exact (mul_pos (OutgoingHistories.E_pos w p) (hsource p hp).angular_positive).ne'
  obtain ⟨gap, p0, hgap, hp0, Hcone⟩ := UniformCone.compact_equation_eleven_gap hcompact
    (OutgoingEntranceCone.coneA_continuous w).continuousOn
    (OutgoingEntranceCone.coneB_continuous w ha).continuousOn hratio
    (fun p hp => (hsource p hp).radial_positive) (fun p hp => (hsource p hp).first_positive)
    (fun p hp => (hsource p hp).second_strict)
  have hp1 : ContinuousOn (OutgoingHistories.p1 1 w Amp) (preWindow d left) := by
    have hx : Continuous (fun p : ℝ × ℝ => Real.exp p.1 * OutgoingHistories.Qs w Amp p) :=
      (Real.continuous_exp.comp continuous_fst).mul (OutgoingHistories.Qs_smooth w ha).continuous
    have hL : Continuous (fun p : ℝ × ℝ => 1 - 2 * d.h * p.2 ^ 2) :=
      continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))
    change ContinuousOn (fun p => (1 * Real.exp p.1 * OutgoingHistories.Qs w Amp p) /
      (1 - 2 * d.h * p.2 ^ 2)) (preWindow d left)
    simp only [one_mul]
    apply hx.continuousOn.div hL.continuousOn
    rintro ⟨y, eta⟩ hp
    exact (CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half
      (OutgoingEntranceCone.parameter_square_le_one (abs_le.mpr hp.2))).ne'
  obtain ⟨c, hc, Hc⟩ := UniformCone.positive_uniform_margin hcompact hp1 (by
    rintro ⟨y, eta⟩ hp
    exact actual_p1_pos w Amp (abs_le.mpr hp.2) (hsource _ hp).angular_positive)
  refine ⟨(p0 + 1) / c, div_pos (by linarith) hc, ?_⟩
  intro XR hXR p hp
  have hXR0 : 0 < XR := (div_pos (by linarith : 0 < p0 + 1) hc).trans hXR
  have hlarge : p0 < OutgoingHistories.p1 XR w Amp p := by
    have ht := (div_lt_iff₀ hc).mp hXR
    have hm := mul_le_mul_of_nonneg_left (Hc p hp) hXR0.le
    rw [OutgoingHistories.p1_dilation]
    linarith
  have hcone := Hcone _ hlarge p hp
  refine ⟨(hsource p hp).angular_positive, (hsource p hp).radial_positive, ?_, ?_⟩
  · dsimp [normalP]
    linarith [hcone.1]
  · dsimp [normalV, normalP, normalJ]
    linarith [hcone.2]

theorem relaxed_of_zero_shear {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (XR y eta : ℝ) (heta : |eta| ≤ 1)
    (hQ : 0 < OutgoingHistories.Qs w Amp (y, eta)) (hA : 0 < coneA w (y, eta))
    (hB : coneB w Amp (y, eta) = 0) (hP : 2 < OutgoingHistories.p1 XR w Amp (y, eta))
    (hroot : coneA w (y, eta) < ConeAlgebra.coneBound
      (OutgoingHistories.p1 XR w Amp (y, eta)) (OutgoingHistories.p2 XR w Amp (y, eta))) :
    RelaxedAt w Amp XR (y, eta) := by
  have hj := TailCone.actualP2_eq w Amp XR eta y
    (OutgoingEntranceCone.parameter_square_le_one heta) hQ
  change OutgoingHistories.p2 XR w Amp (y, eta) =
    OutgoingHistories.p1 XR w Amp (y, eta) * coneRatio w Amp (y, eta) at hj
  rw [hj] at hroot
  refine ⟨hQ, hA, ?_, ?_⟩
  · simpa only [normalP, hB, zero_mul, zero_div, sub_zero, mul_one] using hP
  · simpa only [normalV, normalP, normalJ, hB, zero_mul, zero_div, zero_pow (by decide : (2 : ℕ) ≠
    0),
      sub_zero, add_zero, mul_one] using hroot

noncomputable def cleanEnd (d : TailData) : ℝ := tailStart d + 1 / 2

noncomputable def cleanWindow (d : TailData) (left : ℝ) : Set (ℝ × ℝ) :=
  Icc left (cleanEnd d) ×ˢ Icc (-1) 1

noncomputable def trueWindow (d : TailData) : Set (ℝ × ℝ) :=
  Icc d.core.holdStart (cleanEnd d) ×ˢ Icc (-1) 1

structure CleanOutgoingCone {d : TailData} {K : ℝ} (w : ResetWitness d K) (XR left : ℝ) : Prop where
  relaxed : ∀ p ∈ cleanWindow d left,
    RelaxedAt w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p
  true_from_hold : ∀ p ∈ trueWindow d,
    TrueAt w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p

/-- Join the proved intervals without choosing another reset or amplitude. -/
theorem clean_cone_of_components {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (hsource : PulseCone.sourceConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 8)
    (hh1 : d.h ≤ 1 / 100) (hhlam : d.h ≤ d.core.lam / 4)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (hreset : TailCone.resetSourceError d K ≤ d.core.lam / 4)
    (hfinite : TailCone.finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) ≤ 1 / 2)
    (hrelease : TailCone.releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2)
    (hP : Real.exp (d.core.dropLength + 1) ≤ d.core.P ^ 2)
    (hdrop : OutgoingEntranceCone.dropSpeed d.core.m ≤ OutgoingEntranceCone.dropThreshold)
    (hentrance : d.core.lam * OutgoingEntranceCone.entranceRatioBound d.core.P d.core.m ^ 2 ≤ 1 / 4)
    (hhold : holdSmallConstant d.core.P d.core.m * PulseCone.coneRate d.core.lam ≤ 1 / 2)
    (hpulse : ∀ eta t : ℝ, |eta| ≤ 1 → 0 ≤ t → t ≤ d.core.pulseLength →
      PulseCone.PulseConeAt w (CorrectedPulseAmplitude.amplitude d w.coefficients)
        (d.core.pulseStart + t, eta))
    (left : ℝ) (hleft : left ≤ 0) :
    ∃ XR0 : ℝ, 0 < XR0 ∧ ∀ XR : ℝ, XR0 < XR → CleanOutgoingCone w XR left := by
  let Amp := CorrectedPulseAmplitude.amplitude d w.coefficients
  have ha : ContDiff ℝ ∞ Amp := CorrectedPulseAmplitude.amplitude_contDiff d w.smooth
  have Hpre : ∀ p ∈ preWindow d left, SourceCriterion w Amp p := by
    rintro ⟨y, eta⟩ hp
    exact sourceCriterion_before_endpoint w ha hwait hh1 hhlam hhT hP hdrop hentrance hhold hpulse
      hp.1.2 (abs_le.mpr hp.2)
  obtain ⟨preXR, hpreXR, HpreXR⟩ := compact_actual_pre_cone w ha left Hpre
  refine ⟨max preXR (TailCone.tailRadiusThreshold d), hpreXR.trans_le (le_max_left _ _), ?_⟩
  intro XR hXR
  have hXRpre : preXR < XR := (le_max_left _ _).trans_lt hXR
  have hXRtail : TailCone.tailRadiusThreshold d < XR := (le_max_right _ _).trans_lt hXR
  have Htail : ∀ y eta : ℝ, d.core.endpoint ≤ y → y ≤ cleanEnd d → |eta| ≤ 1 →
      TrueAt w Amp XR (y, eta) := by
    intro y eta hy hy' heta
    have ht := TailCone.corrected_tail_cone w hK hwait hsmall hscale hsource hh1 hhT hreset hfinite
      hrelease
      hXRtail heta hy hy'
    have hA : 2 < coneA w (y, eta) := by rw [coneA_eq_actualA]; exact ht.2.2.1
    have hB : coneB w Amp (y, eta) = 0 := by rw [coneB_eq_actualBs w ha]; exact ht.2.1
    refine ⟨relaxed_of_zero_shear w Amp XR y eta heta ht.1 (by linarith) hB ht.2.2.2.2.1 ?_,
      normalV_gt_two_of_radial w Amp (y, eta) hA⟩
    rw [coneA_eq_actualA]
    exact ht.2.2.2.2.2
  have Hrelaxed : ∀ p ∈ cleanWindow d left, RelaxedAt w Amp XR p := by
    rintro ⟨y, eta⟩ hp
    by_cases hy : y ≤ d.core.endpoint
    · exact HpreXR XR hXRpre (y, eta) ⟨⟨hp.1.1, hy⟩, hp.2⟩
    · exact (Htail y eta (le_of_not_ge hy) hp.1.2 (abs_le.mpr hp.2)).1
  refine ⟨Hrelaxed, ?_⟩
  rintro ⟨y, eta⟩ hp
  have hyLeft : left ≤ y := hleft.trans (d.core.holdStart_pos.le.trans hp.1.1)
  refine ⟨Hrelaxed (y, eta) ⟨⟨hyLeft, hp.1.2⟩, hp.2⟩, ?_⟩
  by_cases hy : y ≤ d.core.endpoint
  · exact true_radial_before_endpoint w Amp hpulse hp.1.1 hy (abs_le.mpr hp.2)
  · exact (Htail y eta (le_of_not_ge hy) hp.1.2 (abs_le.mpr hp.2)).2

noncomputable def heightThreshold (m lam : ℝ) : ℝ :=
  min (OutgoingEntranceCone.heightThreshold m lam) (lam / 100000)

theorem heightThreshold_pos (m : ℝ) {lam : ℝ} (hlam : 0 < lam) : 0 < heightThreshold m lam :=
  lt_min (OutgoingEntranceCone.heightThreshold_pos m hlam) (div_pos hlam (by norm_num))

/-- First choose the drop parameter, then the entrance amplitude, then lambda,
then the terminal height, and only then a finite radius. The theorem accepts
any one existing reset witness throughout. -/
theorem exists_ordered_clean_cone :
    ∃ M : ℝ, 0 < M ∧ ∀ m : ℝ, M ≤ m → ∀ P : ℝ,
      OutgoingEntranceCone.amplitudeThreshold m ≤ P → ∀ K : ℝ, 0 < K →
      ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData,
        d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
        d.core.lam < lam0 → d.h ≤ heightThreshold m d.core.lam →
        ∀ w : ResetWitness d K, ∀ left : ℝ, left ≤ 0 →
          ∃ XR0 : ℝ, 0 < XR0 ∧ ∀ XR : ℝ, XR0 < XR → CleanOutgoingCone w XR left := by
  obtain ⟨M, hM, Hdrop⟩ := OutgoingEntranceCone.exists_small_dropSpeed
    OutgoingEntranceCone.dropThreshold_pos
  refine ⟨M, hM, ?_⟩
  intro m hm P hP K hK
  have hPpos := (OutgoingEntranceCone.amplitudeThreshold_pos m).trans_le hP
  obtain ⟨holdLam, hholdLam, Hhold⟩ := exists_hold_threshold P m
  obtain ⟨pulseLam, hpulseLam, Hpulse⟩ := PulseCone.exists_corrected_pulse_threshold P m K hPpos hK
  obtain ⟨tailLam, htailLam, Htail⟩ := TailCone.exists_tail_smallness_threshold P m K hPpos hK
  refine ⟨min (OutgoingEntranceCone.lambdaThreshold P m) (min holdLam (min pulseLam tailLam)),
    lt_min (OutgoingEntranceCone.lambdaThreshold_pos P m) (lt_min hholdLam (lt_min hpulseLam
      htailLam)), ?_⟩
  intro d hdP hdm hwait hlam hh w left hleft
  rcases lt_min_iff.mp hlam with ⟨hentranceLam, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hhold, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hpulse, htail⟩
  have hhTiny : d.h ≤ d.core.lam / 100000 := hh.trans (min_le_right _ _)
  have hhEntrance : d.h ≤ OutgoingEntranceCone.heightThreshold d.core.m d.core.lam := by
    rw [hdm]
    exact hh.trans (min_le_left _ _)
  have hchosen := OutgoingEntranceCone.chosen_parameters_bounds d
    (by rwa [hdm, hdP]) (by rw [hdP, hdm]; exact hentranceLam.le) hhEntrance
  obtain ⟨hsmall, hscale, hsource, hh1, hhT, hreset, hfinite, hrelease⟩ := Htail d hdP hdm htail
  have hdrop : OutgoingEntranceCone.dropSpeed d.core.m ≤ OutgoingEntranceCone.dropThreshold := by
    rw [hdm]; exact Hdrop m hm
  have hhold' : holdSmallConstant d.core.P d.core.m * PulseCone.coneRate d.core.lam ≤ 1 / 2 := by
    rw [hdP, hdm]; exact Hhold _ d.core.lam_pos hhold
  apply clean_cone_of_components w hK hwait hsmall hscale hsource hh1 (by linarith
    [d.core.lam_pos]) hhT
    hreset hfinite hrelease hchosen.1 hdrop hchosen.2.1 hhold' ?_ left hleft
  exact Hpulse d hdP hdm hwait hpulse hhTiny w

/-! ## The existing profile object and compact margins -/

noncomputable def ProfileCleanCone (F : OutgoingProfile.Profile) (XR left : ℝ) : Prop :=
  CleanOutgoingCone F.reset XR left

/-- The profile wrapper retains the input profile, its reset, and its
amplitude. It does not select a second profile satisfying separate estimates. -/
theorem exists_ordered_profile_cone :
    ∃ M : ℝ, 0 < M ∧ ∀ m : ℝ, M ≤ m → ∀ P : ℝ,
      OutgoingEntranceCone.amplitudeThreshold m ≤ P → ∀ K : ℝ, 0 < K →
      ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ F : OutgoingProfile.Profile,
        F.data.core.P = P → F.data.core.m = m → F.coefficientBound = K →
        F.data.core.wait = 60 * Real.log (1 / F.data.core.lam) →
        F.data.core.lam < lam0 → F.data.h ≤ heightThreshold m F.data.core.lam →
        ∀ left : ℝ, left ≤ 0 →
          ∃ XR0 : ℝ, 0 < XR0 ∧ ∀ XR : ℝ, XR0 < XR → ProfileCleanCone F XR left := by
  obtain ⟨M, hM, H⟩ := exists_ordered_clean_cone
  refine ⟨M, hM, ?_⟩
  intro m hm P hP K hK
  obtain ⟨lam0, hlam0, Hlam⟩ := H m hm P hP K hK
  refine ⟨lam0, hlam0, ?_⟩
  rintro ⟨d, K', w⟩ hdP hdm hK' hwait hlam hh left hleft
  dsimp only at hdP hdm hK' hwait hlam hh ⊢
  subst K'
  exact Hlam d hdP hdm hwait hlam hh w left hleft

theorem normal_data_continuousOn {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (XR : ℝ) {s : Set (ℝ × ℝ)}
    (heta : ∀ p ∈ s, |p.2| ≤ 1) (hQ : ∀ p ∈ s, 0 < OutgoingHistories.Qs w Amp p)
    (hA : ∀ p ∈ s, 0 < coneA w p) :
    ContinuousOn (normalP w Amp XR) s ∧ ContinuousOn (normalJ w Amp XR) s ∧
      ContinuousOn (normalV w Amp) s := by
  have hca := (OutgoingEntranceCone.coneA_continuous w).continuousOn (s := s)
  have hcb := (OutgoingEntranceCone.coneB_continuous w ha).continuousOn (s := s)
  have hcr : ContinuousOn (coneRatio w Amp) s := by
    apply (OutgoingHistories.Ns_smooth w ha).continuous.continuousOn.div
      ((OutgoingHistories.E_smooth w).continuous.mul (OutgoingHistories.Qs_smooth w
        ha).continuous).continuousOn
    intro p hp
    exact (mul_pos (OutgoingHistories.E_pos w p) (hQ p hp)).ne'
  have hp1 : ContinuousOn (OutgoingHistories.p1 XR w Amp) s := by
    have hx : Continuous (fun p : ℝ × ℝ => XR * Real.exp p.1 * OutgoingHistories.Qs w Amp p) :=
      (continuous_const.mul (Real.continuous_exp.comp continuous_fst)).mul
        (OutgoingHistories.Qs_smooth w ha).continuous
    have hL : Continuous (fun p : ℝ × ℝ => 1 - 2 * d.h * p.2 ^ 2) :=
      continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))
    apply hx.continuousOn.div hL.continuousOn
    intro p hp
    exact (CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half
      (OutgoingEntranceCone.parameter_square_le_one (heta p hp))).ne'
  have hane : ∀ p ∈ s, coneA w p ≠ 0 := fun p hp => (hA p hp).ne'
  exact ⟨hp1.mul (continuousOn_const.sub ((hcb.mul hcr).div hca hane)),
    hp1.mul (hcr.add (hcb.div hca hane)),
    hca.mul (continuousOn_const.add ((hcb.div hca hane).pow 2))⟩

/-- Uniform relaxed margins on the full chosen finite outgoing interval. -/
theorem clean_relaxed_margins {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {XR left : ℝ} (h : CleanOutgoingCone w XR left) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ p ∈ cleanWindow d left,
      eps ≤ OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) p ∧
      eps ≤ coneA w p ∧ eps ≤ normalP w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p -
        2 ∧
      eps ≤ ConeAlgebra.coneBound
        (normalP w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p)
        (normalJ w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p) -
          normalV w (CorrectedPulseAmplitude.amplitude d w.coefficients) p := by
  let Amp := CorrectedPulseAmplitude.amplitude d w.coefficients
  have ha : ContDiff ℝ ∞ Amp := CorrectedPulseAmplitude.amplitude_contDiff d w.smooth
  have hk : IsCompact (cleanWindow d left) := isCompact_Icc.prod isCompact_Icc
  have hd := normal_data_continuousOn w ha XR (s := cleanWindow d left)
    (fun p hp => abs_le.mpr hp.2) (fun p hp => (h.relaxed p hp).angular_positive)
    (fun p hp => (h.relaxed p hp).radial_positive)
  obtain ⟨eQ, heQ, HQ⟩ := UniformCone.positive_uniform_margin hk
    (OutgoingHistories.Qs_smooth w ha).continuous.continuousOn (fun p hp => (h.relaxed p
      hp).angular_positive)
  obtain ⟨eA, heA, HA⟩ := UniformCone.positive_uniform_margin hk
    (OutgoingEntranceCone.coneA_continuous w).continuousOn (fun p hp => (h.relaxed p
      hp).radial_positive)
  obtain ⟨eP, heP, HP⟩ := UniformCone.positive_uniform_margin hk (hd.1.sub continuousOn_const)
    (fun p hp => sub_pos.mpr (h.relaxed p hp).stress_gt_two)
  have hroot : ContinuousOn (fun p => ConeAlgebra.coneBound (normalP w Amp XR p) (normalJ w Amp XR
    p) -
      normalV w Amp p) (cleanWindow d left) :=
    (UniformCone.continuous_coneBound.comp_continuousOn (hd.1.prodMk (hd.2.1.prodMk hd.2.2))).sub
      hd.2.2
  obtain ⟨eR, heR, HR⟩ := UniformCone.positive_uniform_margin hk hroot
    (fun p hp => sub_pos.mpr (h.relaxed p hp).root_strict)
  refine ⟨min eQ (min eA (min eP eR)), lt_min heQ (lt_min heA (lt_min heP heR)), ?_⟩
  intro p hp
  exact ⟨(min_le_left _ _).trans (HQ p hp),
    ((min_le_right _ _).trans (min_le_left _ _)).trans (HA p hp),
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans (HP p hp),
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))).trans (HR p hp)⟩

theorem clean_true_margins {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {XR left : ℝ} (h : CleanOutgoingCone w XR left) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ p ∈ trueWindow d,
      eps ≤ normalV w (CorrectedPulseAmplitude.amplitude d w.coefficients) p - 2 ∧
      eps ≤ normalP w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p - 2 ∧
      eps ≤ ConeAlgebra.coneBound
        (normalP w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p)
        (normalJ w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p) -
          normalV w (CorrectedPulseAmplitude.amplitude d w.coefficients) p := by
  have ha := CorrectedPulseAmplitude.amplitude_contDiff d w.smooth
  have hd := normal_data_continuousOn w ha XR (s := trueWindow d)
    (fun p hp => abs_le.mpr hp.2) (fun p hp => (h.true_from_hold p hp).1.angular_positive)
    (fun p hp => (h.true_from_hold p hp).1.radial_positive)
  exact UniformCone.compact_trueCone_margins (isCompact_Icc.prod isCompact_Icc) hd.1 hd.2.1 hd.2.2
    (fun p hp => ⟨(h.true_from_hold p hp).2, (h.true_from_hold p hp).1.stress_gt_two,
      (h.true_from_hold p hp).1.root_strict⟩)

/-- A coordinate perturbation tolerance for later edits on the true region.
The competing coordinates need not be continuous; their closeness must be
proved separately for the actual edit. -/
theorem clean_true_stable {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {XR left : ℝ} (h : CleanOutgoingCone w XR left) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ p ∈ trueWindow d, ∀ P' J' v' : ℝ,
      |P' - normalP w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p| ≤ rho →
      |J' - normalJ w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p| ≤ rho →
      |v' - normalV w (CorrectedPulseAmplitude.amplitude d w.coefficients) p| ≤ rho →
      2 < v' ∧ v' < P' ∧ (v' - 2) * J' ^ 2 < 2 * (P' - v') ^ 2 := by
  have ha := CorrectedPulseAmplitude.amplitude_contDiff d w.smooth
  have hd := normal_data_continuousOn w ha XR (s := trueWindow d)
    (fun p hp => abs_le.mpr hp.2) (fun p hp => (h.true_from_hold p hp).1.angular_positive)
    (fun p hp => (h.true_from_hold p hp).1.radial_positive)
  exact UniformCone.compact_family_quadratic_stable (isCompact_Icc.prod isCompact_Icc) hd.1 hd.2.1
    hd.2.2
    (fun p hp => ⟨(h.true_from_hold p hp).2, (h.true_from_hold p hp).1.stress_gt_two,
      (h.true_from_hold p hp).1.root_strict⟩)

/-! ## Margins independent of the later entrance radius -/

noncomputable def sourceC {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  1 - coneB w Amp p * coneRatio w Amp p / coneA w p

noncomputable def sourceJ {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  coneRatio w Amp p + coneB w Amp p / coneA w p

noncomputable def leadingGap {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * sourceC w Amp p ^ 2 - (normalV w Amp p - 2) * sourceJ w Amp p ^ 2

theorem leading_gap_of_finite {s c j v : ℝ} (hs : 0 < s) (hv : 2 < v)
    (hvP : v < s * c) (hquad : (v - 2) * (s * j) ^ 2 < 2 * (s * c - v) ^ 2) :
    0 < c ∧ 0 < 2 * c ^ 2 - (v - 2) * j ^ 2 := by
  have hc : 0 < c := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hs.le (le_of_not_gt hn)
    linarith
  have hd : (s * c - v) ^ 2 < (s * c) ^ 2 := by
    apply (sq_lt_sq₀ (by linarith : 0 ≤ s * c - v) (mul_pos hs hc).le).mpr
    linarith
  have hgap : s ^ 2 * ((v - 2) * j ^ 2) < s ^ 2 * (2 * c ^ 2) := by
    nlinarith only [hquad, hd]
  exact ⟨hc, sub_pos.mpr ((mul_lt_mul_iff_right₀ (sq_pos_of_pos hs)).mp hgap)⟩

theorem clean_true_source_positive {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {XR left : ℝ} (h : CleanOutgoingCone w XR left) (hXR : 0 < XR)
    {p : ℝ × ℝ} (hp : p ∈ trueWindow d) :
    0 < OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) p ∧
    0 < coneA w p ∧ 2 < normalV w (CorrectedPulseAmplitude.amplitude d w.coefficients) p ∧
    0 < sourceC w (CorrectedPulseAmplitude.amplitude d w.coefficients) p ∧
    0 < leadingGap w (CorrectedPulseAmplitude.amplitude d w.coefficients) p := by
  let Amp := CorrectedPulseAmplitude.amplitude d w.coefficients
  have ht := h.true_from_hold p hp
  have hp1 : 0 < OutgoingHistories.p1 XR w Amp p := by
    rw [OutgoingHistories.p1_dilation]
    exact mul_pos hXR (actual_p1_pos w Amp (abs_le.mpr hp.2) ht.1.angular_positive)
  have hc := (ConeAlgebra.true_cone_iff ht.2).mp ⟨ht.1.stress_gt_two, ht.1.root_strict⟩
  have hg := leading_gap_of_finite (s := OutgoingHistories.p1 XR w Amp p)
    (c := sourceC w Amp p) (j := sourceJ w Amp p) (v := normalV w Amp p) hp1 ht.2 hc.1 hc.2
  exact ⟨ht.1.angular_positive, ht.1.radial_positive, ht.2, hg.1, hg.2⟩

/-- All five quantities in this margin are independent of `XR`. A single
realized true cone therefore supplies a margin for later radius choices. -/
theorem clean_true_source_margins {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {XR left : ℝ} (h : CleanOutgoingCone w XR left) (hXR : 0 < XR) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ p ∈ trueWindow d,
      eps ≤ OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) p ∧
      eps ≤ coneA w p ∧ eps ≤ normalV w (CorrectedPulseAmplitude.amplitude d w.coefficients) p - 2 ∧
      eps ≤ sourceC w (CorrectedPulseAmplitude.amplitude d w.coefficients) p ∧
      eps ≤ leadingGap w (CorrectedPulseAmplitude.amplitude d w.coefficients) p := by
  let Amp := CorrectedPulseAmplitude.amplitude d w.coefficients
  have ha : ContDiff ℝ ∞ Amp := CorrectedPulseAmplitude.amplitude_contDiff d w.smooth
  have hk : IsCompact (trueWindow d) := isCompact_Icc.prod isCompact_Icc
  have hpositive {p : ℝ × ℝ} (hp : p ∈ trueWindow d) := clean_true_source_positive w h hXR hp
  have hca := (OutgoingEntranceCone.coneA_continuous w).continuousOn (s := trueWindow d)
  have hcb := (OutgoingEntranceCone.coneB_continuous w ha).continuousOn (s := trueWindow d)
  have hcr : ContinuousOn (coneRatio w Amp) (trueWindow d) := by
    apply (OutgoingHistories.Ns_smooth w ha).continuous.continuousOn.div
      ((OutgoingHistories.E_smooth w).continuous.mul (OutgoingHistories.Qs_smooth w
        ha).continuous).continuousOn
    intro p hp
    exact (mul_pos (OutgoingHistories.E_pos w p) (hpositive hp).1).ne'
  have hane : ∀ p ∈ trueWindow d, coneA w p ≠ 0 := fun p hp => (hpositive hp).2.1.ne'
  have hC : ContinuousOn (sourceC w Amp) (trueWindow d) :=
    continuousOn_const.sub ((hcb.mul hcr).div hca hane)
  have hJ : ContinuousOn (sourceJ w Amp) (trueWindow d) := hcr.add (hcb.div hca hane)
  have hV : ContinuousOn (normalV w Amp) (trueWindow d) :=
    hca.mul (continuousOn_const.add ((hcb.div hca hane).pow 2))
  have hG : ContinuousOn (leadingGap w Amp) (trueWindow d) :=
    (continuousOn_const.mul (hC.pow 2)).sub ((hV.sub continuousOn_const).mul (hJ.pow 2))
  obtain ⟨eQ, heQ, HQ⟩ := UniformCone.positive_uniform_margin hk
    (OutgoingHistories.Qs_smooth w ha).continuous.continuousOn (fun p hp => (hpositive hp).1)
  obtain ⟨eA, heA, HA⟩ := UniformCone.positive_uniform_margin hk hca (fun p hp => (hpositive
    hp).2.1)
  obtain ⟨eV, heV, HV⟩ := UniformCone.positive_uniform_margin hk (hV.sub continuousOn_const)
    (fun p hp => sub_pos.mpr (hpositive hp).2.2.1)
  obtain ⟨eC, heC, HC⟩ := UniformCone.positive_uniform_margin hk hC (fun p hp => (hpositive
    hp).2.2.2.1)
  obtain ⟨eG, heG, HG⟩ := UniformCone.positive_uniform_margin hk hG (fun p hp => (hpositive
    hp).2.2.2.2)
  refine ⟨min eQ (min eA (min eV (min eC eG))), lt_min heQ (lt_min heA (lt_min heV (lt_min heC
    heG))), ?_⟩
  intro p hp
  exact ⟨(min_le_left _ _).trans (HQ p hp),
    ((min_le_right _ _).trans (min_le_left _ _)).trans (HA p hp),
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans (HV p hp),
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _
      _)))).trans (HC p hp),
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _
      _)))).trans (HG p hp)⟩

end NavierStokes.OutgoingCone
