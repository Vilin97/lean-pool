/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatedOutgoing
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalEdgeFactor

@[expose] public section

/-!
# The full fully-switched terminal cone

The release estimate is uniform on the whole remaining logarithmic interval.
The closed profile band is treated with the actual smooth heat extension,
not with a compact subset of a physical chart.  The compensation witness is
arbitrary throughout.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.TerminalCone

/-- The clock at which the heat switch is complete. -/
noncomputable def terminalStart (d : OutgoingTail.TailData) : ℝ := OutgoingTail.tailStart d + 1 / 2

noncomputable def normalization (F : OutgoingProfile.Profile) (XR : ℝ) : ℝ :=
  TerminalPressure.releasedNormalization F.data (OutgoingDilation.switchRadius F XR)

noncomputable def shift (F : OutgoingProfile.Profile) (XR : ℝ) : ℝ :=
  Real.log (OutgoingDilation.switchRadius F XR) - 1 / 5

noncomputable def edgeDistance (F : OutgoingProfile.Profile) (y : ℝ) : ℝ :=
  OutgoingTail.tailEnd F.data - y

noncomputable def profilePoint (F : OutgoingProfile.Profile) (y eta : ℝ) : ℝ × ℝ :=
  (eta, edgeDistance F y)

/-- The release time and release amplitude depend on the core schedule before
the terminal exponent is chosen. -/
noncomputable def releaseTime (c : OutgoingSchedule.Parameters) : ℝ :=
  c.endpoint + OutgoingTail.flattenLength + 30 * Real.log (1 / c.lam)

noncomputable def releaseAmplitude (c : OutgoingSchedule.Parameters) : ℝ :=
  OutgoingSchedule.radialAmplitude c.P c.dropLength c.lam (releaseTime c) / 2

noncomputable def annulusRatio : ℝ := Real.exp 3

noncomputable def releaseBudget (c : OutgoingSchedule.Parameters) : ℝ :=
  16 * annulusRatio * (annulusRatio - 1) * releaseAmplitude c

/-- The order is explicit: these bounds use only the already fixed core
schedule, then constrain `h`; the entrance radius is chosen afterwards. -/
def SmallTail (d : OutgoingTail.TailData) : Prop :=
  d.h ≤ 1 / 4 ∧ d.h ≤ 1 / (1 + releaseBudget d.core)

theorem releaseAmplitude_eq (d : OutgoingTail.TailData) :
    releaseAmplitude d.core = OutgoingTail.finalAngular d (d.releaseStart, 0) := by
  rw [OutgoingTail.finalAngular_uniform_wait d 0 (OutgoingTail.releaseStart_gt_flattenEnd d).le
    le_rfl]
  rfl

theorem normalization_pos (F : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) :
    0 < normalization F XR := TerminalPressure.releasedNormalization_pos F.data
      (OutgoingDilation.switchRadius_pos F XR hXR)

theorem edgeDistance_bounds (F : OutgoingProfile.Profile) {y : ℝ}
    (hy : terminalStart F.data ≤ y) (hy' : y < OutgoingTail.tailEnd F.data) :
    0 < edgeDistance F y ∧ edgeDistance F y ≤ 5 / 2 := by
  dsimp [terminalStart, edgeDistance, OutgoingTail.tailEnd] at *
  constructor <;> linarith

theorem shift_log (F : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) :
    shift F XR = Real.log XR + OutgoingTail.tailStart F.data := by
  rw [shift, OutgoingDilation.switchRadius_eq, Real.log_mul hXR.ne' (Real.exp_ne_zero _),
    Real.log_exp]
  ring

theorem profileS_clock (F : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    TerminalEdgeFactor.profileS (shift F XR) (edgeDistance F y) = XR * Real.exp y := by
  rw [shift_log F hXR]
  unfold TerminalEdgeFactor.profileS edgeDistance OutgoingTail.tailEnd
  rw [show Real.log XR + OutgoingTail.tailStart F.data + 3 -
      (OutgoingTail.tailStart F.data + 3 - y) = Real.log XR + y by ring,
    Real.exp_add, Real.exp_log hXR]

theorem profileS_ge_switch {K δ : ℝ} (hK : 0 < K) (hδ : δ ≤ 5 / 2) :
    K ≤ TerminalEdgeFactor.profileS (Real.log K - 1 / 5) δ := by
  rw [TerminalEdgeFactor.profileS,
    show Real.log K - 1 / 5 + 3 - δ = Real.log K + (14 / 5 - δ) by ring,
    Real.exp_add, Real.exp_log hK]
  exact le_mul_of_one_le_right hK.le (Real.one_le_exp (by linarith))

theorem profileRadius_le_outer (y0 : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    TerminalEdgeFactor.profileRadius y0 δ ≤ TerminalEdgeFactor.profileRadius y0 0 := by
  unfold TerminalEdgeFactor.profileRadius
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))

theorem profileRadius_annulus (y0 : ℝ) {δ : ℝ} (hδ : δ ≤ 5 / 2) :
    TerminalEdgeFactor.profileRadius y0 0 ^ 2 ≤
      annulusRatio * TerminalEdgeFactor.profileRadius y0 δ ^ 2 := by
  rw [TerminalEdgeFactor.profileRadius_square, TerminalEdgeFactor.profileRadius_square]
  unfold TerminalEdgeFactor.profileS annulusRatio
  have he : Real.exp (y0 + 3 - 0) ≤ Real.exp 3 * Real.exp (y0 + 3 - δ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  nlinarith

theorem le_on_closed_band {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ eta ∈ Ioo (-1 : ℝ) 1, f eta ≤ g eta) {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    f eta ≤ g eta := by
  apply le_on_closure h hf.continuousOn hg.continuousOn
  simpa only [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using heta

theorem eta_sq_lt_one {eta : ℝ} (heta : eta ∈ Ioo (-1 : ℝ) 1) : eta ^ 2 < 1 := by
  nlinarith [mul_pos (show 0 < eta + 1 by linarith [heta.1])
    (show 0 < 1 - eta by linarith [heta.2])]

/-! ## Uniform small-argument heat slope, including zero diffusion -/

noncomputable def heatSlope (d : OutgoingTail.TailData) (z : ℝ) : ℝ :=
  -z * deriv (HeatProfileExtension.extension (1 + d.h)) z /
    HeatProfileExtension.extension (1 + d.h) z

theorem extension_deriv_eq (d : OutgoingTail.TailData) {z : ℝ} (hz : 0 ≤ z) :
    deriv (HeatProfileExtension.extension (1 + d.h)) z =
      derivWithin (RadialHeatProfile.profile (1 + d.h)) (Ici 0) z := by
  rw [← iteratedDeriv_one, HeatProfileExtension.iteratedDeriv_extension_eq_profileJet
    (by linarith [d.h_pos]) 1 hz, ← RadialHeatProfile.iteratedDerivWithin_profile
      (by linarith [d.h_pos]) 1 hz, iteratedDerivWithin_one]

theorem heatSlope_bounds (d : OutgoingTail.TailData) (hh : d.h ≤ 1 / 4)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1 / 16) :
    0 ≤ heatSlope d z ∧ heatSlope d z ≤ d.h / 4 := by
  have hH := HeatProfileExtension.extension_pos (a := 1 + d.h) (by linarith [d.h_pos]) hz
  have hder := RadialHeatProfile.profile_first_derivative_bound (a := 1 + d.h) (by linarith
    [d.h_pos]) hz
  have hneg := RadialHeatProfile.profile_derivWithin_neg (a := 1 + d.h) (by linarith [d.h_pos]) hz
  rw [← extension_deriv_eq d hz] at hder hneg
  have hdev := RadialHeatProfile.profile_h_sub_one_bound d.h_pos hz
  rw [← HeatProfileExtension.extension_eq_profile (1 + d.h) hz] at hdev
  have hdh : (1 + d.h) * d.h ≤ 2 * d.h := by nlinarith [d.h_pos]
  have hn : -deriv (HeatProfileExtension.extension (1 + d.h)) z ≤ 2 * d.h := by
    have he := (abs_le.mp hder).1
    nlinarith
  have hprod : 2 * d.h * z ≤ d.h / 8 := by nlinarith [d.h_pos]
  have hhprod : d.h * (1 + d.h) * z ≤ d.h / 8 :=
    (mul_le_mul_of_nonneg_right (by nlinarith : d.h * (1 + d.h) ≤ 2 * d.h) hz).trans hprod
  have hHhalf : 1 / 2 ≤ HeatProfileExtension.extension (1 + d.h) z := by
    have hl := (abs_le.mp hdev).1
    linarith
  unfold heatSlope
  constructor
  · exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hz) hneg.le) hH.le
  · apply (div_le_iff₀ hH).mpr
    have hnprod := mul_le_mul_of_nonneg_left hn hz
    nlinarith [mul_le_mul_of_nonneg_left hHhalf (div_nonneg d.h_pos.le (by norm_num : (0 : ℝ) ≤ 4))]

theorem profileZ_small (_d : OutgoingTail.TailData) {K δ eta : ℝ}
    (hK : 32 ≤ K) (hδ : δ ≤ 5 / 2) (heta : eta ^ 2 ≤ 1) :
    0 ≤ TerminalEdgeFactor.profileZ (Real.log K - 1 / 5) (eta, δ) ∧
      TerminalEdgeFactor.profileZ (Real.log K - 1 / 5) (eta, δ) ≤ 1 / 16 := by
  have hKp : 0 < K := by linarith
  have hS := profileS_ge_switch hKp hδ
  refine ⟨TerminalEdgeFactor.profileZ_nonneg _ heta, ?_⟩
  unfold TerminalEdgeFactor.profileZ
  apply (div_le_iff₀ (TerminalEdgeFactor.profileS_pos _ _)).mpr
  dsimp only
  nlinarith [sq_nonneg eta]

theorem profileSpeed_eq {C : ℝ} (hC : 0 < C) (d : OutgoingTail.TailData) (y0 : ℝ)
    {eta δ : ℝ} (heta : eta ^ 2 ≤ 1) :
    TerminalEdgeFactor.profileSpeed C d y0 (eta, δ) =
      2 + 2 * d.h - 2 * heatSlope d (TerminalEdgeFactor.profileZ y0 (eta, δ)) -
        2 * OutgoingTail.tailShapeDeriv d (3 - δ) / OutgoingTail.tailShape d (3 - δ) := by
  have hs := TerminalEdgeFactor.profileS_pos y0 δ
  have hH := HeatProfileExtension.extension_pos (a := 1 + d.h) (by linarith [d.h_pos])
    (TerminalEdgeFactor.profileZ_nonneg y0 (y := (eta, δ)) heta)
  have hp := Real.rpow_pos_of_pos hs (RadialHeatProfile.spatialExponent (1 + d.h))
  unfold TerminalEdgeFactor.profileSpeed TerminalEdgeFactor.profileCarrierRadial
    TerminalEdgeFactor.profileCarrier heatSlope
  dsimp only
  rw [Real.rpow_sub hs, Real.rpow_one]
  field_simp [hC.ne', hs.ne', hp.ne', hH.ne', (OutgoingTail.tailShape_pos d (3 - δ)).ne']
  unfold RadialHeatProfile.spatialExponent
  ring_nf
  rw [TerminalEdgeFactor.profileRadius_square]
  ring

theorem profileSpeed_bounds {C : ℝ} (hC : 0 < C) (d : OutgoingTail.TailData) (hh : d.h ≤ 1 / 4)
    {K δ eta : ℝ} (hK : 32 ≤ K) (hδ : δ ≤ 5 / 2) (heta : eta ^ 2 ≤ 1) :
    2 + d.h < TerminalEdgeFactor.profileSpeed C d (Real.log K - 1 / 5) (eta, δ) ∧
      TerminalEdgeFactor.profileSpeed C d (Real.log K - 1 / 5) (eta, δ) ≤ 2 + 2 * d.h := by
  have hz := profileZ_small d hK hδ heta
  have hheat := heatSlope_bounds d hh hz.1 hz.2
  have hf := OutgoingTail.tail_taper_log_derivative d (3 - δ)
  rw [profileSpeed_eq hC d _ heta]
  have he : 2 * OutgoingTail.tailShapeDeriv d (3 - δ) / OutgoingTail.tailShape d (3 - δ) =
      2 * (OutgoingTail.tailShapeDeriv d (3 - δ) / OutgoingTail.tailShape d (3 - δ)) := by ring
  rw [he]
  constructor <;> linarith

/-! ## Physical-section identities and extension to the closed band -/

theorem normalized_X (d : OutgoingTail.TailData) (y0 δ : ℝ) {eta : ℝ} (heta : eta ^ 2 < 1) :
    SimilarityProfile.X d.h (TerminalStress.radiusPoint (eta ^ 2)
      (TerminalEdgeFactor.profileRadius y0 δ) eta) = TerminalEdgeFactor.profileS y0 δ := by
  rw [show TerminalStress.radiusPoint (eta ^ 2) (TerminalEdgeFactor.profileRadius y0 δ) eta =
      PhysicalHeatCoordinates.normalizedSection (TerminalEdgeFactor.profileRadius y0 δ ^ 2 / 2) eta
        by rfl,
    PhysicalHeatCoordinates.X_normalizedSection d.h_pos d.h_lt_half heta,
    TerminalEdgeFactor.profileRadius_square]
  ring

theorem normalized_logX (d : OutgoingTail.TailData) (y0 δ : ℝ) {eta : ℝ} (heta : eta ^ 2 < 1) :
    Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint (eta ^ 2)
      (TerminalEdgeFactor.profileRadius y0 δ) eta)) = y0 + 3 - δ := by
  rw [normalized_X d y0 δ heta, TerminalEdgeFactor.profileS, Real.log_exp]

theorem normalized_denominator (d : OutgoingTail.TailData) {eta : ℝ} (heta : eta ^ 2 < 1) :
    TerminalStress.timeDenominator d.h (eta ^ 2) eta = TerminalEdgeFactor.profileL d eta := by
  have he := TerminalEdgeFactor.denominator_normalizedParam d heta
  change TerminalStress.timeDenominator d.h
    (TerminalEdgeFactor.timeOf (TerminalEdgeFactor.normalizedParam eta)) eta = _ at he
  rw [TerminalEdgeFactor.timeOf_normalizedParam heta] at he
  exact he

theorem normalized_carrier (C : ℝ) (d : OutgoingTail.TailData) (y0 δ : ℝ) {eta : ℝ}
    (heta : eta ^ 2 < 1) :
    TerminalStress.heatAmplitude C (1 + d.h) (eta ^ 2) (TerminalEdgeFactor.profileRadius y0 δ) =
      TerminalEdgeFactor.profileCarrier C d y0 (eta, δ) := by
  have he := TerminalEdgeFactor.carrier_normalizedParam C d y0 δ heta
  simpa only [TerminalEdgeFactor.carrier_eq, TerminalEdgeFactor.timeOf_normalizedParam heta,
    TerminalEdgeFactor.radius_normalizedParam d y0 δ heta] using he

theorem normalized_angularStress (C : ℝ) (d : OutgoingTail.TailData) (y0 δ : ℝ) {eta : ℝ}
    (heta : eta ^ 2 < 1) :
    TerminalStress.terminalStress C d.h (TerminalPressure.outgoingTaper d y0)
      (eta ^ 2) eta (TerminalEdgeFactor.profileRadius y0 δ) =
        TerminalEdgeFactor.profileAngularStress C d y0 (eta, δ) := by
  have he := TerminalEdgeFactor.angularStress_normalizedParam C d y0 δ heta
  change TerminalStress.terminalStress C d.h (TerminalPressure.outgoingTaper d y0)
    (TerminalEdgeFactor.timeOf (TerminalEdgeFactor.normalizedParam eta)) eta
    (TerminalEdgeFactor.radius d y0 (TerminalEdgeFactor.normalizedParam eta, δ)) = _ at he
  rw [TerminalEdgeFactor.timeOf_normalizedParam heta,
    TerminalEdgeFactor.radius_normalizedParam d y0 δ heta] at he
  exact he

theorem normalized_axialStress (C : ℝ) (d : OutgoingTail.TailData) (y0 δ : ℝ) {eta : ℝ}
    (heta : eta ^ 2 < 1) :
    TerminalPressure.axialBackwardStress C d.h (TerminalPressure.outgoingTaper d y0)
      (eta ^ 2) eta (TerminalEdgeFactor.profileRadius y0 δ) =
        TerminalEdgeFactor.profileAxialStress C d y0 (eta, δ) := by
  have he := TerminalEdgeFactor.axialStress_normalizedParam C d y0 δ heta
  change TerminalPressure.axialBackwardStress C d.h (TerminalPressure.outgoingTaper d y0)
    (TerminalEdgeFactor.timeOf (TerminalEdgeFactor.normalizedParam eta)) eta
    (TerminalEdgeFactor.radius d y0 (TerminalEdgeFactor.normalizedParam eta, δ)) = _ at he
  rw [TerminalEdgeFactor.timeOf_normalizedParam heta,
    TerminalEdgeFactor.radius_normalizedParam d y0 δ heta] at he
  exact he

noncomputable def profileMass (C : ℝ) (d : OutgoingTail.TailData) (y0 δ eta : ℝ) : ℝ :=
  (TerminalEdgeFactor.profileRadius y0 δ * TerminalEdgeFactor.profileCarrier C d y0 (eta, 0) /
    (2 * TerminalEdgeFactor.profileL d eta)) * (1 - OutgoingTail.tailShape d (3 - δ))

theorem profileMass_continuous (C : ℝ) (d : OutgoingTail.TailData) (y0 δ : ℝ) :
    Continuous (profileMass C d y0 δ) := by
  apply Continuous.mul
  · exact (continuous_const.mul ((TerminalEdgeFactor.profileCarrier_contDiff C d y0).continuous.comp
      (continuous_id.prodMk continuous_const))).div
        (continuous_const.mul (TerminalEdgeFactor.profileL_contDiff d).continuous)
        (fun eta => mul_ne_zero (by norm_num) (TerminalEdgeFactor.profileL_pos d eta).ne')
  · exact continuous_const

theorem profileMass_le_stress {C : ℝ} (hC : 0 < C) (d : OutgoingTail.TailData) (y0 : ℝ)
    {δ eta : ℝ} (hδ : 0 < δ) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    profileMass C d y0 δ eta ≤ TerminalEdgeFactor.profileAngularStress C d y0 (eta, δ) := by
  apply le_on_closed_band (profileMass_continuous C d y0 δ)
    (((TerminalEdgeFactor.profileStress_contDiff C d y0).continuous.comp
      (continuous_id.prodMk continuous_const)).fst) _ heta
  intro e he
  have he2 := eta_sq_lt_one he
  have hR : y0 + 3 ≤ Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint (e ^ 2)
      (TerminalEdgeFactor.profileRadius y0 0) e)) := by
    rw [normalized_logX d y0 0 he2]
    simp only [sub_zero, le_refl]
  have hm := TerminalPressure.terminalStress_ge_mass hC d.h_pos d.h_lt_half he2
    (TerminalEdgeFactor.profileRadius_pos y0 δ) (profileRadius_le_outer y0 hδ.le)
    (TerminalPressure.outgoingTaper_contDiff d y0) (TerminalPressure.outgoingTaper_deriv_nonneg d
      y0)
    (TerminalPressure.outgoingTaper_plateau d y0) hR
  rw [normalized_carrier C d y0 0 he2, normalized_denominator d he2,
    normalized_angularStress C d y0 δ he2, TerminalPressure.outgoingTaper, normalized_logX d y0 δ
      he2,
    show y0 + 3 - δ - y0 = 3 - δ by ring] at hm
  exact hm

theorem profileAngularStress_pos {C : ℝ} (hC : 0 < C) (d : OutgoingTail.TailData) (y0 : ℝ)
    {δ eta : ℝ} (hδ : 0 < δ) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    0 < TerminalEdgeFactor.profileAngularStress C d y0 (eta, δ) := by
  apply lt_of_lt_of_le _ (profileMass_le_stress hC d y0 hδ heta)
  have ht : OutgoingTail.tailShape d (3 - δ) < 1 := by
    simpa only [TerminalPressure.outgoingTaper, sub_zero] using
      TerminalPressure.outgoingTaper_lt_one d (y0 := 0) (y := 3 - δ) (by linarith)
  unfold profileMass
  exact mul_pos (div_pos (mul_pos (TerminalEdgeFactor.profileRadius_pos y0 δ)
    (TerminalEdgeFactor.profileCarrier_pos hC d y0 (y := (eta, 0))
      (TerminalEdgeFactor.eta_sq_le_one heta)))
      (mul_pos (by norm_num) (TerminalEdgeFactor.profileL_pos d eta))) (sub_pos.mpr ht)

theorem releaseAmplitude_pos (c : OutgoingSchedule.Parameters) : 0 < releaseAmplitude c := by
  unfold releaseAmplitude OutgoingSchedule.radialAmplitude
  exact div_pos (mul_pos c.P_pos (Real.exp_pos _)) (by norm_num)

theorem annulusRatio_gt_one : 1 < annulusRatio := Real.one_lt_exp_iff.mpr (by norm_num)

theorem releaseBudget_nonneg (c : OutgoingSchedule.Parameters) : 0 ≤ releaseBudget c := by
  unfold releaseBudget
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans annulusRatio_gt_one).le)
    (sub_nonneg.mpr annulusRatio_gt_one.le)) (releaseAmplitude_pos c).le

theorem release_small (d : OutgoingTail.TailData) (hsmall : SmallTail d) :
    releaseBudget d.core * d.h ^ 4 ≤ 1 := by
  have hB := releaseBudget_nonneg d.core
  have hh1 : d.h ≤ 1 := by linarith [hsmall.1]
  have hhpow : d.h ^ 4 ≤ d.h := by
    calc
      _ = d.h * d.h ^ 3 := by ring
      _ ≤ d.h * 1 ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ d.h_pos.le hh1 3) d.h_pos.le
      _ = _ := by ring
  have hs := (le_div_iff₀ (show 0 < 1 + releaseBudget d.core by linarith)).mp hsmall.2
  nlinarith [mul_le_mul_of_nonneg_left hhpow hB, d.h_pos]

theorem profileAxialStress_le_angular (d : OutgoingTail.TailData) (hsmall : SmallTail d)
    {K δ eta : ℝ} (hK : 0 < K) (hδ : 0 < δ) (hδ' : δ ≤ 5 / 2)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    |TerminalEdgeFactor.profileAxialStress (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ)| ≤
    TerminalEdgeFactor.profileAngularStress (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ) := by
  let C := TerminalPressure.releasedNormalization d K
  let y0 := Real.log K - 1 / 5
  have hC : 0 < C := TerminalPressure.releasedNormalization_pos d hK
  apply le_on_closed_band
    (((TerminalEdgeFactor.profileStress_contDiff C d y0).continuous.comp
      (continuous_id.prodMk continuous_const)).snd.abs)
    (((TerminalEdgeFactor.profileStress_contDiff C d y0).continuous.comp
      (continuous_id.prodMk continuous_const)).fst) _ heta
  intro e he
  have he2 := eta_sq_lt_one he
  have hX : K ≤ SimilarityProfile.X d.h (TerminalStress.radiusPoint (e ^ 2)
      (TerminalEdgeFactor.profileRadius y0 δ) e) := by
    rw [normalized_X d y0 δ he2]
    exact profileS_ge_switch hK hδ'
  have hR : y0 + 3 ≤ Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint (e ^ 2)
      (TerminalEdgeFactor.profileRadius y0 0) e)) := by
    rw [normalized_logX d y0 0 he2]
    simp only [sub_zero, le_refl]
  have hins : Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint (e ^ 2)
      (TerminalEdgeFactor.profileRadius y0 δ) e)) < y0 + 3 := by
    rw [normalized_logX d y0 δ he2]
    linarith
  have hb := TerminalPressure.released_terminal_tilt d hK hsmall.1 he2
    (TerminalEdgeFactor.profileRadius_pos y0 δ) (profileRadius_le_outer y0 hδ.le)
    annulusRatio_gt_one.le (profileRadius_annulus y0 hδ') hX hR hins
  rw [normalized_angularStress C d y0 δ he2, normalized_axialStress C d y0 δ he2] at hb
  have hb' : |TerminalEdgeFactor.profileAxialStress C d y0 (e, δ)| /
      TerminalEdgeFactor.profileAngularStress C d y0 (e, δ) ≤ releaseBudget d.core * d.h ^ 4 := by
    simpa only [releaseBudget, releaseAmplitude_eq d] using hb.2
  exact (div_le_one hb.1).mp (hb'.trans (release_small d hsmall))

/-! ## Uniform cone margin through the actual terminal edge -/

theorem profileAngularFactor_pos {C : ℝ} (hC : 0 < C) (d : OutgoingTail.TailData) (y0 : ℝ)
    {δ eta : ℝ} (hδ : 0 ≤ δ) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    0 < TerminalEdgeFactor.profileAngularFactor C d y0 (eta, δ) := by
  rcases hδ.eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact TerminalEdgeFactor.profileAngularFactor_zero_pos hC d y0 heta
  · have hT := profileAngularStress_pos hC d y0 hpos heta
    rw [TerminalEdgeFactor.profileAngularStress_factorization] at hT
    exact (mul_pos_iff_of_pos_left (div_pos (FlatCutoff.edge_pos 4 hpos) (pow_pos hpos 3))).mp hT

theorem profileTilt_contDiffAt {C : ℝ} (hC : 0 < C) (d : OutgoingTail.TailData) (y0 : ℝ)
    {δ eta : ℝ} (hδ : 0 ≤ δ) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ (TerminalEdgeFactor.profileTilt C d y0) (eta, δ) :=
  ((contDiffAt_snd.pow 6).mul
    (TerminalEdgeFactor.profileAxialFactor_contDiff C d y0).contDiffAt).div
      (TerminalEdgeFactor.profileAngularFactor_contDiff C d y0).contDiffAt
      (profileAngularFactor_pos hC d y0 hδ heta).ne'

theorem profileTilt_abs_le_one (d : OutgoingTail.TailData) (hsmall : SmallTail d)
    {K δ eta : ℝ} (hK : 0 < K) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 2)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    |TerminalEdgeFactor.profileTilt (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ)| ≤ 1 := by
  rcases hδ.eq_or_lt with hzero | hpos
  · rw [← hzero, TerminalEdgeFactor.profileTilt_zero]
    norm_num
  · have hT := profileAngularStress_pos (TerminalPressure.releasedNormalization_pos d hK)
      d (Real.log K - 1 / 5) hpos heta
    rw [← TerminalEdgeFactor.profileTilt_eq_ratio _ d _ eta hpos, abs_div, abs_of_pos hT]
    exact (div_le_one hT).mpr (profileAxialStress_le_angular d hsmall hK hpos hδ' heta)

/-- A numerical direction margin on the entire remaining interval, including
both closed parameter endpoints and the stress-free terminal edge. -/
theorem profile_cone_margin (d : OutgoingTail.TailData) (hsmall : SmallTail d)
    {K δ eta : ℝ} (hK : 32 ≤ K) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 2)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    2 + d.h < TerminalEdgeFactor.profileSpeed (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ) ∧
    TerminalEdgeFactor.profileSpeed (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ) ≤ 2 + 2 * d.h ∧
    3 / 2 ≤ TerminalEdgeFactor.profileConeGap (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ) := by
  have hKp : 0 < K := by linarith
  have hs := profileSpeed_bounds (TerminalPressure.releasedNormalization_pos d hKp) d
    hsmall.1 hK hδ' (TerminalEdgeFactor.eta_sq_le_one heta)
  have ht := profileTilt_abs_le_one d hsmall hKp hδ hδ' heta
  refine ⟨hs.1, hs.2, ?_⟩
  have ht2 : TerminalEdgeFactor.profileTilt (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ) ^ 2 ≤ 1 := by
    rcases abs_le.mp ht with ⟨hl, hu⟩
    nlinarith
  have hv : 0 ≤ TerminalEdgeFactor.profileSpeed (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ) - 2 := by linarith [d.h_pos]
  have hm := mul_le_mul_of_nonneg_left ht2 hv
  unfold TerminalEdgeFactor.profileConeGap
  nlinarith [hsmall.1]

theorem profile_relative_cone (d : OutgoingTail.TailData) (hsmall : SmallTail d)
    {K δ eta : ℝ} (hK : 32 ≤ K) (hδ : 0 < δ) (hδ' : δ ≤ 5 / 2)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    let C := TerminalPressure.releasedNormalization d K
    let y0 := Real.log K - 1 / 5
    0 < TerminalEdgeFactor.profileAngularStress C d y0 (eta, δ) ∧
    2 < TerminalEdgeFactor.profileSpeed C d y0 (eta, δ) ∧
    (TerminalEdgeFactor.profileSpeed C d y0 (eta, δ) - 2) *
      TerminalEdgeFactor.profileAxialStress C d y0 (eta, δ) ^ 2 <
        2 * TerminalEdgeFactor.profileAngularStress C d y0 (eta, δ) ^ 2 := by
  dsimp only
  have hKp : 0 < K := by linarith
  have hT := profileAngularStress_pos (TerminalPressure.releasedNormalization_pos d hKp)
    d (Real.log K - 1 / 5) hδ heta
  obtain ⟨hs, _, hg⟩ := profile_cone_margin d hsmall hK hδ.le hδ' heta
  refine ⟨hT, by linarith [d.h_pos], ?_⟩
  have hnorm : (TerminalEdgeFactor.profileSpeed (TerminalPressure.releasedNormalization d K) d
      (Real.log K - 1 / 5) (eta, δ) - 2) *
      (TerminalEdgeFactor.profileAxialStress (TerminalPressure.releasedNormalization d K) d
          (Real.log K - 1 / 5) (eta, δ) /
        TerminalEdgeFactor.profileAngularStress (TerminalPressure.releasedNormalization d K) d
          (Real.log K - 1 / 5) (eta, δ)) ^ 2 < 2 := by
    rw [TerminalEdgeFactor.profileTilt_eq_ratio _ d _ eta hδ]
    unfold TerminalEdgeFactor.profileConeGap at hg
    linarith
  apply (div_lt_iff₀ (sq_pos_of_pos hT)).mp
  simpa only [div_pow, mul_div_assoc] using hnorm

/-- The root-form true cone for the actual heat/taper backward stress, with
`P-a=Tθ/F` and `J=Tz/F`, on the full switched interval. -/
theorem profile_full_true_cone (d : OutgoingTail.TailData) (hsmall : SmallTail d)
    {K δ eta : ℝ} (hK : 32 ≤ K) (hδ : 0 < δ) (hδ' : δ ≤ 5 / 2)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    let C := TerminalPressure.releasedNormalization d K
    let y0 := Real.log K - 1 / 5
    2 < TerminalEdgeFactor.profileP C d y0 (eta, δ) ∧
    TerminalEdgeFactor.profileSpeed C d y0 (eta, δ) <
      ConeAlgebra.coneBound (TerminalEdgeFactor.profileP C d y0 (eta, δ))
        (TerminalEdgeFactor.profileJ C d y0 (eta, δ)) := by
  dsimp only
  obtain ⟨hT, hv, hm⟩ := profile_relative_cone d hsmall hK hδ hδ' heta
  have hKp : 0 < K := by linarith
  have hF := TerminalEdgeFactor.profileSwirlCoefficient_pos
    (TerminalPressure.releasedNormalization_pos d hKp) d (Real.log K - 1 / 5)
    (y := (eta, δ)) heta
  apply (ConeAlgebra.true_cone_iff hv).mpr
  constructor
  · exact lt_add_of_pos_right _ (div_pos hT hF)
  · have hd := div_lt_div_of_pos_right hm (sq_pos_of_pos hF)
    simp only [TerminalEdgeFactor.profileP, TerminalEdgeFactor.profileJ,
      add_sub_cancel_left, div_pow]
    simpa only [mul_div_assoc] using hd

/-! ## The identical compensated outgoing field and the ordered radius choice -/

theorem tailTime_clock (F : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    Real.log ((XR * Real.exp y) / OutgoingDilation.switchRadius F XR) + 1 / 5 =
      y - OutgoingTail.tailStart F.data := by
  have hc := OutgoingDilation.clock_center XR (OutgoingDilation.radius XR y)
    (HeatTailEdit.switchStart F.data) hXR (OutgoingDilation.radius_pos XR y hXR)
  rw [OutgoingDilation.clock_radius XR y hXR] at hc
  change OutgoingTail.tailStart F.data + 1 / 5 +
    Real.log ((XR * Real.exp y) / OutgoingDilation.switchRadius F XR) = y at hc
  linarith

theorem E_eq_profileAngularVelocity (F : OutgoingProfile.Profile) {XR : ℝ}
    (c : ℝ → TerminalCompensation.Coeff) (hXR : 0 < XR) {y eta : ℝ}
    (hy : terminalStart F.data ≤ y) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    HeatedOutgoing.E F XR c (XR * Real.exp y, eta) =
      TerminalEdgeFactor.profileAngularVelocity (normalization F XR) F.data (shift F XR)
        (profilePoint F y eta) := by
  have hX := mul_pos hXR (Real.exp_pos y)
  have hfull : 1 / 2 ≤ Real.log ((XR * Real.exp y) / OutgoingDilation.switchRadius F XR) + 1 / 5 :=
    by
    rw [tailTime_clock F hXR y]
    dsimp only [terminalStart] at hy
    linarith
  rw [HeatedOutgoing.E_full_switch F XR c eta (XR * Real.exp y) hXR hX hfull,
    tailTime_clock F hXR y]
  simp only [TerminalEdgeFactor.profileAngularVelocity, TerminalEdgeFactor.profileCarrier,
    TerminalEdgeFactor.profileZ, profilePoint, profileS_clock F hXR y]
  have hz : 0 ≤ 2 * (1 - eta ^ 2) / (XR * Real.exp y) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (TerminalEdgeFactor.eta_sq_le_one heta)))
      hX.le
  rw [HeatProfileExtension.extension_eq_profile (1 + F.data.h) hz,
    show 3 - edgeDistance F y = y - OutgoingTail.tailStart F.data by
      unfold edgeDistance OutgoingTail.tailEnd
      ring]
  simp only [normalization, TerminalPressure.releasedNormalization,
    OutgoingDilation.carrierAmplitude,
    TerminalPressure.amplitudeExponent, HeatTailEdit.exponent, RadialHeatProfile.spatialProfile,
    ParametricHeatTail.diffusion]
  ring

theorem U_eq_zero (F : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) {y eta : ℝ}
    (hy : terminalStart F.data ≤ y) : HeatedOutgoing.U F XR (XR * Real.exp y, eta) = 0 := by
  apply HeatedOutgoing.U_after_switch F XR eta (XR * Real.exp y) hXR
  apply HeatedOutgoing.full_switch_above_radius (OutgoingDilation.switchRadius_pos F XR hXR)
    (mul_pos hXR (Real.exp_pos y))
  rw [tailTime_clock F hXR y]
  dsimp only [terminalStart] at hy
  linarith

/-- Chosen only after the core schedule and `h`.  This bound contains no
compensation coefficient or data-dependent edge-collar width. -/
noncomputable def radiusThreshold (F : OutgoingProfile.Profile) : ℝ :=
  32 / Real.exp (HeatTailEdit.switchStart F.data)

theorem radiusThreshold_pos (F : OutgoingProfile.Profile) : 0 < radiusThreshold F :=
  div_pos (by norm_num) (Real.exp_pos _)

theorem switchRadius_ge_32 (F : OutgoingProfile.Profile) {XR : ℝ}
    (hXR : radiusThreshold F ≤ XR) : 32 ≤ OutgoingDilation.switchRadius F XR := by
  exact (div_le_iff₀ (Real.exp_pos (HeatTailEdit.switchStart F.data))).mp hXR

theorem full_interval_true_cone (F : OutgoingProfile.Profile) {XR y eta : ℝ}
    (hsmall : SmallTail F.data) (hXR : radiusThreshold F ≤ XR)
    (hy : terminalStart F.data ≤ y) (hy' : y < OutgoingTail.tailEnd F.data)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    2 < TerminalEdgeFactor.profileP (normalization F XR) F.data (shift F XR) (profilePoint F y eta)
      ∧
    TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR) (profilePoint F y eta)
      <
      ConeAlgebra.coneBound
        (TerminalEdgeFactor.profileP (normalization F XR) F.data (shift F XR) (profilePoint F y
          eta))
        (TerminalEdgeFactor.profileJ (normalization F XR) F.data (shift F XR) (profilePoint F y
          eta)) := by
  have hδ := edgeDistance_bounds F hy hy'
  exact profile_full_true_cone F.data hsmall (switchRadius_ge_32 F hXR) hδ.1 hδ.2 heta

theorem full_interval_direction_margin (F : OutgoingProfile.Profile) {XR y eta : ℝ}
    (hsmall : SmallTail F.data) (hXR : radiusThreshold F ≤ XR)
    (hy : terminalStart F.data ≤ y) (hy' : y ≤ OutgoingTail.tailEnd F.data)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    2 + F.data.h < TerminalEdgeFactor.profileSpeed (normalization F XR) F.data
      (shift F XR) (profilePoint F y eta) ∧
    TerminalEdgeFactor.profileSpeed (normalization F XR) F.data
      (shift F XR) (profilePoint F y eta) ≤ 2 + 2 * F.data.h ∧
    3 / 2 ≤ TerminalEdgeFactor.profileConeGap (normalization F XR) F.data
      (shift F XR) (profilePoint F y eta) := by
  have hδ : 0 ≤ edgeDistance F y := sub_nonneg.mpr hy'
  have hδ' : edgeDistance F y ≤ 5 / 2 := by
    dsimp only [terminalStart] at hy
    dsimp only [edgeDistance, OutgoingTail.tailEnd]
    linarith
  exact profile_cone_margin F.data hsmall (switchRadius_ge_32 F hXR) hδ hδ' heta

/-- The actual compensated velocity uses precisely the terminal field whose
true cone was proved above.  The existing witness, its coefficients, and the
base outgoing profile are retained. -/
theorem same_witness_full_cone (F : OutgoingProfile.Profile) {XR C y eta : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C)
    (hsmall : SmallTail F.data) (hXR : radiusThreshold F ≤ XR)
    (hy : terminalStart F.data ≤ y) (hy' : y < OutgoingTail.tailEnd F.data)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    HeatedOutgoing.E F XR w.coefficients (XR * Real.exp y, eta) =
      TerminalEdgeFactor.profileAngularVelocity (normalization F XR) F.data (shift F XR)
        (profilePoint F y eta) ∧
    HeatedOutgoing.U F XR (XR * Real.exp y, eta) = 0 ∧
    2 < TerminalEdgeFactor.profileP (normalization F XR) F.data (shift F XR) (profilePoint F y eta)
      ∧
    TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR) (profilePoint F y eta)
      <
      ConeAlgebra.coneBound
        (TerminalEdgeFactor.profileP (normalization F XR) F.data (shift F XR) (profilePoint F y
          eta))
        (TerminalEdgeFactor.profileJ (normalization F XR) F.data (shift F XR) (profilePoint F y
          eta)) :=
  ⟨E_eq_profileAngularVelocity F w.coefficients w.radius_pos hy heta,
    U_eq_zero F w.radius_pos hy, full_interval_true_cone F hsmall hXR hy hy' heta⟩

end NavierStokes.TerminalCone
