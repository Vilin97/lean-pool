/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ReleaseMoments
public import LeanPool.NavierStokesAndEuler.NavierStokes.CoordinateAlgebra
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectedPressureBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseCone

/-!
# The actual outgoing tail and its cone estimates

The controller below is identified with an actual corrected angular history
by `ReleaseMoments`. Bounds never assume an amplitude small relative to `h`:
the prescribed long release plateau supplies that suppression.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset
open NavierStokes.TailEnergyBounds

namespace NavierStokes.TailCone

theorem initialLag_ge_half_lambda (d : TailData) : d.core.lam / 2 ≤ initialLag d := by
  have hd : 0 < 1 - d.core.lam := by linarith [d.core.lam_lt]
  apply (le_div_iff₀ hd).mpr
  nlinarith [d.h_small, sq_nonneg d.core.lam]

theorem release_rate_integral_bound_all (d : TailData) {t : ℝ}
    (_ht : 0 ≤ t) (ht' : t ≤ d.rampEnd) : primitive (releaseRate d) t ≤ 2 := by
  have hc := (releaseRate_contDiff d).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t d.rampEnd)
  have hn : 0 ≤ ∫ s in t..d.rampEnd, releaseRate d s :=
    intervalIntegral.integral_nonneg ht' (fun s _ => (release_rate_bounds d s).1)
  have hb := release_rate_integral_bound d
  unfold primitive at hb ⊢
  linarith

theorem releaseLag_lower_all (d : TailData) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ d.rampEnd) :
    Real.exp (-2) * (d.core.lam / 2) ≤ releaseLag d t := by
  have hsource : 0 ≤ primitive
      (fun s => Real.exp (primitive (releaseRate d) s) * releaseSource d s) t :=
    intervalIntegral.integral_nonneg ht
      (fun s _ => mul_nonneg (Real.exp_pos _).le (release_source_nonneg d s))
  have he : Real.exp (-2) ≤ Real.exp (-primitive (releaseRate d) t) :=
    Real.exp_le_exp.mpr (by linarith [release_rate_integral_bound_all d ht ht'])
  have hq := initialLag_ge_half_lambda d
  have hq0 : 0 ≤ initialLag d := d.h_pos.le.trans (initialLag_gt_h d).le
  unfold releaseLag linearLag
  have h1 := mul_le_mul_of_nonneg_right he hq0
  have h2 := mul_le_mul_of_nonneg_left hq (Real.exp_pos (-2)).le
  nlinarith [mul_nonneg (Real.exp_pos (-primitive (releaseRate d) t)).le hsource]

theorem tailDebt_ge_coefficient (d : TailData) : tailCoefficient * d.h ≤ tailDebt d := by
  have hd : 0 < 1 - d.rho := by linarith [d.rho_lt_half]
  have h : d.rho ≤ d.rho / (1 - d.rho) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg d.rho]
  exact h.trans (tailDebt_bounds d).1

theorem holdLag_lower (d : TailData) {t : ℝ} (ht : t ≤ decayHold d) :
    tailCoefficient * d.h ≤ holdLag d t := by
  have hq : 0 ≤ releaseLag d d.rampEnd :=
    (tailDebt_pos d).le.trans (releaseLag_gt_tailDebt d).le
  have he : Real.exp (-(1 - d.h) * decayHold d) ≤ Real.exp (-(1 - d.h) * t) :=
    Real.exp_le_exp.mpr (by nlinarith [d.one_sub_h_pos])
  have h := mul_le_mul_of_nonneg_left he hq
  rw [decayHold_hits_target] at h
  exact (tailDebt_ge_coefficient d).trans h

theorem tailLag_first_half (d : TailData) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    tailLag d t = tailDebt d * Real.exp (-(1 - d.h) * t) := by
  have hi : primitive (weightedTailDerivative d) t = 0 := by
    unfold primitive
    calc
      _ = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' := uIcc_of_le ht ▸ hs
        have harg : (s - 1) / 2 < 0 := by linarith [hs'.2]
        simp [weightedTailDerivative, tailShapeDeriv, sigma_derivative_zero_left harg]
      _ = 0 := by simp
  unfold tailLag tailNumerator
  rw [hi, sub_zero, tailShape_early d (show t ≤ 1 by linarith)]
  unfold tailDebt primitive weightedTailDerivative
  ring

theorem tailLag_first_half_lower (d : TailData) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    Real.exp (-1) * tailCoefficient * d.h ≤ tailLag d t := by
  rw [tailLag_first_half d ht ht']
  have he : Real.exp (-1) ≤ Real.exp (-(1 - d.h) * t) :=
    Real.exp_le_exp.mpr (by nlinarith [d.h_pos])
  have h := mul_le_mul (tailDebt_ge_coefficient d) he (Real.exp_pos (-1)).le (tailDebt_pos d).le
  nlinarith

/-- Release lower constant, given by `min (Real.exp (-2)) (Real.exp (-1) * tailCoefficient)`. -/
noncomputable def releaseLowerConstant : ℝ := min (Real.exp (-2)) (Real.exp (-1) * tailCoefficient)

theorem releaseLowerConstant_pos : 0 < releaseLowerConstant :=
  lt_min (Real.exp_pos _) (mul_pos (Real.exp_pos _) tailCoefficient_pos)

theorem normalizedLag_release_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) (hy' : y ≤ d.releaseStart + d.rampEnd) :
    Real.exp (-2) * (d.core.lam / 2) ≤ ReleaseMoments.normalizedLag d w.coefficients eta y := by
  rw [ReleaseMoments.ResetWitness.normalizedLag_release w eta hy hy']
  exact releaseLag_lower_all d (by linarith) (by linarith)

/-- Positivity of the actual angular-history lag through the first half tail unit. -/
theorem normalizedLag_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    releaseLowerConstant * d.h ≤ ReleaseMoments.normalizedLag d w.coefficients eta y := by
  by_cases h1 : y ≤ d.releaseStart + d.rampEnd
  · have h := normalizedLag_release_lower w eta hy h1
    have hc : releaseLowerConstant ≤ Real.exp (-2) := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_right hc d.h_pos.le
    nlinarith [mul_le_mul_of_nonneg_left d.h_small.le (Real.exp_pos (-2)).le]
  · by_cases h2 : y ≤ tailStart d
    · rw [ReleaseMoments.ResetWitness.normalizedLag_hold w eta (le_of_not_ge h1) h2]
      have ht : y - (d.releaseStart + d.rampEnd) ≤ decayHold d := by
        dsimp [tailStart] at h2
        linarith
      have h := holdLag_lower d ht
      have he : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      have hc : releaseLowerConstant ≤ tailCoefficient :=
        (min_le_right _ _).trans (by nlinarith [tailCoefficient_pos])
      exact (mul_le_mul_of_nonneg_right hc d.h_pos.le).trans h
    · rw [ReleaseMoments.ResetWitness.normalizedLag_tail w eta (le_of_not_ge h2)]
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) d.h_pos.le).trans
        (tailLag_first_half_lower d (by linarith) (by linarith))

theorem normalizedLag_pos {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    0 < ReleaseMoments.normalizedLag d w.coefficients eta y :=
  (mul_pos releaseLowerConstant_pos d.h_pos).trans_le (normalizedLag_lower w eta hy hy')

/-! ## The designed suppression of the actual field -/

theorem finalAngular_release_formula (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    finalAngular d (y, eta) = finalAngular d (d.releaseStart, eta) *
      Real.exp (releasePrimitive d (y - d.releaseStart) - (y - d.releaseStart) / 2) *
      (tailShape d (y - tailStart d) / (1 - d.rho)) := by
  have hR : d.core.holdStart ≤ d.releaseStart := by
    linarith [coreEndpoint_ge_hold d, flattenEnd_gt_core d, releaseStart_gt_flattenEnd d]
  have hrad := radialAmplitude_hold d.core.dropLength_pos.le hR hy
    (P := d.core.P) (lam := d.core.lam)
  rw [finalAngular_uniform d eta ((releaseStart_gt_flattenEnd d).le.trans hy),
    finalAngular_uniform_wait d eta (releaseStart_gt_flattenEnd d).le le_rfl,
    carrier, hrad, releaseAdjustment_eq]
  have hex : Real.exp (-(1 / 2 + d.core.lam) * (y - d.releaseStart)) *
      Real.exp (releasePrimitive d (y - d.releaseStart) + d.core.lam * (y - d.releaseStart)) =
      Real.exp (releasePrimitive d (y - d.releaseStart) - (y - d.releaseStart) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (radialAmplitude d.core.P d.core.dropLength d.core.lam d.releaseStart / 2) *
      (Real.exp (-(1 / 2 + d.core.lam) * (y - d.releaseStart)) *
        Real.exp (releasePrimitive d (y - d.releaseStart) + d.core.lam * (y - d.releaseStart))) *
      (tailShape d (y - tailStart d) / (1 - d.rho)) := by ring
    _ = _ := by rw [hex]

theorem tailShape_ratio_le_two (d : TailData) (t : ℝ) : tailShape d t / (1 - d.rho) ≤ 2 := by
  apply (div_le_iff₀ (show 0 < 1 - d.rho by linarith [d.rho_lt_half])).mpr
  linarith [(tailShape_bounds d t).2, d.rho_lt_half]

theorem plateau_amplitude_suppression (d : TailData) : Real.exp (-d.longHold) = d.h ^ 4 := by
  have he := OutgoingPulseBounds.exp_log_inverse_nat d.h_pos 4
  simpa [TailData.longHold] using he

theorem finalAngular_suppressed (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart + d.secondRampStart ≤ y) :
    finalAngular d (y, eta) ≤ 2 * finalAngular d (d.releaseStart, eta) * d.h ^ 4 := by
  have ht : d.secondRampStart ≤ y - d.releaseStart := by linarith
  have h0 : 0 ≤ y - d.releaseStart := by
    dsimp [TailData.secondRampStart] at ht
    linarith [d.longHold_pos]
  have hp := releasePrimitive_late_le d ht
  have hex : Real.exp (releasePrimitive d (y - d.releaseStart) - (y - d.releaseStart) / 2) ≤
      d.h ^ 4 := by
    rw [← plateau_amplitude_suppression]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg d.h_pos.le (sub_nonneg.mpr ht)]
  have hratio0 : 0 ≤ tailShape d (y - tailStart d) / (1 - d.rho) :=
    div_nonneg (tailShape_pos d _).le (by linarith [d.rho_lt_half])
  rw [finalAngular_release_formula d eta (by linarith)]
  have h := mul_le_mul hex (tailShape_ratio_le_two d (y - tailStart d)) hratio0
    (pow_nonneg d.h_pos.le 4)
  have h' := mul_le_mul_of_nonneg_left h (finalAngular_pos d (d.releaseStart, eta)).le
  nlinarith

theorem finalAngular_div_h_suppressed (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart + d.secondRampStart ≤ y) :
    finalAngular d (y, eta) / d.h ≤ 2 * finalAngular d (d.releaseStart, eta) * d.h ^ 3 := by
  apply (div_le_iff₀ d.h_pos).mpr
  convert! finalAngular_suppressed d eta hy using 1
  ring

theorem profileSlope_bounds (d : TailData) (y : ℝ) :
    -1 ≤ profileSlope d y ∧ profileSlope d y ≤ -(3 * d.h / 4) := by
  have hs := releaseSlope_bounds d (y - d.releaseStart)
  have ht := tail_taper_log_derivative d (y - tailStart d)
  dsimp [profileSlope]
  constructor <;> linarith

/-- Release A, given by `2 - 2 * profileSlope d y`. -/
noncomputable def releaseA (d : TailData) (y : ℝ) : ℝ := 2 - 2 * profileSlope d y

theorem releaseA_bounds (d : TailData) (y : ℝ) : 2 < releaseA d y ∧ releaseA d y ≤ 4 := by
  have h := profileSlope_bounds d y
  dsimp [releaseA]
  constructor <;> linarith [d.h_pos]

theorem releaseA_eq_derivative (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    releaseA d y = 1 - 2 * deriv (fun t => Real.log (finalAngular d (t, eta))) y := by
  rw [(finalAngular_log_hasDerivAt_on_release d eta hy).deriv]
  dsimp [releaseA]
  ring

/-! ## Future integrals on the uniform release -/

theorem finalAngular_release_decay (d : TailData) (eta : ℝ) {y t : ℝ}
    (hy : d.releaseStart ≤ y) (hyt : y ≤ t) :
    finalAngular d (t, eta) ≤ finalAngular d (y, eta) *
      Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y)) := by
  have hf : ContDiff ℝ ∞ (fun s => Real.log (finalAngular d (s, eta))) :=
    ((finalAngular_contDiff d).comp (contDiff_id.prodMk contDiff_const)).log
      (fun s => (finalAngular_pos d (s, eta)).ne')
  have hi := (convex_Ici d.releaseStart).image_sub_le_mul_sub_of_deriv_le
    hf.continuous.continuousOn (hf.differentiable (by simp)).differentiableOn
    (fun z hz => show deriv (fun s => Real.log (finalAngular d (s, eta))) z ≤
        -(1 / 2 + 3 * d.h / 4) by
      rw [(finalAngular_log_hasDerivAt_on_release d eta (interior_subset hz)).deriv]
      linarith [(profileSlope_bounds d z).2]) y hy t (hy.trans hyt) hyt
  have he := Real.exp_le_exp.mpr hi
  rw [Real.exp_sub, Real.exp_log (finalAngular_pos d _), Real.exp_log (finalAngular_pos d _)] at he
  have he' := (div_le_iff₀ (finalAngular_pos d (y, eta))).mp he
  simpa only [mul_comm] using he'

theorem weighted_square_release_decay (d : TailData) (eta : ℝ) {y t : ℝ}
    (hy : d.releaseStart ≤ y) (hyt : y ≤ t) :
    Real.exp (t - y) * finalAngular d (t, eta) ^ 2 ≤
      finalAngular d (y, eta) ^ 2 * Real.exp (-(3 * d.h / 2) * (t - y)) := by
  have he := finalAngular_release_decay d eta hy hyt
  have hs := pow_le_pow_left₀ (finalAngular_pos d (t, eta)).le he 2
  have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos (t - y)).le
  have hex : Real.exp (t - y) * Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y)) ^ 2 =
      Real.exp (-(3 * d.h / 2) * (t - y)) := by
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (t - y) *
        (finalAngular d (y, eta) * Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y))) ^ 2 := hm
    _ = finalAngular d (y, eta) ^ 2 *
        (Real.exp (t - y) * Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y)) ^ 2) := by ring
    _ = _ := by rw [hex]

theorem weighted_square_release_integrable (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    IntegrableOn (fun t => Real.exp (t - y) * finalAngular d (t, eta) ^ 2) (Ioi y) := by
  have ha : 0 < 3 * d.h / 2 := div_pos (mul_pos (by norm_num) d.h_pos) (by norm_num)
  have hm := (integrableOn_shift_exp ha y).const_mul (finalAngular d (y, eta) ^ 2)
  have hc : Continuous (fun t => Real.exp (t - y) * finalAngular d (t, eta) ^ 2) :=
    (Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul
      (((finalAngular_contDiff d).continuous.comp (continuous_id.prodMk continuous_const)).pow 2)
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact weighted_square_release_decay d eta hy ht.le

theorem weighted_square_release_integral_le (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    d.h * (∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, eta) ^ 2) ≤
      finalAngular d (y, eta) ^ 2 := by
  have ha : 0 < 3 * d.h / 2 := div_pos (mul_pos (by norm_num) d.h_pos) (by norm_num)
  have hm := (integrableOn_shift_exp ha y).const_mul (finalAngular d (y, eta) ^ 2)
  have hi := setIntegral_mono_on (weighted_square_release_integrable d eta hy) hm
    measurableSet_Ioi (fun t ht => weighted_square_release_decay d eta hy ht.le)
  rw [integral_const_mul, integral_shift_exp ha] at hi
  have h := mul_le_mul_of_nonneg_left hi d.h_pos.le
  have heq : d.h * (finalAngular d (y, eta) ^ 2 * (1 / (3 * d.h / 2))) =
      (2 / 3) * finalAngular d (y, eta) ^ 2 := by field_simp [d.h_pos.ne']
  rw [heq] at h
  nlinarith [sq_nonneg (finalAngular d (y, eta))]

/-- Release future energy, given by `∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, 0) ^
2`. -/
noncomputable def releaseFutureEnergy (d : TailData) (y : ℝ) : ℝ :=
  ∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, 0) ^ 2

/-- Release future mass, given by `∫ t in Ioi y, finalAngular d (t, 0) ^ 2`. -/
noncomputable def releaseFutureMass (d : TailData) (y : ℝ) : ℝ :=
  ∫ t in Ioi y, finalAngular d (t, 0) ^ 2

/-- The backward-energy numerator in the uniform region. Its identification
with the source primitive uses the actual zero total energy. -/
noncomputable def releaseNumerator (d : TailData) (eta y : ℝ) : ℝ :=
  2 * eta * (d.h * releaseFutureEnergy d y - (1 / 2 + d.h) * releaseFutureMass d y)

/-- Numerator constant, given by `2 * (1 + FuturePressureBounds.envelopeConstant)`. -/
noncomputable def numeratorConstant : ℝ := 2 * (1 + FuturePressureBounds.envelopeConstant)

theorem numeratorConstant_pos : 0 < numeratorConstant := by
  dsimp [numeratorConstant]
  linarith [FuturePressureBounds.envelopeConstant_pos]

theorem releaseNumerator_abs_le (d : TailData) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y) :
    |releaseNumerator d eta y| ≤ numeratorConstant * finalAngular d (y, 0) ^ 2 := by
  have he0 : 0 ≤ releaseFutureEnergy d y := integral_nonneg (fun t => by positivity)
  have hm0 : 0 ≤ releaseFutureMass d y := integral_nonneg (fun t => sq_nonneg _)
  have he : d.h * releaseFutureEnergy d y ≤ finalAngular d (y, 0) ^ 2 :=
    weighted_square_release_integral_le d 0 hy
  have hy0 : 0 ≤ y := (UniformAngularReset.flattenEnd_pos d).le.trans
    ((releaseStart_gt_flattenEnd d).le.trans hy)
  have hm : releaseFutureMass d y ≤
      FuturePressureBounds.envelopeConstant * finalAngular d (y, 0) ^ 2 :=
    FuturePressureBounds.future_square_integral_le d hy0 (by norm_num)
  have hA : 0 ≤ 1 / 2 + d.h := by linarith [d.h_pos]
  have hA' : 1 / 2 + d.h ≤ 1 := by linarith [d.h_lt_half]
  have hmass := mul_le_mul_of_nonneg_right hA' hm0
  have hs : |d.h * releaseFutureEnergy d y - (1 / 2 + d.h) * releaseFutureMass d y| ≤
      (1 + FuturePressureBounds.envelopeConstant) * finalAngular d (y, 0) ^ 2 := by
    have h := abs_sub_le (d.h * releaseFutureEnergy d y) 0 ((1 / 2 + d.h) * releaseFutureMass d y)
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg d.h_pos.le he0),
      abs_of_nonneg (mul_nonneg hA hm0)] at h
    nlinarith
  dsimp [releaseNumerator, numeratorConstant]
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul (mul_le_mul_of_nonneg_left heta (by norm_num : (0 : ℝ) ≤ 2)) hs
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
  nlinarith

/-! ## Uniform smallness after dividing by the actual controller -/

theorem releaseAmplitude_le_pulse (d : TailData) (eta : ℝ) :
    finalAngular d (d.releaseStart, eta) ≤ pulseAmplitude d.core := by
  have hy : d.core.pulseStart ≤ d.releaseStart := by
    have hs := endpoint_le_releaseStart d
    dsimp [OutgoingSchedule.Parameters.endpoint] at hs
    linarith [d.core.pulseLength_pos]
  have hr := radialAmplitude_hold d.core.dropLength_pos.le d.core.pulseStart_ge_hold hy
    (P := d.core.P) (lam := d.core.lam)
  rw [finalAngular_uniform_wait d eta (releaseStart_gt_flattenEnd d).le le_rfl, hr]
  change pulseAmplitude d.core * Real.exp (-(1 / 2 + d.core.lam) *
    (d.releaseStart - d.core.pulseStart)) / 2 ≤ pulseAmplitude d.core
  have he : Real.exp (-(1 / 2 + d.core.lam) * (d.releaseStart - d.core.pulseStart)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [d.core.lam_pos])
  nlinarith [pulseAmplitude_pos d.core]

theorem releaseAmplitude_small (d : TailData)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (eta : ℝ) :
    finalAngular d (d.releaseStart, eta) ≤
      (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ) :=
  (releaseAmplitude_le_pulse d eta).trans (OutgoingPulseBounds.pulseAmplitude_small d.core hwait)

theorem finalAngular_le_releaseAmplitude (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) : finalAngular d (y, eta) ≤ finalAngular d (d.releaseStart, eta) := by
  have he := finalAngular_release_decay d eta le_rfl hy
  have hex : Real.exp (-(1 / 2 + 3 * d.h / 4) * (y - d.releaseStart)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [d.h_pos])
  nlinarith [finalAngular_pos d (d.releaseStart, eta)]

/-- Release velocity ratio, given by `releaseNumerator d eta y / (finalAngular d (y, 0) *
ReleaseMoments.normalizedLag d c eta y)`. -/
noncomputable def releaseVelocityRatio (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) : ℝ :=
  releaseNumerator d eta y / (finalAngular d (y, 0) * ReleaseMoments.normalizedLag d c eta y)

theorem releaseVelocityRatio_abs_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      numeratorConstant * finalAngular d (y, 0) / ReleaseMoments.normalizedLag d w.coefficients eta
          y := by
  have hQ := normalizedLag_pos w eta hy hy'
  have hden := mul_pos (finalAngular_pos d (y, 0)) hQ
  rw [releaseVelocityRatio, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ numeratorConstant * finalAngular d (y, 0) ^ 2 := releaseNumerator_abs_le d heta hy
    _ = _ := by field_simp [hQ.ne']

/-- Early ratio constant, given by `2 * numeratorConstant / Real.exp (-2)`. -/
noncomputable def earlyRatioConstant : ℝ := 2 * numeratorConstant / Real.exp (-2)
/-- Late ratio constant, given by `2 * numeratorConstant / releaseLowerConstant`. -/
noncomputable def lateRatioConstant : ℝ := 2 * numeratorConstant / releaseLowerConstant

theorem earlyRatioConstant_pos : 0 < earlyRatioConstant :=
  div_pos (mul_pos (by norm_num) numeratorConstant_pos) (Real.exp_pos _)

theorem lateRatioConstant_pos : 0 < lateRatioConstant :=
  div_pos (mul_pos (by norm_num) numeratorConstant_pos) releaseLowerConstant_pos

theorem releaseVelocityRatio_early {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y)
    (hy' : y ≤ d.releaseStart + d.rampEnd) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      earlyRatioConstant * (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (29 : ℕ)
          := by
  have hyend : y ≤ tailStart d + 1 / 2 := by
    dsimp [tailStart]
    linarith [decayHold_pos d]
  have hQ := normalizedLag_pos w eta hy hyend
  have hQl := normalizedLag_release_lower w eta hy hy'
  have hcl : 0 < Real.exp (-2) * (d.core.lam / 2) := by
    exact mul_pos (Real.exp_pos _) (div_pos d.core.lam_pos (by norm_num))
  calc
    _ ≤ numeratorConstant * finalAngular d (y, 0) / ReleaseMoments.normalizedLag d w.coefficients
        eta y :=
      releaseVelocityRatio_abs_le w heta hy hyend
    _ ≤ numeratorConstant * finalAngular d (d.releaseStart, 0) /
        ReleaseMoments.normalizedLag d w.coefficients eta y :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (finalAngular_le_releaseAmplitude d 0 hy)
            numeratorConstant_pos.le) hQ.le
    _ ≤ numeratorConstant * finalAngular d (d.releaseStart, 0) / (Real.exp (-2) * (d.core.lam / 2))
        :=
      div_le_div_of_nonneg_left (mul_nonneg numeratorConstant_pos.le (finalAngular_pos d _).le) hcl
          hQl
    _ ≤ numeratorConstant * ((d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 :
        ℕ)) /
        (Real.exp (-2) * (d.core.lam / 2)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (releaseAmplitude_small d hwait 0) numeratorConstant_pos.le)
            hcl.le
    _ = _ := by
      dsimp [earlyRatioConstant]
      field_simp [d.core.lam_pos.ne']

theorem releaseVelocityRatio_late {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart + d.secondRampStart ≤ y)
    (hy' : y ≤ tailStart d + 1 / 2) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      lateRatioConstant * (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (29 : ℕ) :=
          by
  have hyR : d.releaseStart ≤ y := by
    dsimp [TailData.secondRampStart] at hy
    linarith [d.longHold_pos]
  have hQ := normalizedLag_pos w eta hyR hy'
  have hQl := normalizedLag_lower w eta hyR hy'
  have hcl := mul_pos releaseLowerConstant_pos d.h_pos
  have hh : d.h ^ (3 : ℕ) ≤ 1 := pow_le_one₀ d.h_pos.le (by linarith [d.h_lt_half])
  have hlam : d.core.lam ^ (30 : ℕ) ≤ d.core.lam ^ (29 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left (show d.core.lam ≤ 1 by linarith [d.core.lam_lt])
      (pow_nonneg d.core.lam_pos.le 29)
    simpa only [← pow_succ, mul_one] using h
  calc
    _ ≤ numeratorConstant * finalAngular d (y, 0) / ReleaseMoments.normalizedLag d w.coefficients
        eta y :=
      releaseVelocityRatio_abs_le w heta hyR hy'
    _ ≤ numeratorConstant * (2 * finalAngular d (d.releaseStart, 0) * d.h ^ 4) /
        ReleaseMoments.normalizedLag d w.coefficients eta y :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (finalAngular_suppressed d 0 hy) numeratorConstant_pos.le) hQ.le
    _ ≤ numeratorConstant * (2 * finalAngular d (d.releaseStart, 0) * d.h ^ 4) /
        (releaseLowerConstant * d.h) :=
      div_le_div_of_nonneg_left (mul_nonneg numeratorConstant_pos.le
        (mul_nonneg (mul_nonneg (by
            norm_num) (finalAngular_pos d _).le) (pow_nonneg d.h_pos.le 4))) hcl hQl
    _ = lateRatioConstant * finalAngular d (d.releaseStart, 0) * d.h ^ 3 := by
      dsimp [lateRatioConstant]
      field_simp [d.h_pos.ne', releaseLowerConstant_pos.ne']
    _ ≤ lateRatioConstant * finalAngular d (d.releaseStart, 0) := by
      exact mul_le_of_le_one_right (mul_nonneg lateRatioConstant_pos.le (finalAngular_pos d _).le)
          hh
    _ ≤ lateRatioConstant *
        ((d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ)) :=
      mul_le_mul_of_nonneg_left (releaseAmplitude_small d hwait 0) lateRatioConstant_pos.le
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hlam
        (mul_nonneg lateRatioConstant_pos.le
          (mul_nonneg d.core.P_pos.le (Real.exp_pos (Real.exp d.core.m + 12)).le))
      simpa only [mul_assoc] using h

/-- Release cone constant, given by `(earlyRatioConstant + lateRatioConstant) * (P * Real.exp
(Real.exp m + 12))`. -/
noncomputable def releaseConeConstant (P m : ℝ) : ℝ :=
  (earlyRatioConstant + lateRatioConstant) * (P * Real.exp (Real.exp m + 12))

theorem releaseConeConstant_pos {P m : ℝ} (hP : 0 < P) : 0 < releaseConeConstant P m :=
  mul_pos (add_pos earlyRatioConstant_pos lateRatioConstant_pos) (mul_pos hP (Real.exp_pos _))

theorem releaseVelocityRatio_uniform {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) := by
  have hP : 0 ≤ (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (29 : ℕ) := by
    exact mul_nonneg (mul_nonneg d.core.P_pos.le (Real.exp_pos _).le) (pow_nonneg d.core.lam_pos.le
        _)
  dsimp [releaseConeConstant]
  by_cases h1 : y ≤ d.releaseStart + d.rampEnd
  · have h := releaseVelocityRatio_early w hwait heta hy h1
    nlinarith [mul_nonneg lateRatioConstant_pos.le hP]
  · have hb : d.releaseStart + d.secondRampStart ≤ y := by
      dsimp [TailData.rampEnd] at h1
      linarith
    have h := releaseVelocityRatio_late w hwait heta hb hy'
    nlinarith [mul_nonneg earlyRatioConstant_pos.le hP]

/-! ## Actual slopes and the finite stress cone -/

theorem corrected_release_eventuallyEq (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    (fun t => correctedAngular d c (t, eta)) =ᶠ[𝓝 y] (fun t => finalAngular d (t, eta)) := by
  have hcut : correctionCenter d + 43 / 20 < y := by
    dsimp [correctionCenter]
    linarith
  filter_upwards [lt_mem_nhds hcut] with t ht
  have hr : relative (c eta) (t - correctionCenter d) = 0 := by
    by_contra hn
    have h := relative_support (c eta) hn
    linarith [h.2]
  simp [correctedAngular, hr]

theorem corrected_releaseA (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    1 - 2 * deriv (fun t => Real.log (correctedAngular d c (t, eta))) y = releaseA d y := by
  have he := (corrected_release_eventuallyEq d c eta hy).fun_comp Real.log
  dsimp only [Function.comp_def] at he
  rw [he.deriv_eq]
  exact (releaseA_eq_derivative d eta hy).symm

theorem corrected_bs_zero (d : TailData) (c : ℝ → Coeff) (Amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint < y) :
    2 * deriv (fun t => axial d.core Amp (t, eta)) y / correctedAngular d c (y, eta) = 0 := by
  have he : (fun t => axial d.core Amp (t, eta)) =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
    filter_upwards [lt_mem_nhds hy] with t ht
    exact axial_after_pulse d.core Amp eta ht.le
  rw [he.deriv_eq]
  simp

theorem cone_of_zero_bs {a r p : ℝ} (ha : 2 < a) (ha' : a ≤ 4)
    (hr : |r| ≤ 1 / 2) (hp : 16 < p) :
    2 < p ∧ 2 < a ∧ a < ConeAlgebra.coneBound p (p * r) := by
  have hr2 : r ^ 2 ≤ 1 / 4 := by
    have h := abs_le.mp hr
    nlinarith
  have hmargin : 3 / 2 ≤ 2 - (a - 2) * r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sq_nonneg r)]
  refine ⟨by linarith, ha, ?_⟩
  have h := ConeAlgebra.finite_amplitude_cone (c := 1) (j := r) (v := a) (p := p)
    (by linarith) (by nlinarith) (by nlinarith) ?_
  · simpa using h
  · have hmul := mul_le_mul_of_nonneg_left hmargin (show 0 ≤ p by linarith)
    nlinarith

/-- Release P1, given by `XR * Real.exp y * ReleaseMoments.normalizedLag d c eta y /
CoordinateAlgebra.L d.h eta`. -/
noncomputable def releaseP1 (d : TailData) (c : ℝ → Coeff) (XR eta y : ℝ) : ℝ :=
  XR * Real.exp y * ReleaseMoments.normalizedLag d c eta y / CoordinateAlgebra.L d.h eta

/-- Release radius threshold, given by `16 / (Real.exp d.releaseStart * (releaseLowerConstant *
d.h))`. -/
noncomputable def releaseRadiusThreshold (d : TailData) : ℝ :=
  16 / (Real.exp d.releaseStart * (releaseLowerConstant * d.h))

theorem releaseRadiusThreshold_pos (d : TailData) : 0 < releaseRadiusThreshold d :=
  div_pos (by norm_num) (mul_pos (Real.exp_pos _) (mul_pos releaseLowerConstant_pos d.h_pos))

theorem releaseP1_large {d : TailData} {K : ℝ} (w : ResetWitness d K) {XR eta y : ℝ}
    (hXR : releaseRadiusThreshold d < XR) (heta : eta ^ 2 ≤ 1)
    (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    16 < releaseP1 d w.coefficients XR eta y := by
  have hL := CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half heta
  have hL1 : CoordinateAlgebra.L d.h eta ≤ 1 := by
    dsimp [CoordinateAlgebra.L]
    nlinarith [mul_nonneg d.h_pos.le (sq_nonneg eta)]
  have hXR0 := (releaseRadiusThreshold_pos d).trans hXR
  have hscale : 16 < XR * (Real.exp d.releaseStart * (releaseLowerConstant * d.h)) := by
    exact (div_lt_iff₀ (mul_pos (Real.exp_pos _) (mul_pos releaseLowerConstant_pos d.h_pos))).mp hXR
  have he := Real.exp_le_exp.mpr hy
  have hq := normalizedLag_lower w eta hy hy'
  have hprod := mul_le_mul he hq (mul_pos releaseLowerConstant_pos d.h_pos).le (Real.exp_pos y).le
  have hprod' := mul_le_mul_of_nonneg_left hprod hXR0.le
  unfold releaseP1
  apply (lt_div_iff₀ hL).mpr
  nlinarith

theorem release_true_cone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2)
    {XR eta y : ℝ} (hXR : releaseRadiusThreshold d < XR) (heta : |eta| ≤ 1)
    (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    2 < releaseP1 d w.coefficients XR eta y ∧ 2 < releaseA d y ∧
      releaseA d y < ConeAlgebra.coneBound (releaseP1 d w.coefficients XR eta y)
        (releaseP1 d w.coefficients XR eta y * releaseVelocityRatio d w.coefficients eta y) := by
  have heta2 : eta ^ 2 ≤ 1 := by have h := abs_le.mp heta; nlinarith
  exact cone_of_zero_bs (releaseA_bounds d y).1 (releaseA_bounds d y).2
    ((releaseVelocityRatio_uniform w hwait heta hy hy').trans hsmall)
    (releaseP1_large w hXR heta2 hy hy')

theorem exists_release_cone_threshold (P m : ℝ) (hP : 0 < P) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.P = P → d.core.m = m →
      d.core.lam < lam0 → releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) < 1 / 2 :=
          by
  have hC := releaseConeConstant_pos (m := m) hP
  refine ⟨(1 / 2) / releaseConeConstant P m, div_pos (by norm_num) hC, ?_⟩
  intro d hdP hdm hd
  rw [hdP, hdm]
  have hp : d.core.lam ^ (29 : ℕ) ≤ d.core.lam := by
    have h := pow_le_one₀ d.core.lam_pos.le (show d.core.lam ≤ 1 by linarith [d.core.lam_lt])
      (n := 28)
    calc
      _ = d.core.lam * d.core.lam ^ (28 : ℕ) := by ring
      _ ≤ d.core.lam * 1 := mul_le_mul_of_nonneg_left h d.core.lam_pos.le
      _ = _ := mul_one _
  have hsmall := (lt_div_iff₀ hC).mp hd
  have h := mul_le_mul_of_nonneg_left hp hC.le
  nlinarith

/-! ## Identification with the actual global histories -/

theorem actualI_eq_releaseHistory {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    OutgoingHistories.I w (y, eta) = ReleaseMoments.history d w.coefficients eta y := by
  rw [OutgoingHistories.I_eq_integral, ReleaseMoments.ResetWitness.history_eq_integral w eta hy]
  rfl

theorem actualI_eta_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.dEta (OutgoingHistories.I w) (y, eta) = 0 := by
  have hy0 : 0 ≤ y := (UniformAngularReset.flattenEnd_pos d).le.trans
    ((releaseStart_gt_flattenEnd d).le.trans hy)
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.I_smooth w)]
  have he : (fun q => OutgoingHistories.I w (y, q)) =
      (fun q => ReleaseMoments.history d w.coefficients q y) :=
    funext (fun q => actualI_eq_releaseHistory w q hy0)
  rw [he]
  exact ReleaseMoments.ResetWitness.history_deriv_eta_zero w hy eta

theorem actualQs_eq_normalizedLag {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.Qs w Amp (y, eta) = ReleaseMoments.normalizedLag d w.coefficients eta y := by
  have hyS := (endpoint_le_releaseStart d).trans hy
  have hy0 : 0 ≤ y := (UniformAngularReset.flattenEnd_pos d).le.trans
    ((releaseStart_gt_flattenEnd d).le.trans hy)
  rw [OutgoingHistories.Qs_after_endpoint w ha eta hyS, actualI_eta_zero w eta hy,
    mul_zero, sub_zero, actualI_eq_releaseHistory w eta hy0]
  change -1 + (1 - d.h) * ReleaseMoments.history d w.coefficients eta y /
    (Real.exp (3 * y / 2) * correctedAngular d w.coefficients (y, eta)) = _
  rw [ReleaseMoments.corrected_eq_release d w.coefficients eta hy]
  unfold ReleaseMoments.normalizedLag ReleaseMoments.releaseWeight
  ring

theorem actual_energyWeight_eq {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (eta t : ℝ) :
    Real.exp t * (OutgoingHistories.U d Amp (t, eta) ^ 2 - OutgoingHistories.E w (t, eta) ^ 2 / 2) =
      CorrectedPulseAmplitude.energyIntegrand d w.coefficients (Amp eta) eta t := by
  dsimp [OutgoingHistories.U, OutgoingHistories.E, CorrectedPulseAmplitude.energyIntegrand]
  rw [PulseAmplitude.axial_eq_of_amplitude_eq d.core Amp (fun _ => Amp eta) eta t rfl]

/-- Zero actual total energy fixes the future energy term, including the reset. -/
theorem actualS_backward {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y)
    (hz : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0) :
    OutgoingHistories.S w Amp (y, eta) =
      (1 / 2 : ℝ) * ∫ t in Ioi y, Real.exp t * correctedAngular d w.coefficients (t, eta) ^ 2 := by
  have hS : OutgoingHistories.S w Amp (y, eta) =
      ∫ t in Iic y, CorrectedPulseAmplitude.energyIntegrand d w.coefficients (Amp eta) eta t := by
    rw [OutgoingHistories.S_eq_integral w ha]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t _
    exact actual_energyWeight_eq w Amp eta t
  have hf : (∫ t in Ioi y, CorrectedPulseAmplitude.energyIntegrand d w.coefficients (Amp eta) eta
      t) =
      -(1 / 2 : ℝ) * ∫ t in Ioi y, Real.exp t * correctedAngular d w.coefficients (t, eta) ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    unfold CorrectedPulseAmplitude.energyIntegrand
    rw [axial_after_pulse d.core (fun _ => Amp eta) eta (hy.trans ht.le)]
    ring
  have hsplit := integral_add_compl measurableSet_Iic
    (CorrectedPulseAmplitude.energyIntegrand_integrable d w.coefficients (Amp eta) eta)
    (s := Iic y)
  rw [compl_Iic, ← hS, hf] at hsplit
  change _ = CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta at hsplit
  rw [hz] at hsplit
  linarith

theorem actualS_uniform {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0) :
    OutgoingHistories.S w Amp (y, eta) =
      (Real.exp y / 2) * releaseFutureEnergy d y := by
  rw [actualS_backward w ha eta ((endpoint_le_releaseStart d).trans hy) hz]
  unfold releaseFutureEnergy
  have he : (∫ t in Ioi y, Real.exp t * correctedAngular d w.coefficients (t, eta) ^ 2) =
      Real.exp y * ∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, 0) ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [ReleaseMoments.corrected_eq_release d w.coefficients eta (hy.trans ht.le)]
    have hex : Real.exp y * Real.exp (t - y) = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, hex]
  rw [he]
  ring

theorem actualS_eta_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y, eta) = 0 := by
  have he : (fun q => OutgoingHistories.S w Amp (y, q)) =ᶠ[𝓝 eta]
      (fun _ => (Real.exp y / 2) * releaseFutureEnergy d y) := by
    filter_upwards [hz] with q hq
    exact actualS_uniform w ha q hy hq
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.S_smooth w ha), he.deriv_eq]
  simp

theorem actualPi_eq_correctedPi {d : TailData} {K : ℝ} (w : ResetWitness d K) (y eta : ℝ) :
    OutgoingHistories.Pi w (y, eta) = CorrectedPressureBounds.correctedPi w y eta := by
  rw [OutgoingHistories.Pi_eq_past_integral,
      CorrectedPressureBounds.correctedPi_eq_axisPressure_add]
  rw [integral_div]
  dsimp [OutgoingHistories.E]
  ring

theorem actualPi_uniform {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.Pi w (y, eta) = -(1 / 2 : ℝ) * releaseFutureMass d y := by
  rw [actualPi_eq_correctedPi, CorrectedPressureBounds.correctedPi_eta_independent_after w hy eta 0,
    CorrectedPressureBounds.correctedPi_eq_after w hy]
  rfl

theorem actualPi_eta_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.dEta (OutgoingHistories.Pi w) (y, eta) = 0 := by
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.Pi_smooth w)]
  have he : (fun q => OutgoingHistories.Pi w (y, q)) = CorrectedPressureBounds.correctedPi w y :=
    funext (fun q => actualPi_eq_correctedPi w y q)
  rw [he]
  exact CorrectedPressureBounds.correctedPi_deriv_eta_zero_after w hy eta

theorem actualNs_eq_releaseNumerator {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.Ns w Amp (y, eta) = releaseNumerator d eta y := by
  have hz0 : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0 :=
    Filter.Eventually.self_of_nhds (x := eta)
      (p := fun q => CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) hz
  rw [OutgoingHistories.Ns_after_endpoint w ha eta ((endpoint_le_releaseStart d).trans hy),
    actualS_uniform w ha eta hy hz0, actualS_eta_zero w ha eta hy hz,
    actualPi_uniform w eta hy, actualPi_eta_zero w eta hy]
  dsimp [releaseNumerator, StressAlgebra.velocityExponent]
  field_simp; ring

theorem amplitude_energy_zero_germ {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta : ℝ)
    (hneg : CorrectedPulseAmplitude.constantTerm d w.coefficients eta < -(1 / 5)) :
    ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients
      (CorrectedPulseAmplitude.amplitude d w.coefficients q) q = 0 := by
  have hc : ContinuousAt (CorrectedPulseAmplitude.constantTerm d w.coefficients) eta :=
    (CorrectedPulseAmplitude.constantTerm_contDiff d w.smooth).continuous.continuousAt
  filter_upwards [hc.eventually (gt_mem_nhds hneg)] with q hq
  exact CorrectedPulseAmplitude.amplitude_totalEnergy_zero d w.coefficients q hq.le

theorem actualRatio_eq_releaseVelocityRatio {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.Ns w Amp (y, eta) /
      (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta)) =
        releaseVelocityRatio d w.coefficients eta y := by
  rw [actualNs_eq_releaseNumerator w ha eta hy hz, actualQs_eq_normalizedLag w ha eta hy]
  change releaseNumerator d eta y /
      (correctedAngular d w.coefficients (y, eta) * ReleaseMoments.normalizedLag d w.coefficients
          eta y) = _
  rw [ReleaseMoments.corrected_eq_release d w.coefficients eta hy]
  rfl

theorem actual_release_cone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {XR eta y : ℝ} (hXR : releaseRadiusThreshold d < XR) (heta : |eta| ≤ 1)
    (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    0 < OutgoingHistories.Qs w Amp (y, eta) ∧
    2 < releaseA d y ∧
    2 < XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta ∧
    releaseA d y < ConeAlgebra.coneBound
      (XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta)
      ((XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta) *
        (OutgoingHistories.Ns w Amp (y, eta) /
          (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta)))) := by
  rw [actualRatio_eq_releaseVelocityRatio w ha eta hy hz, actualQs_eq_normalizedLag w ha eta hy]
  have hc := release_true_cone w hwait hsmall hXR heta hy hy'
  exact ⟨normalizedLag_pos w eta hy hy', hc.2.1, hc.1, hc.2.2⟩

/-! ## Actual logarithmic derivatives through flattening and reset -/

/-- Reset relative, given by `relative (w.coefficients eta) (y - correctionCenter d)`. -/
noncomputable def resetRelative {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) : ℝ :=
  relative (w.coefficients eta) (y - correctionCenter d)

/-- Reset radial derivative, given by `deriv (relative (w.coefficients eta)) (y -
correctionCenter d)`. -/
noncomputable def resetRadialDerivative {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := deriv (relative (w.coefficients eta)) (y - correctionCenter d)

/-- Reset eta derivative, given by `relative (deriv w.coefficients eta) (y - correctionCenter
d)`. -/
noncomputable def resetEtaDerivative {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := relative (deriv w.coefficients eta) (y - correctionCenter d)

/-- Corrected flat slope, given by `flatteningSlope d y eta + resetRadialDerivative w eta y / (1
+ resetRelative w eta y)`. -/
noncomputable def correctedFlatSlope {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := flatteningSlope d y eta + resetRadialDerivative w eta y / (1 + resetRelative
        w eta y)

/-- Corrected eta slope, given by `etaRate d eta y + resetEtaDerivative w eta y / (1 +
resetRelative w eta y)`. -/
noncomputable def correctedEtaSlope {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := etaRate d eta y + resetEtaDerivative w eta y / (1 + resetRelative w eta y)

theorem resetFactor_ge_half {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    1 / 2 ≤ 1 + resetRelative w eta y := by
  have h := (abs_le.mp (w.small_jets eta (y - correctionCenter d)).1).1
  dsimp [resetRelative]
  linarith

theorem correctedFlat_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    HasDerivAt (fun t => OutgoingHistories.E w (t, eta))
      (OutgoingHistories.E w (y, eta) * (correctedFlatSlope w eta y - 1 / 2)) y := by
  have he : (fun t => finalAngular d (t, eta)) =ᶠ[𝓝 y] (fun t => flattened d (t, eta)) := by
    filter_upwards [gt_mem_nhds hy'] with t ht
    exact UniformAngularReset.finalAngular_before_release d eta ht.le
  have hc : HasDerivAt (fun t => finalAngular d (t, eta))
      (finalAngular d (y, eta) * (flatteningSlope d y eta - 1 / 2)) y := by
    rw [UniformAngularReset.finalAngular_before_release d eta hy'.le]
    exact (flattened_hasDerivAt d eta hy).congr_of_eventuallyEq he
  have hr := (((relative_contDiff (w.coefficients eta)).differentiable (by simp)
    (y - correctionCenter d)).hasDerivAt).comp y ((hasDerivAt_id y).sub_const (correctionCenter d))
  have hd := hc.mul (hr.const_add 1)
  have hn : 1 + resetRelative w eta y ≠ 0 := by linarith [resetFactor_ge_half w eta y]
  convert! hd using 1
  dsimp [OutgoingHistories.E, correctedAngular, correctedFlatSlope, resetRelative,
      resetRadialDerivative] at *
  field_simp [hn]; ring

theorem correctedEta_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    HasDerivAt (fun q => OutgoingHistories.E w (y, q))
      (OutgoingHistories.E w (y, eta) * correctedEtaSlope w eta y) eta := by
  have hc : HasDerivAt (fun q => finalAngular d (y, q))
      (finalAngular d (y, eta) * etaRate d eta y) eta := by
    convert! finalAngular_hasDerivAt_eta d eta y using 1
    dsimp [etaRate]
    ring
  have hr := ResetEnergyBounds.relative_coeff_hasDerivAt
    ((w.smooth.differentiable (by simp) eta).hasDerivAt) (y - correctionCenter d)
  have hd := hc.mul (hr.const_add 1)
  have hn : 1 + resetRelative w eta y ≠ 0 := by linarith [resetFactor_ge_half w eta y]
  convert! hd using 1
  dsimp [OutgoingHistories.E, correctedAngular, correctedEtaSlope, resetRelative,
      resetEtaDerivative] at *
  field_simp [hn]

theorem correctedFlat_dY_H {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    OutgoingHistories.dY (OutgoingHistories.H w) (y, eta) =
      OutgoingHistories.H w (y, eta) * correctedFlatSlope w eta y := by
  have hh := (((hasDerivAt_id y).div_const 2).exp).mul (correctedFlat_hasDerivAt w eta hy hy')
  have he : HasDerivAt (fun t => OutgoingHistories.H w (t, eta))
      (OutgoingHistories.H w (y, eta) * correctedFlatSlope w eta y) y := by
    convert! hh using 1
    dsimp [OutgoingHistories.H]
    ring
  exact (OutgoingHistories.dY_hasDerivAt (OutgoingHistories.H_smooth w) (y, eta)).unique he

theorem corrected_dEta_H {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    OutgoingHistories.dEta (OutgoingHistories.H w) (y, eta) =
      OutgoingHistories.H w (y, eta) * correctedEtaSlope w eta y := by
  have hh := (correctedEta_hasDerivAt w eta y).const_mul (Real.exp (y / 2))
  have he : HasDerivAt (fun q => OutgoingHistories.H w (y, q))
      (OutgoingHistories.H w (y, eta) * correctedEtaSlope w eta y) eta := by
    convert! hh using 1
    dsimp [OutgoingHistories.H]
    ring
  exact (OutgoingHistories.dEta_hasDerivAt (OutgoingHistories.H_smooth w) (y, eta)).unique he

theorem correctedFlat_Sq {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    OutgoingHistories.Sq w Amp (y, eta) = -correctedFlatSlope w eta y - d.h -
      StressAlgebra.axialExponent d.h * eta * correctedEtaSlope w eta y := by
  unfold OutgoingHistories.Sq OutgoingHistories.angularSource
  rw [OutgoingHistories.W_after_endpoint d ha eta hy, OutgoingHistories.U_after_endpoint d Amp eta
      hy,
    correctedFlat_dY_H w eta hy hy', corrected_dEta_H]
  dsimp only
  field_simp [(OutgoingHistories.H_pos w (y, eta)).ne']; ring

/-- Reset jet constant, given by `Classical.choose relative_first_jet_bound`. -/
noncomputable def resetJetConstant : ℝ := Classical.choose relative_first_jet_bound

theorem resetJetConstant_pos : 0 < resetJetConstant := (Classical.choose_spec
    relative_first_jet_bound).1

theorem relative_radial_bound (c : Coeff) (y : ℝ) :
    |deriv (relative c) y| ≤ resetJetConstant * ‖c‖ :=
  ((Classical.choose_spec relative_first_jet_bound).2 c y).2

/-- Reset source error, given by `(2 * resetJetConstant + 2) * (K * d.core.lam ^ (28 : ℕ))`. -/
noncomputable def resetSourceError (d : TailData) (K : ℝ) : ℝ :=
  (2 * resetJetConstant + 2) * (K * d.core.lam ^ (28 : ℕ))

theorem reset_radial_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    |resetRadialDerivative w eta y / (1 + resetRelative w eta y)| ≤
      2 * resetJetConstant * (K * d.core.lam ^ (28 : ℕ)) := by
  have hden : 0 < 1 + resetRelative w eta y := by linarith [resetFactor_ge_half w eta y]
  have hr := (relative_radial_bound (w.coefficients eta) (y - correctionCenter d)).trans
    (mul_le_mul_of_nonneg_left (w.coefficient_bound eta) resetJetConstant_pos.le)
  change |resetRadialDerivative w eta y| ≤ _ at hr
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hprod := mul_le_mul_of_nonneg_left (resetFactor_ge_half w eta y)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) resetJetConstant_pos.le)
      (ResetEnergyBounds.coefficient_scale_nonneg w))
  nlinarith

theorem reset_eta_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    |resetEtaDerivative w eta y / (1 + resetRelative w eta y)| ≤ 4 * (K * d.core.lam ^ (28 : ℕ)) :=
        by
  have hden : 0 < 1 + resetRelative w eta y := by linarith [resetFactor_ge_half w eta y]
  have hr := ResetEnergyBounds.relative_eta_bound w eta (y - correctionCenter d)
  change |resetEtaDerivative w eta y| ≤ _ at hr
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hprod := mul_le_mul_of_nonneg_left (resetFactor_ge_half w eta y)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (ResetEnergyBounds.coefficient_scale_nonneg w))
  nlinarith

theorem eta_times_etaRate_nonpos (d : TailData) (eta y : ℝ) : eta * etaRate d eta y ≤ 0 := by
  have hp : 0 ≤ 2 * eta ^ 2 / (1 + eta ^ 2) := by positivity
  have hs := sigma_le_one ((y - d.core.endpoint) / flattenLength)
  calc
    eta * etaRate d eta y = (sigma ((y - d.core.endpoint) / flattenLength) - 1) *
        (2 * eta ^ 2 / (1 + eta ^ 2)) := by dsimp [etaRate]; ring
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hp

theorem correctedFlatSlope_bounds {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) (heta : eta ^ 2 ≤ 1) :
    -d.core.lam - 1 / 10 - resetSourceError d K ≤ correctedFlatSlope w eta y ∧
      correctedFlatSlope w eta y ≤ -d.core.lam + resetSourceError d K := by
  have hf := flatteningSlope_bounds d y eta heta
  have hr := abs_le.mp (reset_radial_ratio_bound w eta y)
  have hs := ResetEnergyBounds.coefficient_scale_nonneg w
  dsimp [correctedFlatSlope, resetSourceError]
  constructor <;> nlinarith

theorem correctedFlat_source_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) (heta : |eta| ≤ 1) {y : ℝ}
    (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    d.core.lam / 2 - resetSourceError d K ≤ OutgoingHistories.Sq w Amp (y, eta) := by
  have heta2 : eta ^ 2 ≤ 1 := by have h := abs_le.mp heta; nlinarith
  have hf := flatteningSlope_bounds d y eta heta2
  have hr := abs_le.mp (reset_radial_ratio_bound w eta y)
  have hD : 0 ≤ StressAlgebra.axialExponent d.h := by
    dsimp [StressAlgebra.axialExponent]
    linarith [d.h_lt_half]
  have hD' : StressAlgebra.axialExponent d.h ≤ 1 / 2 := by
    dsimp [StressAlgebra.axialExponent]
    linarith [d.h_pos]
  have hbase := mul_nonpos_of_nonneg_of_nonpos hD (eta_times_etaRate_nonpos d eta y)
  have hDEta : |StressAlgebra.axialExponent d.h * eta| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hD]
    nlinarith [mul_le_mul_of_nonneg_left heta hD]
  have he := mul_le_mul hDEta (reset_eta_ratio_bound w eta y) (abs_nonneg _) (by
      norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← abs_mul] at he
  have he' := (le_abs_self _).trans he
  rw [correctedFlat_Sq w ha eta hy hy']
  dsimp [correctedFlatSlope, correctedEtaSlope, resetSourceError]
  nlinarith [d.h_small]

theorem correctedFlat_geometry {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hsmall : resetSourceError d K ≤ d.core.lam / 4) (eta y : ℝ) (heta : eta ^ 2 ≤ 1) :
    2 < 2 - 2 * correctedFlatSlope w eta y ∧ 2 - 2 * correctedFlatSlope w eta y ≤ 4 ∧
      1 + correctedFlatSlope w eta y ≤ 1 := by
  have h := correctedFlatSlope_bounds w eta y heta
  constructor
  · linarith [d.core.lam_pos]
  constructor
  · linarith [d.core.lam_lt]
  · linarith [d.core.lam_pos]

theorem ode_constant_barrier {q a b : ℝ → ℝ} (hq : Continuous q) (ha : Continuous a)
    {lo hi B : ℝ} (hlh : lo ≤ hi) (hinit : B ≤ q lo)
    (hODE : ∀ t ∈ Ioo lo hi, HasDerivAt q (b t - a t * q t) t)
    (hsource : ∀ t ∈ Ioo lo hi, a t * B ≤ b t) : B ≤ q hi := by
  let g : ℝ → ℝ := fun t => Real.exp (primitive a t) * (q t - B)
  have hp : Continuous (primitive a) := continuous_iff_continuousAt.mpr
    (fun t => (primitive_hasDerivAt ha t).continuousAt)
  have hg : Continuous g := (Real.continuous_exp.comp hp).mul (hq.sub continuous_const)
  have hgd : ∀ t ∈ Ioo lo hi,
      HasDerivAt g (Real.exp (primitive a t) * (b t - a t * B)) t := by
    intro t ht
    have hd := ((primitive_hasDerivAt ha t).exp).mul ((hODE t ht).sub_const B)
    convert! hd using 1
    ring
  have hm : MonotoneOn g (Icc lo hi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc lo hi) hg.continuousOn
    · intro t ht
      have ht' : t ∈ Ioo lo hi := by simpa only [interior_Icc] using ht
      exact (hgd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo lo hi := by simpa only [interior_Icc] using ht
      rw [(hgd t ht').deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hsource t ht'))
  have hg0 : 0 ≤ g lo := mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hinit)
  have hg1 : 0 ≤ g hi := hg0.trans (hm ⟨le_rfl, hlh⟩ ⟨hlh, le_rfl⟩ hlh)
  change 0 ≤ Real.exp (primitive a hi) * (q hi - B) at hg1
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hg1)

theorem flatten_Qs_lower_of_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hsmall : resetSourceError d K ≤ d.core.lam / 4) (eta : ℝ) (heta : |eta| ≤ 1)
    (hinit : d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (d.core.endpoint, eta))
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (y, eta) := by
  have heta2 : eta ^ 2 ≤ 1 := by have h := abs_le.mp heta; nlinarith
  let rate : ℝ → ℝ := fun t => 1 + OutgoingHistories.dY (OutgoingHistories.H w) (t, eta) /
    OutgoingHistories.H w (t, eta)
  have hr : Continuous rate := by
    apply continuous_const.add
    exact ((OutgoingHistories.dY_smooth (OutgoingHistories.H_smooth w)).continuous.comp
      (continuous_id.prodMk continuous_const)).div
      ((OutgoingHistories.H_smooth w).continuous.comp (continuous_id.prodMk continuous_const))
      (fun t => (OutgoingHistories.H_pos w (t, eta)).ne')
  apply ode_constant_barrier (b := fun t => OutgoingHistories.Sq w Amp (t, eta))
    ((OutgoingHistories.Qs_smooth w ha).continuous.comp (continuous_id.prodMk continuous_const)) hr
        hy hinit
  · intro t _
    exact OutgoingHistories.Qs_hasDerivAt w ha (t, eta)
  · intro t ht
    have htR : t < d.releaseStart := ht.2.trans_le hy'
    have hr_eq : rate t = 1 + correctedFlatSlope w eta t := by
      dsimp [rate]
      rw [correctedFlat_dY_H w eta ht.1.le htR]
      field_simp [(OutgoingHistories.H_pos w (t, eta)).ne']
    rw [hr_eq]
    have hrate := (correctedFlat_geometry w hsmall eta t heta2).2.2
    have hsource := correctedFlat_source_lower w ha eta heta ht.1.le htR
    have hm := mul_le_mul_of_nonneg_right hrate (div_nonneg d.core.lam_pos.le (by
        norm_num : (0 : ℝ) ≤ 4))
    nlinarith

theorem corrected_flatten_Qs_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (hpulse : PulseCone.sourceConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 8)
    (hh1 : d.h ≤ 1 / 100) (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (hreset : resetSourceError d K ≤ d.core.lam / 4)
    (eta : ℝ) (heta : |eta| ≤ 1) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    d.core.lam / 4 ≤ OutgoingHistories.Qs w
      (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) := by
  exact flatten_Qs_lower_of_endpoint w (CorrectedPulseAmplitude.amplitude_contDiff d w.smooth)
    hreset eta heta
    (PulseCone.corrected_Qs_endpoint_lower w hK hwait hsmall hscale hpulse hh1 hhT heta) hy hy'

/-! ## Energy and its parameter derivative on the finite post-pulse interval -/

theorem corrected_density_prefix_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) {y : ℝ} (hy : d.core.endpoint ≤ y)
    (hy' : y ≤ d.releaseStart) :
    Real.exp y * OutgoingHistories.E w (y, eta) ^ 2 ≤
      (9 / 4 : ℝ) * energyDensity d eta d.core.endpoint := by
  have hr := abs_le.mp (w.small_jets eta (y - correctionCenter d)).1
  have hr2 : (1 + relative (w.coefficients eta) (y - correctionCenter d)) ^ 2 ≤ 9 / 4 := by
    nlinarith
  have h := mul_le_mul_of_nonneg_left hr2 (energyDensity_pos d eta y).le
  have he := energyDensity_prefix_le d eta heta hy hy'
  change Real.exp y * (finalAngular d (y, eta) *
    (1 + relative (w.coefficients eta) (y - correctionCenter d))) ^ 2 ≤ _
  dsimp [energyDensity] at h he ⊢
  nlinarith

theorem corrected_square_prefix_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) {y : ℝ} (hy : d.core.endpoint ≤ y)
    (hy' : y ≤ d.releaseStart) :
    OutgoingHistories.E w (y, eta) ^ 2 ≤ (9 / 4 : ℝ) * finalAngular d (d.core.endpoint, eta) ^ 2 :=
        by
  have hd := corrected_density_prefix_le w eta heta hy hy'
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hy)
    (sq_nonneg (OutgoingHistories.E w (y, eta)))
  dsimp [energyDensity] at hd
  nlinarith [Real.exp_pos d.core.endpoint]

theorem correctedEtaSlope_abs_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta y : ℝ) :
    |correctedEtaSlope w eta y| ≤ 5 := by
  exact (abs_add_le _ _).trans (by
    have h1 := etaRate_bound d eta y
    have h2 := reset_eta_ratio_bound w eta y
    nlinarith)

theorem actualS_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ)
    (hz : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0) :
    OutgoingHistories.S w Amp (d.core.endpoint, eta) =
      (1 / 2 : ℝ) * (postPulseEnergy d eta + ResetEnergyBounds.resetEnergy d w.coefficients eta) :=
          by
  rw [actualS_backward w ha eta le_rfl hz, ResetEnergyBounds.integral_corrected_energy]

theorem actualS_eta_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.dEta (OutgoingHistories.S w Amp) (d.core.endpoint, eta) =
      (1 / 2 : ℝ) * (deriv (postPulseEnergy d) eta +
        deriv (ResetEnergyBounds.resetEnergy d w.coefficients) eta) := by
  have he : (fun q => OutgoingHistories.S w Amp (d.core.endpoint, q)) =ᶠ[𝓝 eta]
      (fun q => (1 / 2 : ℝ) * (postPulseEnergy d q + ResetEnergyBounds.resetEnergy d w.coefficients
          q)) := by
    filter_upwards [hz] with q hq
    exact actualS_endpoint w ha q hq
  have hd := (((postPulseEnergy_contDiff d).differentiable (by simp) eta).hasDerivAt.fun_add
    (((ResetEnergyBounds.resetEnergy_contDiff d w.smooth).differentiable (by
        simp) eta).hasDerivAt)).const_mul
      (1 / 2 : ℝ)
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.S_smooth w ha), he.deriv_eq, hd.deriv]

theorem actualS_after_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    HasDerivAt (fun t => OutgoingHistories.S w Amp (t, eta))
      (-(Real.exp y * OutgoingHistories.E w (y, eta) ^ 2) / 2) y := by
  have hd := OutgoingHistories.S_hasDerivAt w ha (y, eta)
  dsimp [OutgoingHistories.X, OutgoingHistories.energyDensity] at hd
  rw [OutgoingHistories.U_after_endpoint d Amp eta hy] at hd
  convert! hd using 1
  ring

theorem actualS_eta_after_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    HasDerivAt (fun t => OutgoingHistories.dEta (OutgoingHistories.S w Amp) (t, eta))
      (-(Real.exp y * OutgoingHistories.E w (y, eta) ^ 2) * correctedEtaSlope w eta y) y := by
  have hd := OutgoingHistories.dEta_S_hasDerivAt w ha (y, eta)
  have he : OutgoingHistories.dEta (OutgoingHistories.E w) (y, eta) =
      OutgoingHistories.E w (y, eta) * correctedEtaSlope w eta y :=
    (OutgoingHistories.dEta_hasDerivAt (OutgoingHistories.E_smooth w) (y, eta)).unique
      (correctedEta_hasDerivAt w eta y)
  rw [OutgoingHistories.U_after_endpoint d Amp eta hy, he] at hd
  dsimp [OutgoingHistories.X] at hd
  convert! hd using 1
  ring

theorem abs_increment_le {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ C) : |f b - f a| ≤ C * (b - a) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hf t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1, ht.2.le⟩) b ⟨hab, le_rfl⟩
  simpa only [Real.norm_eq_abs] using h

/-- Finite energy budget, given by `flattenLength + releaseConstant + 40 + 20 * (d.releaseStart
- d.core.endpoint)`. -/
noncomputable def finiteEnergyBudget (d : TailData) : ℝ :=
  flattenLength + releaseConstant + 40 + 20 * (d.releaseStart - d.core.endpoint)

theorem finiteEnergyBudget_pos (d : TailData) : 0 < finiteEnergyBudget d := by
  dsimp [finiteEnergyBudget]
  linarith [flattenLength_pos, releaseConstant_pos, endpoint_le_releaseStart d]

theorem actualS_finite_bounds {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta : ℝ) (heta : eta ^ 2 ≤ 1)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0)
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    |OutgoingHistories.S w Amp (y, eta)| ≤ finiteEnergyBudget d * energyDensity d eta
        d.core.endpoint ∧
    |OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y, eta)| ≤
      finiteEnergyBudget d * energyDensity d eta d.core.endpoint := by
  have hz0 : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0 :=
    Filter.Eventually.self_of_nhds (x := eta)
      (p := fun q => CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) hz
  have hD := (energyDensity_pos d eta d.core.endpoint).le
  have hL : 0 ≤ d.releaseStart - d.core.endpoint := sub_nonneg.mpr (endpoint_le_releaseStart d)
  have hSI : |OutgoingHistories.S w Amp (d.core.endpoint, eta)| ≤
      ((d.releaseStart - d.core.endpoint + releaseConstant) / 2 + 12) * energyDensity d eta
          d.core.endpoint := by
    rw [actualS_endpoint w ha eta hz0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hsum := abs_add_le (postPulseEnergy d eta) (ResetEnergyBounds.resetEnergy d w.coefficients
        eta)
    rw [abs_of_nonneg (postPulseEnergy_nonneg d eta)] at hsum
    have hR := ResetEnergyBounds.resetEnergy_abs_le w eta heta
    have hs := mul_le_mul_of_nonneg_right hsmall hD
    nlinarith [postPulseEnergy_le_length d eta heta]
  have hSEI : |OutgoingHistories.dEta (OutgoingHistories.S w Amp) (d.core.endpoint, eta)| ≤
      (flattenLength + 12) * energyDensity d eta d.core.endpoint := by
    rw [actualS_eta_endpoint w ha eta hz, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hsum := abs_add_le (deriv (postPulseEnergy d) eta)
      (deriv (ResetEnergyBounds.resetEnergy d w.coefficients) eta)
    have hs := mul_le_mul_of_nonneg_right hsmall hD
    nlinarith [abs_deriv_postPulseEnergy_le d eta heta, ResetEnergyBounds.resetEnergy_deriv_abs_le
        w eta heta]
  have hSD := abs_increment_le hy (fun t ht => actualS_after_hasDerivAt w ha eta ht.1)
    (C := 2 * energyDensity d eta d.core.endpoint) (fun t ht => by
      rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      norm_num
      have hd := corrected_density_prefix_le w eta heta ht.1 (ht.2.trans hy')
      nlinarith)
  have hSED := abs_increment_le hy (fun t ht => actualS_eta_after_hasDerivAt w ha eta ht.1)
    (C := 12 * energyDensity d eta d.core.endpoint) (fun t ht => by
      rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      have hd := corrected_density_prefix_le w eta heta ht.1 (ht.2.trans hy')
      have hs := mul_le_mul_of_nonneg_left (correctedEtaSlope_abs_le w hsmall eta t)
        (mul_nonneg (Real.exp_pos t).le (sq_nonneg (OutgoingHistories.E w (t, eta))))
      nlinarith)
  have hlen := mul_le_mul_of_nonneg_right (show y - d.core.endpoint ≤ d.releaseStart -
      d.core.endpoint by
      linarith) hD
  have hS := abs_sub_le (OutgoingHistories.S w Amp (y, eta))
    (OutgoingHistories.S w Amp (d.core.endpoint, eta)) 0
  have hSE := abs_sub_le (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y, eta))
    (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (d.core.endpoint, eta)) 0
  simp only [sub_zero] at hS hSE
  dsimp [finiteEnergyBudget]
  constructor <;> nlinarith [mul_nonneg flattenLength_pos.le hD, mul_nonneg releaseConstant_pos.le
      hD,
    mul_nonneg hL hD]

/-- Finite numerator budget, given by `5 * finiteEnergyBudget d + 12 *
CorrectedPressureBounds.correctedConstant`. -/
noncomputable def finiteNumeratorBudget (d : TailData) : ℝ :=
  5 * finiteEnergyBudget d + 12 * CorrectedPressureBounds.correctedConstant

theorem finiteNumeratorBudget_pos (d : TailData) : 0 < finiteNumeratorBudget d := by
  dsimp [finiteNumeratorBudget]
  have := finiteEnergyBudget_pos d
  have := CorrectedPressureBounds.correctedConstant_pos
  positivity

theorem actualNs_finite_bound {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta : ℝ) (heta : |eta| ≤ 1)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0)
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    |OutgoingHistories.Ns w Amp (y, eta)| ≤
      finiteNumeratorBudget d * finalAngular d (d.core.endpoint, eta) ^ 2 := by
  have heta2 : eta ^ 2 ≤ 1 := by have h := abs_le.mp heta; nlinarith
  have hS := actualS_finite_bounds w ha hsmall eta heta2 hz hy hy'
  have hB := (finiteEnergyBudget_pos d).le
  have hF := sq_nonneg (finalAngular d (d.core.endpoint, eta))
  have hdiv : ∀ z : ℝ, |z| ≤ finiteEnergyBudget d * energyDensity d eta d.core.endpoint →
      |z / Real.exp y| ≤ finiteEnergyBudget d * finalAngular d (d.core.endpoint, eta) ^ 2 := by
    intro z hz
    rw [abs_div, abs_of_pos (Real.exp_pos y)]
    apply (div_le_iff₀ (Real.exp_pos y)).mpr
    have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) (mul_nonneg hB hF)
    dsimp [energyDensity] at hz
    nlinarith
  have hs0 := hdiv _ hS.1
  have hs1 := hdiv _ hS.2
  have hP := CorrectedPressureBounds.corrected_bounds_of_small w hsmall
    ((SchedulePressure.endpoint_pos d).le.trans hy) heta
  have hP0 : |OutgoingHistories.Pi w (y, eta)| ≤
      CorrectedPressureBounds.correctedConstant * OutgoingHistories.E w (y, eta) ^ 2 := by
    rw [actualPi_eq_correctedPi]
    exact hP.1
  have hP1 : |OutgoingHistories.dEta (OutgoingHistories.Pi w) (y, eta)| ≤
      CorrectedPressureBounds.correctedConstant * OutgoingHistories.E w (y, eta) ^ 2 := by
    rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.Pi_smooth w)]
    have he : (fun q => OutgoingHistories.Pi w (y, q)) = CorrectedPressureBounds.correctedPi w y :=
      funext (actualPi_eq_correctedPi w y)
    rw [he]
    exact hP.2
  have hE := mul_le_mul_of_nonneg_left (corrected_square_prefix_le w eta heta2 hy hy')
    CorrectedPressureBounds.correctedConstant_pos.le
  have hd : |StressAlgebra.coordinateFactor eta| ≤ 1 := by
    dsimp [StressAlgebra.coordinateFactor]
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - eta ^ 2)]
    nlinarith [sq_nonneg eta]
  have hh : |4 * d.h * eta| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos d.h_pos]
    have hm := mul_le_mul_of_nonneg_left heta (show 0 ≤ 4 * d.h by linarith [d.h_pos])
    nlinarith [d.h_lt_half]
  have ha0 : 0 ≤ StressAlgebra.velocityExponent d.h := by
    dsimp [StressAlgebra.velocityExponent]; linarith [d.h_pos]
  have ha1 : StressAlgebra.velocityExponent d.h ≤ 1 := by
    dsimp [StressAlgebra.velocityExponent]; linarith [d.h_lt_half]
  have hav : |4 * StressAlgebra.velocityExponent d.h * eta| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg ha0]
    have hm := mul_le_mul_of_nonneg_left heta (show 0 ≤ 4 * StressAlgebra.velocityExponent d.h by
        positivity)
    nlinarith
  have h1 := mul_le_mul hh hs0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul hd hs1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h3 := mul_le_mul hav (hP0.trans hE) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
  have h4 := mul_le_mul hd (hP1.trans hE) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [← abs_mul] at h1 h2 h3 h4
  rw [OutgoingHistories.Ns_after_endpoint w ha eta hy]
  rw [show (4 * d.h * eta * OutgoingHistories.S w Amp (y, eta) -
      StressAlgebra.coordinateFactor eta * OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta)) /
      Real.exp y = 4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y) -
      StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta) /
        Real.exp y) by ring]
  have ht1 := abs_sub_le
    (4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y)) 0
    (StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
        eta) / Real.exp y))
  have ht2 := abs_add_le
    (4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y) -
      StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta) / Real.exp y))
    (4 * StressAlgebra.velocityExponent d.h * eta * OutgoingHistories.Pi w (y, eta))
  have ht3 := abs_sub_le
    (4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y) -
      StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta) / Real.exp y) +
      4 * StressAlgebra.velocityExponent d.h * eta * OutgoingHistories.Pi w (y, eta)) 0
    (StressAlgebra.coordinateFactor eta * OutgoingHistories.dEta (OutgoingHistories.Pi w) (y, eta))
  simp only [sub_zero, zero_sub, abs_neg] at ht1 ht3
  dsimp [finiteNumeratorBudget]
  nlinarith [mul_nonneg hB hF, mul_nonneg CorrectedPressureBounds.correctedConstant_pos.le hF]

theorem lambda_log_bound (d : TailData) : d.core.lam * Real.log (1 / d.core.lam) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr d.core.lam_pos)
  have hm := mul_le_mul_of_nonneg_left h d.core.lam_pos.le
  have hid : d.core.lam * (1 / d.core.lam - 1) = 1 - d.core.lam := by
    field_simp [d.core.lam_pos.ne']
  rw [hid] at hm
  linarith [d.core.lam_pos]

theorem lambda_finite_length_bound (d : TailData) :
    d.core.lam * (d.releaseStart - d.core.endpoint) ≤ flattenLength + 30 := by
  have hf := mul_le_mul_of_nonneg_right (show d.core.lam ≤ 1 by
      linarith [d.core.lam_lt]) flattenLength_pos.le
  have hl := lambda_log_bound d
  dsimp [TailData.releaseStart, TailData.flattenEnd, TailData.uniformWait]
  nlinarith

/-- Finite numerator constant, given by `5 * (flattenLength + releaseConstant + 40 + 20 *
(flattenLength + 30)) + 12 * CorrectedPressureBounds.correctedConstant`. -/
noncomputable def finiteNumeratorConstant : ℝ :=
  5 * (flattenLength + releaseConstant + 40 + 20 * (flattenLength + 30)) +
    12 * CorrectedPressureBounds.correctedConstant

theorem finiteNumeratorConstant_pos : 0 < finiteNumeratorConstant := by
  dsimp [finiteNumeratorConstant]
  have := flattenLength_pos
  have := releaseConstant_pos
  have := CorrectedPressureBounds.correctedConstant_pos
  positivity

theorem finiteNumeratorBudget_bound (d : TailData) :
    d.core.lam * finiteNumeratorBudget d ≤ finiteNumeratorConstant := by
  have hl : d.core.lam ≤ 1 := by linarith [d.core.lam_lt]
  have hbase := mul_le_mul_of_nonneg_right hl
    (show 0 ≤ flattenLength + releaseConstant + 40 by
        linarith [flattenLength_pos, releaseConstant_pos])
  have hP := mul_le_mul_of_nonneg_right hl CorrectedPressureBounds.correctedConstant_pos.le
  have hlen := lambda_finite_length_bound d
  dsimp [finiteNumeratorBudget, finiteEnergyBudget, finiteNumeratorConstant]
  nlinarith

/-! ## A lower amplitude bound up to release

The finite waiting interval loses only eighteen powers of `lam`, whereas the
earlier scheduled wait has already supplied thirty powers.
-/

theorem flattenFactor_ge_half (d : TailData) (eta y : ℝ) : 1 / 2 ≤ flattenFactor d (y, eta) := by
  have hJ : 0 ≤ logShape eta := Real.log_nonneg (by nlinarith [sq_nonneg eta])
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right (sigma_le_one ((y - d.core.endpoint) / flattenLength)) hlog
  have hp := mul_nonneg (sigma_nonneg ((y - d.core.endpoint) / flattenLength)) hJ
  have hh : -Real.log 2 ≤ sigma ((y - d.core.endpoint) / flattenLength) * (logShape eta - Real.log
      2) := by
    nlinarith
  have he := Real.exp_le_exp.mpr hh
  simp only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div] at he
  exact he

/-- Finite amplitude constant, given by `Real.exp (-(3 / 5 : ℝ) * flattenLength) / 4`. -/
noncomputable def finiteAmplitudeConstant : ℝ := Real.exp (-(3 / 5 : ℝ) * flattenLength) / 4

theorem finiteAmplitudeConstant_pos : 0 < finiteAmplitudeConstant := div_pos (Real.exp_pos _) (by
    norm_num)

theorem corrected_amplitude_finite_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) * d.core.lam ^ (18 : ℕ) ≤
      OutgoingHistories.E w (y, eta) := by
  have hE := finalAngular_pos d (d.core.endpoint, eta)
  have hr := radialAmplitude_hold d.core.dropLength_pos.le (coreEndpoint_ge_hold d) hy
    (P := d.core.P) (lam := d.core.lam)
  have hang : angular d.core.P d.core.dropLength d.core.lam (y, eta) =
      finalAngular d (d.core.endpoint, eta) * Real.exp (-(1 / 2 + d.core.lam) * (y -
          d.core.endpoint)) := by
    rw [finalAngular_before d eta le_rfl]
    dsimp [angular]
    rw [hr]
    ring
  have hpow : Real.exp (-(3 / 5 : ℝ) * (d.releaseStart - d.core.endpoint)) =
      Real.exp (-(3 / 5 : ℝ) * flattenLength) * d.core.lam ^ (18 : ℕ) := by
    have h18 : Real.exp (-(18 : ℝ) * Real.log (1 / d.core.lam)) = d.core.lam ^ (18 : ℕ) := by
      simpa using OutgoingPulseBounds.exp_log_inverse_nat d.core.lam_pos 18
    rw [show -(3 / 5 : ℝ) * (d.releaseStart - d.core.endpoint) =
      -(3 / 5 : ℝ) * flattenLength + -(18 : ℝ) * Real.log (1 / d.core.lam) by
        dsimp [TailData.releaseStart, TailData.flattenEnd, TailData.uniformWait]; ring,
      Real.exp_add, h18]
  have hrate : -(3 / 5 : ℝ) * (d.releaseStart - d.core.endpoint) ≤
      -(1 / 2 + d.core.lam) * (y - d.core.endpoint) := by
    have hm := mul_le_mul_of_nonneg_right (show 1 / 2 + d.core.lam ≤ (3 / 5 : ℝ) by
        linarith [d.core.lam_lt])
      (sub_nonneg.mpr hy)
    linarith
  have he := Real.exp_le_exp.mpr hrate
  rw [hpow] at he
  have hflat := flattenFactor_ge_half d eta y
  have hrel := resetFactor_ge_half w eta y
  have he1 := mul_le_mul_of_nonneg_left he hE.le
  have he2 := mul_le_mul he1 hflat (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg hE.le (Real.exp_pos _).le)
  have he3 := mul_le_mul he2 hrel (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg (mul_nonneg hE.le (Real.exp_pos _).le) (by linarith : 0 ≤ flattenFactor d (y, eta)))
  change _ ≤ finalAngular d (y, eta) * (1 + resetRelative w eta y)
  rw [TailEnergyBounds.finalAngular_before_release d eta hy']
  dsimp only [flattened]
  rw [hang]
  dsimp [finiteAmplitudeConstant]
  nlinarith

theorem endpointAmplitude_le_pulse (d : TailData) (eta : ℝ) :
    finalAngular d (d.core.endpoint, eta) ≤ pulseAmplitude d.core := by
  have hy : d.core.pulseStart ≤ d.core.endpoint := by
    dsimp [OutgoingSchedule.Parameters.endpoint]
    linarith [d.core.pulseLength_pos]
  have hr := radialAmplitude_hold d.core.dropLength_pos.le d.core.pulseStart_ge_hold hy
    (P := d.core.P) (lam := d.core.lam)
  rw [finalAngular_before d eta le_rfl]
  dsimp [angular]
  rw [hr]
  change pulseAmplitude d.core * Real.exp (-(1 / 2 + d.core.lam) * (d.core.endpoint -
      d.core.pulseStart)) *
    shape eta ≤ pulseAmplitude d.core
  have he : Real.exp (-(1 / 2 + d.core.lam) * (d.core.endpoint - d.core.pulseStart)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [d.core.lam_pos])
  have hs : shape eta ≤ 1 := by
    dsimp [shape]
    rw [← one_div]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg eta]
  have hm := mul_le_mul he hs (shape_pos eta).le (by norm_num : (0 : ℝ) ≤ 1)
  have hp := mul_le_mul_of_nonneg_left hm (pulseAmplitude_pos d.core).le
  nlinarith

/-- Finite cone constant, given by `(4 * finiteNumeratorConstant / finiteAmplitudeConstant) * (P
* Real.exp (Real.exp m + 12))`. -/
noncomputable def finiteConeConstant (P m : ℝ) : ℝ :=
  (4 * finiteNumeratorConstant / finiteAmplitudeConstant) * (P * Real.exp (Real.exp m + 12))

theorem finiteConeConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < finiteConeConstant P m := by
  dsimp [finiteConeConstant]
  exact mul_pos (div_pos (mul_pos (by
      norm_num) finiteNumeratorConstant_pos) finiteAmplitudeConstant_pos)
    (mul_pos hP (Real.exp_pos _))

theorem actual_finite_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta : ℝ) (heta : |eta| ≤ 1)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0)
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart)
    (hQ : d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (y, eta)) :
    |OutgoingHistories.Ns w Amp (y, eta) /
      (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta))| ≤
      finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) := by
  have he := corrected_amplitude_finite_lower w eta hy hy'
  have hq : 0 < OutgoingHistories.Qs w Amp (y, eta) := lt_of_lt_of_le (by
      linarith [d.core.lam_pos]) hQ
  have hden := mul_pos (OutgoingHistories.E_pos w (y, eta)) hq
  have hnum := actualNs_finite_bound w ha hsmall eta heta hz hy hy'
  have hbud : finiteNumeratorBudget d ≤ finiteNumeratorConstant / d.core.lam :=
    (le_div_iff₀ d.core.lam_pos).mpr (by nlinarith [finiteNumeratorBudget_bound d])
  have hend := (endpointAmplitude_le_pulse d eta).trans (OutgoingPulseBounds.pulseAmplitude_small
      d.core hwait)
  have hE := finalAngular_pos d (d.core.endpoint, eta)
  have he0 : 0 < finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) * d.core.lam ^ (18
      : ℕ) :=
    mul_pos (mul_pos finiteAmplitudeConstant_pos hE) (pow_pos d.core.lam_pos _)
  have hdl := mul_le_mul he hQ (by linarith [d.core.lam_pos] : (0 : ℝ) ≤ d.core.lam / 4)
    (OutgoingHistories.E_pos w (y, eta)).le
  have hdl0 : 0 < finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) *
      d.core.lam ^ (18 : ℕ) * (d.core.lam / 4) := mul_pos he0 (by linarith [d.core.lam_pos])
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ (finiteNumeratorConstant / d.core.lam * finalAngular d (d.core.endpoint, eta) ^ 2) /
        (finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) * d.core.lam ^ (18 : ℕ) *
            (d.core.lam / 4)) :=
      div_le_div₀ (mul_nonneg (div_nonneg finiteNumeratorConstant_pos.le d.core.lam_pos.le)
          (sq_nonneg _))
        (hnum.trans (mul_le_mul_of_nonneg_right hbud (sq_nonneg _))) hdl0 hdl
    _ = (4 * finiteNumeratorConstant / finiteAmplitudeConstant) *
        (finalAngular d (d.core.endpoint, eta) / d.core.lam ^ (20 : ℕ)) := by
      field_simp [d.core.lam_pos.ne', hE.ne', finiteAmplitudeConstant_pos.ne']
    _ ≤ (4 * finiteNumeratorConstant / finiteAmplitudeConstant) *
        ((d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ) / d.core.lam ^ (20
            : ℕ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hend (pow_pos d.core.lam_pos _).le)
        (div_nonneg (mul_nonneg (by
            norm_num) finiteNumeratorConstant_pos.le) finiteAmplitudeConstant_pos.le)
    _ = _ := by
      have hp : d.core.lam ^ (30 : ℕ) / d.core.lam ^ (20 : ℕ) = d.core.lam ^ (10 : ℕ) := by
        field_simp [d.core.lam_pos.ne']
      rw [show (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ) /
          d.core.lam ^ (20 : ℕ) = (d.core.P * Real.exp (Real.exp d.core.m + 12)) *
            (d.core.lam ^ (30 : ℕ) / d.core.lam ^ (20 : ℕ)) by ring, hp]
      dsimp [finiteConeConstant]
      ring

/-! ## Cone quantities of the actual corrected profile -/

/-- Actual A, given by `1 - 2 * deriv (fun t => Real.log (OutgoingHistories.E w (t, eta))) y`. -/
noncomputable def actualA {d : TailData} {K : ℝ} (w : ResetWitness d K) (y eta : ℝ) : ℝ :=
  1 - 2 * deriv (fun t => Real.log (OutgoingHistories.E w (t, eta))) y

/-- Actual bs, given by `2 * deriv (fun t => OutgoingHistories.U d Amp (t, eta)) y /
OutgoingHistories.E w (y, eta)`. -/
noncomputable def actualBs {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (y eta : ℝ) : ℝ :=
  2 * deriv (fun t => OutgoingHistories.U d Amp (t, eta)) y / OutgoingHistories.E w (y, eta)

theorem actualA_finite {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    actualA w y eta = 2 - 2 * correctedFlatSlope w eta y := by
  have hd := (correctedFlat_hasDerivAt w eta hy hy').log (OutgoingHistories.E_pos w (y, eta)).ne'
  unfold actualA
  rw [hd.deriv]
  change 1 - 2 * (OutgoingHistories.E w (y, eta) * (correctedFlatSlope w eta y - 1 / 2) /
    OutgoingHistories.E w (y, eta)) = _
  field_simp [(OutgoingHistories.E_pos w (y, eta)).ne']; ring

theorem actualA_release {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) : actualA w y eta = releaseA d y :=
  corrected_releaseA d w.coefficients eta hy

theorem actualBs_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    actualBs w Amp y eta = 0 := by
  have hf : Differentiable ℝ (fun t => OutgoingHistories.U d Amp (t, eta)) :=
    ((OutgoingHistories.U_smooth d ha).comp (contDiff_id.prodMk contDiff_const)).differentiable (by
        simp)
  have hz : HasDerivWithinAt (fun t => OutgoingHistories.U d Amp (t, eta)) 0 (Ici y) y := by
    apply (hasDerivWithinAt_const y (Ici y) (0 : ℝ)).congr
    · intro t ht
      exact OutgoingHistories.U_after_endpoint d Amp eta (hy.trans ht)
    · exact OutgoingHistories.U_after_endpoint d Amp eta hy
  have hd : deriv (fun t => OutgoingHistories.U d Amp (t, eta)) y = 0 :=
    (uniqueDiffOn_Ici y y (show y ∈ Ici y from le_refl y)).eq_deriv _ (hf
        y).hasDerivAt.hasDerivWithinAt hz
  simp [actualBs, hd]

theorem actualP2_eq {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (XR eta y : ℝ) (heta : eta ^ 2 ≤ 1)
    (hQ : 0 < OutgoingHistories.Qs w Amp (y, eta)) :
    OutgoingHistories.p2 XR w Amp (y, eta) = OutgoingHistories.p1 XR w Amp (y, eta) *
      (OutgoingHistories.Ns w Amp (y, eta) /
        (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta))) := by
  have hL := CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half heta
  change 0 < 1 - 2 * d.h * eta ^ 2 at hL
  dsimp [OutgoingHistories.p1, OutgoingHistories.p2]
  field_simp [hL.ne', hQ.ne', (OutgoingHistories.E_pos w (y, eta)).ne']

/-- Finite radius threshold, given by `16 / (Real.exp d.core.endpoint * (d.core.lam / 4))`. -/
noncomputable def finiteRadiusThreshold (d : TailData) : ℝ :=
  16 / (Real.exp d.core.endpoint * (d.core.lam / 4))

theorem finiteRadiusThreshold_pos (d : TailData) : 0 < finiteRadiusThreshold d :=
  div_pos (by norm_num) (mul_pos (Real.exp_pos _) (div_pos d.core.lam_pos (by norm_num)))

theorem actualP1_finite_large {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) {XR eta y : ℝ} (hXR : finiteRadiusThreshold d < XR) (heta : eta ^ 2 ≤ 1)
    (hy : d.core.endpoint ≤ y) (hQ : d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (y, eta)) :
    16 < OutgoingHistories.p1 XR w Amp (y, eta) := by
  have hL := CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half heta
  have hL1 : CoordinateAlgebra.L d.h eta ≤ 1 := by
    dsimp [CoordinateAlgebra.L]
    nlinarith [mul_nonneg d.h_pos.le (sq_nonneg eta)]
  have hXR0 := (finiteRadiusThreshold_pos d).trans hXR
  have hscale : 16 < XR * (Real.exp d.core.endpoint * (d.core.lam / 4)) :=
    (div_lt_iff₀ (mul_pos (Real.exp_pos _) (div_pos d.core.lam_pos (by norm_num)))).mp hXR
  have hprod := mul_le_mul (Real.exp_le_exp.mpr hy) hQ
    (div_nonneg d.core.lam_pos.le (by norm_num : (0 : ℝ) ≤ 4)) (Real.exp_pos y).le
  have hp := mul_le_mul_of_nonneg_left hprod hXR0.le
  change 16 < XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta
  apply (lt_div_iff₀ hL).mpr
  nlinarith

theorem corrected_amplitude_energy_zero_germ {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients
      (CorrectedPulseAmplitude.amplitude d w.coefficients q) q = 0 := by
  have h := CorrectedPulseAmplitude.numerical_coefficient_bounds d w.coefficients eta
    (CorrectedPulseAmplitude.combinedScale d K) heta
    (CorrectedPulseAmplitude.old_error_bounds d K hK hsmall hwait eta heta)
    (CorrectedPulseAmplitude.energyShift_bounds w hK eta heta).1 hscale
  apply amplitude_energy_zero_germ w eta
  linarith [h.2.2.2.2]

theorem reset_scale_le_one {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hreset : resetSourceError d K ≤ d.core.lam / 4) : K * d.core.lam ^ (28 : ℕ) ≤ 1 := by
  have h0 := ResetEnergyBounds.coefficient_scale_nonneg w
  have hp := mul_nonneg resetJetConstant_pos.le h0
  dsimp [resetSourceError] at hreset
  nlinarith [d.core.lam_lt]

/-- Tail radius threshold, given by `max (finiteRadiusThreshold d) (releaseRadiusThreshold d)`. -/
noncomputable def tailRadiusThreshold (d : TailData) : ℝ :=
  max (finiteRadiusThreshold d) (releaseRadiusThreshold d)

theorem tailRadiusThreshold_pos (d : TailData) : 0 < tailRadiusThreshold d :=
  (finiteRadiusThreshold_pos d).trans_le (le_max_left _ _)

/-- All quantities are those of the corrected profile and its actual integral
histories. The scalar smallness conditions are arranged by the thresholds below. -/
theorem corrected_tail_cone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (hpulse : PulseCone.sourceConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 8)
    (hh1 : d.h ≤ 1 / 100) (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (hreset : resetSourceError d K ≤ d.core.lam / 4)
    (hfinite : finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) ≤ 1 / 2)
    (hrelease : releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2)
    {XR eta y : ℝ} (hXR : tailRadiusThreshold d < XR) (heta : |eta| ≤ 1)
    (hy : d.core.endpoint ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    0 < OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualBs w (CorrectedPulseAmplitude.amplitude d w.coefficients) y eta = 0 ∧
    2 < actualA w y eta ∧ actualA w y eta ≤ 4 ∧
    2 < OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualA w y eta < ConeAlgebra.coneBound
      (OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta))
      (OutgoingHistories.p2 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta)) :=
          by
  let Amp := CorrectedPulseAmplitude.amplitude d w.coefficients
  have ha : ContDiff ℝ ∞ Amp := CorrectedPulseAmplitude.amplitude_contDiff d w.smooth
  have heta2 : eta ^ 2 ≤ 1 := by have h := abs_le.mp heta; nlinarith
  have hz := corrected_amplitude_energy_zero_germ w hK hwait hsmall hscale eta heta2
  have hb := actualBs_zero w ha eta hy
  by_cases hyr : y < d.releaseStart
  · have hQ := corrected_flatten_Qs_lower w hK hwait hsmall hscale hpulse hh1 hhT hreset eta heta
      hy hyr.le
    have hQ0 : 0 < OutgoingHistories.Qs w Amp (y, eta) := by
      change 0 < OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y,
          eta)
      linarith [d.core.lam_pos]
    have har := correctedFlat_geometry w hreset eta y heta2
    have hAw := actualA_finite w eta hy hyr
    have hratio := (actual_finite_ratio_bound w ha hwait (reset_scale_le_one w hreset) eta heta hz
        hy hyr.le hQ).trans hfinite
    have hp := actualP1_finite_large w Amp ((le_max_left _ _).trans_lt hXR) heta2 hy hQ
    have hc := cone_of_zero_bs (a := actualA w y eta) (by rw [hAw]; exact har.1)
      (by rw [hAw]; exact har.2.1) hratio hp
    refine ⟨hQ0, hb, hc.2.1, ?_, hc.1, ?_⟩
    · rw [hAw]; exact har.2.1
    · rw [actualP2_eq w Amp XR eta y heta2 hQ0]
      exact hc.2.2
  · have hR : d.releaseStart ≤ y := le_of_not_gt hyr
    have hQ : 0 < OutgoingHistories.Qs w Amp (y, eta) := by
      rw [actualQs_eq_normalizedLag w ha eta hR]
      exact normalizedLag_pos w eta hR hy'
    have hratio : |OutgoingHistories.Ns w Amp (y, eta) /
        (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta))| ≤ 1 / 2 := by
      rw [actualRatio_eq_releaseVelocityRatio w ha eta hR hz]
      exact (releaseVelocityRatio_uniform w hwait heta hR hy').trans hrelease
    have hp : 16 < OutgoingHistories.p1 XR w Amp (y, eta) := by
      change 16 < XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h
          eta
      rw [actualQs_eq_normalizedLag w ha eta hR]
      exact releaseP1_large w ((le_max_right _ _).trans_lt hXR) heta2 hR hy'
    have har := releaseA_bounds d y
    have hAw := actualA_release w eta hR
    have hc := cone_of_zero_bs (a := actualA w y eta) (by rw [hAw]; exact har.1)
      (by rw [hAw]; exact har.2) hratio hp
    refine ⟨hQ, hb, hc.2.1, ?_, hc.1, ?_⟩
    · rw [hAw]; exact har.2
    · rw [actualP2_eq w Amp XR eta y heta2 hQ]
      exact hc.2.2

/-! ## Simultaneous parameter choice, uniform in the terminal parameter -/

theorem lambda_power_le_self (d : TailData) (n : ℕ) : d.core.lam ^ (n + 1) ≤ d.core.lam := by
  have hp := pow_le_one₀ d.core.lam_pos.le (show d.core.lam ≤ 1 by
      linarith [d.core.lam_lt]) (n := n)
  rw [pow_succ]
  nlinarith [d.core.lam_pos]

theorem exists_finite_cone_threshold (P m : ℝ) (hP : 0 < P) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.P = P → d.core.m = m →
      d.core.lam < lam0 → finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) < 1 / 2 := by
  have hC := finiteConeConstant_pos hP m
  refine ⟨(1 / 2) / finiteConeConstant P m, div_pos (by norm_num) hC, ?_⟩
  intro d hdP hdm hlam
  rw [hdP, hdm]
  have hpow : d.core.lam ^ (10 : ℕ) ≤ d.core.lam := lambda_power_le_self d 9
  have hsmall := (lt_div_iff₀ hC).mp hlam
  have hp := mul_le_mul_of_nonneg_left hpow hC.le
  nlinarith

theorem exists_reset_source_threshold (K : ℝ) (hK : 0 < K) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.lam < lam0 →
      resetSourceError d K ≤ d.core.lam / 4 := by
  let C : ℝ := (2 * resetJetConstant + 2) * K
  have hC : 0 < C := mul_pos (by linarith [resetJetConstant_pos]) hK
  refine ⟨(1 / 4) / C, div_pos (by norm_num) hC, ?_⟩
  intro d hlam
  have hpow : d.core.lam ^ (27 : ℕ) ≤ d.core.lam := lambda_power_le_self d 26
  have hc := (lt_div_iff₀ hC).mp hlam
  have hp := mul_le_mul_of_nonneg_left hpow hC.le
  have hb : C * d.core.lam ^ (27 : ℕ) ≤ 1 / 4 := by nlinarith
  calc
    resetSourceError d K = d.core.lam * (C * d.core.lam ^ (27 : ℕ)) := by
      dsimp [resetSourceError, C]; ring
    _ ≤ d.core.lam * (1 / 4) := mul_le_mul_of_nonneg_left hb d.core.lam_pos.le
    _ = _ := by ring

theorem exists_tail_smallness_threshold (P m K : ℝ) (hP : 0 < P) (hK : 0 < K) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.P = P → d.core.m = m → d.core.lam < lam0 →
      d.core.lam ≤ 1 / 120 ∧ CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000 ∧
      PulseCone.sourceConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 8 ∧
      d.h ≤ 1 / 100 ∧ d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8 ∧
      resetSourceError d K ≤ d.core.lam / 4 ∧
      finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) ≤ 1 / 2 ∧
      releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2 := by
  obtain ⟨rate, hrate, Hrate⟩ := PulseAmplitude.exists_rate_threshold
      (CorrectedPulseAmplitude.combinedConstant P m K)
  obtain ⟨finite, hfinite, Hfinite⟩ := exists_finite_cone_threshold P m hP
  obtain ⟨release, hrelease, Hrelease⟩ := exists_release_cone_threshold P m hP
  obtain ⟨reset, hreset, Hreset⟩ := exists_reset_source_threshold K hK
  let source : ℝ := (1 / 8) / PulseCone.sourceConstant P m
  let incoming : ℝ := Real.exp (-(Real.exp m + 12 + 3 / 5)) / 4
  have hsource : 0 < source := div_pos (by norm_num) (PulseCone.sourceConstant_pos hP m)
  have hincoming : 0 < incoming := div_pos (Real.exp_pos _) (by norm_num)
  refine ⟨min rate (min finite (min release (min reset (min source (min (1 / 120) incoming))))),
    lt_min hrate (lt_min hfinite (lt_min hrelease (lt_min hreset (lt_min hsource (lt_min (by
        norm_num) hincoming))))), ?_⟩
  intro d hdP hdm hlam
  rcases lt_min_iff.mp hlam with ⟨hlrate, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlfinite, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlrelease, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlreset, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlsource, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlnum, hlincoming⟩
  refine ⟨hlnum.le, ?_, ?_, ?_, ?_, Hreset d hlreset, (Hfinite d hdP hdm hlfinite).le,
    (Hrelease d hdP hdm hlrelease).le⟩
  · unfold CorrectedPulseAmplitude.combinedScale
    rw [hdP, hdm]
    exact Hrate _ d.core.lam_pos hlrate
  · rw [hdP, hdm]
    have hs : d.core.lam * PulseCone.sourceConstant P m < 1 / 8 :=
      (lt_div_iff₀ (PulseCone.sourceConstant_pos hP m)).mp hlsource
    have hp : d.core.lam ^ (29 : ℕ) ≤ d.core.lam := lambda_power_le_self d 28
    have hm := mul_le_mul_of_nonneg_left hp (PulseCone.sourceConstant_pos hP m).le
    nlinarith
  · linarith [d.h_small]
  · have hhold : d.core.holdStart = Real.exp m + 12 := by
      dsimp [OutgoingSchedule.Parameters.holdStart, OutgoingSchedule.Parameters.dropLength]
      rw [hdm]
      ring
    rw [hhold]
    dsimp [incoming] at hlincoming
    linarith [d.h_small]

/-- The post-pulse pointwise cone for the exact corrected schedule. -/
noncomputable def PostPulseCone {d : TailData} {K : ℝ} (w : ResetWitness d K) (XR : ℝ) : Prop :=
  ∀ eta : ℝ, |eta| ≤ 1 → ∀ y : ℝ, d.core.endpoint ≤ y → y ≤ tailStart d + 1 / 2 →
    0 < OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualBs w (CorrectedPulseAmplitude.amplitude d w.coefficients) y eta = 0 ∧
    2 < actualA w y eta ∧ actualA w y eta ≤ 4 ∧
    2 < OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualA w y eta < ConeAlgebra.coneBound
      (OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta))
      (OutgoingHistories.p2 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta))

/-- A common positive `lam` threshold works for every `0 < 2*h < lam`.
The entrance radius is chosen only after the full schedule, including `h`.
No energy, pressure, angular-lag, or cone inequality is assumed as input. -/
theorem exists_scheduled_tail_cone (P m : ℝ) (hP : 0 < P) :
    ∃ lam0 K : ℝ, 0 < lam0 ∧ 0 < K ∧ ∀ d : TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam0 → ∃ w : ResetWitness d K,
        ContDiff ℝ ∞ (CorrectedPulseAmplitude.amplitude d w.coefficients) ∧
        (∀ eta : ℝ, eta ^ 2 ≤ 1 → CorrectedPulseAmplitude.totalEnergy d w.coefficients
          (CorrectedPulseAmplitude.amplitude d w.coefficients eta) eta = 0) ∧
        ∃ R0 : ℝ, 0 < R0 ∧ ∀ XR : ℝ, R0 < XR → PostPulseCone w XR := by
  obtain ⟨resetLam, K, hresetLam, hK, Hreset⟩ := exists_scheduled_reset
  obtain ⟨smallLam, hsmallLam, Hsmall⟩ := exists_tail_smallness_threshold P m K hP hK
  refine ⟨min resetLam smallLam, K, lt_min hresetLam hsmallLam, hK, ?_⟩
  intro d hdP hdm hwait hlam
  have hr := lt_of_lt_of_le hlam (min_le_left _ _)
  have hs := lt_of_lt_of_le hlam (min_le_right _ _)
  obtain ⟨w⟩ := Hreset d hr
  obtain ⟨hsmall, hscale, hpulse, hh1, hhT, hreset, hfinite, hrelease⟩ := Hsmall d hdP hdm hs
  have ha := CorrectedPulseAmplitude.amplitude_spec w hK hsmall hwait hscale
  refine ⟨w, ha.1, ?_, tailRadiusThreshold d, tailRadiusThreshold_pos d, ?_⟩
  · intro eta heta
    exact (ha.2 eta heta).2.2.1
  · intro XR hXR eta heta y hy hy'
    exact corrected_tail_cone w hK hwait hsmall hscale hpulse hh1 hhT hreset hfinite hrelease hXR
        heta hy hy'

end NavierStokes.TailCone
