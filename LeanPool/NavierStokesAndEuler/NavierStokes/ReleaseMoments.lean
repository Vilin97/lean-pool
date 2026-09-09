/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformAngularReset
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual angular history through the release and terminal tail

The corrected angular field has the exact initial moment required by the
release controller. Matching derivatives and initial values identifies its
actual integral with each constructed lag solution. The terminal identity
then gives the vanishing renormalized angular moment.
-/

@[expose] public section


noncomputable section

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

namespace NavierStokes.ReleaseMoments

/-- Corrected weight, given by `Real.exp (3 * y / 2) * correctedAngular d c (y, eta)`. -/
noncomputable def correctedWeight (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) : ℝ :=
  Real.exp (3 * y / 2) * correctedAngular d c (y, eta)

/-- History, given by `(5 / 8) * d.core.P * shape eta + primitive (correctedWeight d c eta) y`. -/
noncomputable def history (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) : ℝ :=
  (5 / 8) * d.core.P * shape eta + primitive (correctedWeight d c eta) y

/-- Release weight, given by `Real.exp (3 * y / 2) * finalAngular d (y, 0)`. -/
noncomputable def releaseWeight (d : TailData) (y : ℝ) : ℝ :=
  Real.exp (3 * y / 2) * finalAngular d (y, 0)

theorem releaseWeight_contDiff (d : TailData) : ContDiff ℝ ∞ (releaseWeight d) :=
  ((contDiff_const.mul contDiff_id).div_const 2).exp.mul
    ((finalAngular_contDiff d).comp (contDiff_id.prodMk contDiff_const))

theorem releaseWeight_pos (d : TailData) (y : ℝ) : 0 < releaseWeight d y :=
  mul_pos (Real.exp_pos _) (finalAngular_pos d _)

theorem correctedWeight_contDiff (d : TailData) (c : ℝ → Coeff)
    (hc : ContDiff ℝ ∞ c) (eta : ℝ) : ContDiff ℝ ∞ (correctedWeight d c eta) :=
  ((contDiff_const.mul contDiff_id).div_const 2).exp.mul
    ((correctedAngular_contDiff d c hc).comp (contDiff_id.prodMk contDiff_const))

theorem corrected_eq_release (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) : correctedAngular d c (y, eta) = finalAngular d (y, 0) := by
  have hout : y ∉ Ioo (d.releaseStart - 4) d.releaseStart := by
    intro h
    exact (not_lt_of_ge hy) h.2
  rw [correctedAngular_unchanged d c eta hout]
  exact finalAngular_eta_independent d eta 0 ((releaseStart_gt_flattenEnd d).le.trans hy)

theorem correctedWeight_eq_release (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) : correctedWeight d c eta y = releaseWeight d y := by
  unfold correctedWeight releaseWeight
  rw [corrected_eq_release d c eta hy]

theorem correctedWeight_ideal (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : y ≤ 0) : correctedWeight d c eta y =
      (d.core.P * shape eta) * Real.exp ((8 / 5 : ℝ) * y) := by
  have hout : y ∉ Ioo (d.releaseStart - 4) d.releaseStart := by
    intro hw
    linarith [flattenEnd_pos d, last_four_after_flatten d, hw.1]
  unfold correctedWeight
  rw [correctedAngular_unchanged d c eta hout]
  exact full_weight_ideal d eta hy

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)

theorem history_contDiff_y (eta : ℝ) : ContDiff ℝ ∞ (history d w.coefficients eta) :=
  contDiff_const.add (primitive_contDiff (correctedWeight_contDiff d w.coefficients w.smooth eta))

theorem history_hasDerivAt (eta y : ℝ) :
    HasDerivAt (history d w.coefficients eta) (correctedWeight d w.coefficients eta y) y :=
  (primitive_hasDerivAt (correctedWeight_contDiff d w.coefficients w.smooth eta).continuous
      y).const_add _

theorem history_integrable (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (correctedWeight d w.coefficients eta) (Iic y) :=
  (history_from_ideal_prefix d eta _
    (correctedWeight_contDiff d w.coefficients w.smooth eta).continuous
    (fun _ ht => correctedWeight_ideal d w.coefficients eta ht) hy).1

theorem history_eq_integral (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    history d w.coefficients eta y = ∫ t in Iic y, correctedWeight d w.coefficients eta t :=
  (history_from_ideal_prefix d eta _
    (correctedWeight_contDiff d w.coefficients w.smooth eta).continuous
    (fun _ ht => correctedWeight_ideal d w.coefficients eta ht) hy).2.symm

theorem history_at_release (eta : ℝ) :
    history d w.coefficients eta d.releaseStart = releaseWeight d d.releaseStart / (1 - d.core.lam)
        := by
  change correctedHistory d w.coefficients eta = _
  rw [w.exact_endpoint eta]
  unfold releaseWeight baseWeight
  rw [finalAngular_uniform_wait d 0 (releaseStart_gt_flattenEnd d).le le_rfl]
  field_simp [show 1 - d.core.lam ≠ 0 by linarith [d.core.lam_lt]]

theorem history_hasDerivAt_release (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    HasDerivAt (history d w.coefficients eta) (releaseWeight d y) y := by
  rw [← correctedWeight_eq_release d w.coefficients eta hy]
  exact history_hasDerivAt w eta y

theorem history_eta_independent (eta eta' : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    history d w.coefficients eta y = history d w.coefficients eta' y := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ ht => history_hasDerivAt_release w eta ((uIcc_of_le hy ▸ ht).1))
    ((releaseWeight_contDiff d).continuous.intervalIntegrable d.releaseStart y)
  have hi' := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ ht => history_hasDerivAt_release w eta' ((uIcc_of_le hy ▸ ht).1))
    ((releaseWeight_contDiff d).continuous.intervalIntegrable d.releaseStart y)
  rw [history_at_release w eta] at hi
  rw [history_at_release w eta'] at hi'
  linarith

theorem history_contDiff_eta {y : ℝ} (hy : d.releaseStart ≤ y) :
    ContDiff ℝ ∞ (fun eta => history d w.coefficients eta y) := by
  have he : (fun eta => history d w.coefficients eta y) =
      fun _ : ℝ => history d w.coefficients 0 y :=
    funext (fun eta => history_eta_independent w eta 0 hy)
  rw [he]
  exact contDiff_const

theorem history_deriv_eta_zero {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    deriv (fun p => history d w.coefficients p y) eta = 0 := by
  have he : (fun p => history d w.coefficients p y) =
      fun _ : ℝ => history d w.coefficients 0 y :=
    funext (fun p => history_eta_independent w p 0 hy)
  rw [he, deriv_const]

end ResetWitness

theorem releaseWeight_hasDerivAt (d : TailData) {y : ℝ} (hy : d.releaseStart ≤ y) :
    HasDerivAt (releaseWeight d) (releaseWeight d y * (1 + profileSlope d y)) y := by
  have he := (((hasDerivAt_id y).const_mul 3).div_const 2).exp
  have hp := he.mul (finalAngular_hasDerivAt_on_release d 0 hy)
  convert! hp using 1
  dsimp [releaseWeight]
  ring

/-- Moment candidate, given by `(1 + q y) * releaseWeight d y / (1 - d.h)`. -/
noncomputable def momentCandidate (d : TailData) (q : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 + q y) * releaseWeight d y / (1 - d.h)

/-- The lag equation turns the candidate into a primitive of the actual
release weight. This is the uniqueness mechanism used below. -/
theorem momentCandidate_hasDerivAt (d : TailData) (q : ℝ → ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hq : HasDerivAt q (-profileSlope d y - d.h - (1 + profileSlope d y) * q y) y) :
    HasDerivAt (momentCandidate d q) (releaseWeight d y) y := by
  have hp := ((hq.const_add 1).mul (releaseWeight_hasDerivAt d hy)).div_const (1 - d.h)
  convert! hp using 1
  field_simp [d.one_sub_h_pos.ne']; ring

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)

theorem history_eq_candidate (eta : ℝ) (q : ℝ → ℝ) {a y : ℝ}
    (ha : d.releaseStart ≤ a) (hay : a ≤ y)
    (hq : ∀ t ∈ Icc a y,
      HasDerivAt q (-profileSlope d t - d.h - (1 + profileSlope d t) * q t) t)
    (hinit : history d w.coefficients eta a = momentCandidate d q a) :
    history d w.coefficients eta y = momentCandidate d q y := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ ht => history_hasDerivAt_release w eta (ha.trans (uIcc_of_le hay ▸ ht).1))
    ((releaseWeight_contDiff d).continuous.intervalIntegrable a y)
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => momentCandidate_hasDerivAt d q (ha.trans (uIcc_of_le hay ▸ ht).1)
      (hq t (uIcc_of_le hay ▸ ht)))
    ((releaseWeight_contDiff d).continuous.intervalIntegrable a y)
  rw [hinit] at hi
  linarith

end ResetWitness

theorem tailShapeDeriv_zero_early (d : TailData) {t : ℝ} (ht : t ≤ 0) :
    tailShapeDeriv d t = 0 := by
  unfold tailShapeDeriv
  rw [sigma_derivative_zero_left (by linarith : (t - 1) / 2 < 0), mul_zero]

theorem tailShapeDeriv_zero_late (d : TailData) {t : ℝ} (ht : 3 ≤ t) :
    tailShapeDeriv d t = 0 := by
  have hm : IsLocalMax (tailShape d) t := by
    filter_upwards [] with u
    rw [tailShape_late d ht]
    exact (tailShape_bounds d u).2
  exact hm.hasDerivAt_eq_zero (tailShape_hasDerivAt d t)

theorem profileSlope_before_tail (d : TailData) {y : ℝ} (hy : y ≤ tailStart d) :
    profileSlope d y = releaseSlope d (y - d.releaseStart) := by
  simp [profileSlope, tailShapeDeriv_zero_early d (by linarith : y - tailStart d ≤ 0)]

theorem releaseLag_hasDerivAt (d : TailData) (t : ℝ) :
    HasDerivAt (releaseLag d)
      (-releaseSlope d t - d.h - (1 + releaseSlope d t) * releaseLag d t) t :=
  linearLag_hasDerivAt (releaseRate_contDiff d).continuous
    (releaseSource_contDiff d).continuous (initialLag d) t

theorem shifted_releaseLag_hasDerivAt (d : TailData) {y : ℝ} (hy : y ≤ tailStart d) :
    HasDerivAt (fun t => releaseLag d (t - d.releaseStart))
      (-profileSlope d y - d.h - (1 + profileSlope d y) * releaseLag d (y - d.releaseStart)) y := by
  have hd := (releaseLag_hasDerivAt d (y - d.releaseStart)).comp y
    ((hasDerivAt_id y).sub_const d.releaseStart)
  simpa only [profileSlope_before_tail d hy, Function.comp_def, id_eq, mul_one] using hd

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)

theorem history_release (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) (hy' : y ≤ d.releaseStart + d.rampEnd) :
    history d w.coefficients eta y =
      momentCandidate d (fun t => releaseLag d (t - d.releaseStart)) y := by
  apply history_eq_candidate w eta _ le_rfl hy
  · intro t ht
    apply shifted_releaseLag_hasDerivAt
    dsimp [tailStart]
    linarith [ht.2, decayHold_pos d]
  · rw [history_at_release w eta]
    unfold momentCandidate
    dsimp only
    rw [sub_self, releaseLag_initial]
    unfold initialLag
    field_simp [d.one_sub_h_pos.ne', show 1 - d.core.lam ≠ 0 by linarith [d.core.lam_lt]]; ring

theorem history_hold (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart + d.rampEnd ≤ y) (hy' : y ≤ tailStart d) :
    history d w.coefficients eta y =
      momentCandidate d (fun t => holdLag d (t - (d.releaseStart + d.rampEnd))) y := by
  apply history_eq_candidate w eta _ (by linarith [d.rampEnd_pos]) hy
  · intro t ht
    have hp : profileSlope d t = -d.h := by
      rw [profileSlope_before_tail d (ht.2.trans hy')]
      exact releaseSlope_late d (by linarith [ht.1])
    have hh := (holdLag_hasDerivAt d (t - (d.releaseStart + d.rampEnd))).comp t
      ((hasDerivAt_id t).sub_const (d.releaseStart + d.rampEnd))
    convert! hh using 1
    rw [hp]
    ring
  · rw [history_release w eta (by linarith [d.rampEnd_pos]) le_rfl]
    unfold momentCandidate
    dsimp only
    rw [sub_self, (holdLag_matches d).1]
    congr 2
    congr 1
    ring_nf

theorem history_tail (eta : ℝ) {y : ℝ} (hy : tailStart d ≤ y) :
    history d w.coefficients eta y =
      momentCandidate d (fun t => tailLag d (t - tailStart d)) y := by
  apply history_eq_candidate w eta _ (tailStart_gt_release d).le hy
  · intro t ht
    have hh := (tailLag_hasDerivAt d (t - tailStart d)).comp t
      ((hasDerivAt_id t).sub_const (tailStart d))
    convert! hh using 1
    rw [profileSlope_tail d ht.1]
    unfold tailRate tailLogSlope
    ring
  · rw [history_hold w eta (by dsimp [tailStart]; linarith [decayHold_pos d]) le_rfl]
    unfold momentCandidate
    dsimp only
    have he : tailStart d - (d.releaseStart + d.rampEnd) = decayHold d := by
      dsimp [tailStart]
      ring
    rw [he, sub_self, (holdLag_matches d).2]

end ResetWitness

theorem tailLag_zero_late (d : TailData) {t : ℝ} (ht : 3 ≤ t) : tailLag d t = 0 := by
  have hp := primitive_increment (g := weightedTailDerivative d)
    (weightedTailDerivative_contDiff d).continuous 3 t 0 (by
      intro u hu
      simp [weightedTailDerivative, tailShapeDeriv_zero_late d ((uIcc_of_le ht ▸ hu).1)])
  have he : primitive (weightedTailDerivative d) t = primitive (weightedTailDerivative d) 3 := by
    simpa only [mul_zero, add_zero] using hp
  simp [tailLag, tailNumerator, he]

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)

theorem history_eventual_power (eta : ℝ) {y : ℝ} (hy : tailEnd d ≤ y) :
    history d w.coefficients eta y = releaseWeight d y / (1 - d.h) := by
  have ht : tailStart d ≤ y := by dsimp [tailEnd] at hy; linarith
  rw [history_tail w eta ht]
  simp [momentCandidate, tailLag_zero_late d (by
      dsimp [tailEnd] at hy; linarith : 3 ≤ y - tailStart d)]

end ResetWitness

/-- Normalized lag, given by `(1 - d.h) * history d c eta y / releaseWeight d y - 1`. -/
noncomputable def normalizedLag (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) : ℝ :=
  (1 - d.h) * history d c eta y / releaseWeight d y - 1

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)

theorem normalizedLag_hasDerivAt (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    HasDerivAt (normalizedLag d w.coefficients eta)
      (-profileSlope d y - d.h - (1 + profileSlope d y) * normalizedLag d w.coefficients eta y) y
          := by
  have hp := (((history_hasDerivAt_release w eta hy).const_mul (1 - d.h)).div
    (releaseWeight_hasDerivAt d hy) (releaseWeight_pos d y).ne').sub_const 1
  convert! hp using 1
  unfold normalizedLag
  field_simp [(releaseWeight_pos d y).ne']; ring

theorem normalizedLag_eq_of_history (eta : ℝ) (q : ℝ → ℝ) (y : ℝ)
    (heq : history d w.coefficients eta y = momentCandidate d q y) :
    normalizedLag d w.coefficients eta y = q y := by
  unfold normalizedLag
  rw [heq]
  unfold momentCandidate
  field_simp [(releaseWeight_pos d y).ne', d.one_sub_h_pos.ne']; ring

theorem normalizedLag_release (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) (hy' : y ≤ d.releaseStart + d.rampEnd) :
    normalizedLag d w.coefficients eta y = releaseLag d (y - d.releaseStart) :=
  normalizedLag_eq_of_history w eta _ y (history_release w eta hy hy')

theorem normalizedLag_hold (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart + d.rampEnd ≤ y) (hy' : y ≤ tailStart d) :
    normalizedLag d w.coefficients eta y = holdLag d (y - (d.releaseStart + d.rampEnd)) :=
  normalizedLag_eq_of_history w eta _ y (history_hold w eta hy hy')

theorem normalizedLag_tail (eta : ℝ) {y : ℝ} (hy : tailStart d ≤ y) :
    normalizedLag d w.coefficients eta y = tailLag d (y - tailStart d) :=
  normalizedLag_eq_of_history w eta _ y (history_tail w eta hy)

theorem normalizedLag_initial (eta : ℝ) :
    normalizedLag d w.coefficients eta d.releaseStart = initialLag d := by
  rw [normalizedLag_release w eta le_rfl (by linarith [d.rampEnd_pos]),
    sub_self, releaseLag_initial]

theorem normalizedLag_eventual_zero (eta : ℝ) {y : ℝ} (hy : tailEnd d ≤ y) :
    normalizedLag d w.coefficients eta y = 0 := by
  have ht : tailStart d ≤ y := by dsimp [tailEnd] at hy; linarith
  rw [normalizedLag_tail w eta ht]
  exact tailLag_zero_late d (by dsimp [tailEnd] at hy; linarith)

end ResetWitness

/-- Power weight, given by `powerConstant d * Real.exp ((1 - d.h) * y)`. -/
noncomputable def powerWeight (d : TailData) (y : ℝ) : ℝ :=
  powerConstant d * Real.exp ((1 - d.h) * y)

theorem weighted_power (d : TailData) (y : ℝ) :
    Real.exp (3 * y / 2) * (powerConstant d * Real.exp (-(1 / 2 + d.h) * y)) = powerWeight d y := by
  rw [mul_left_comm, ← Real.exp_add]
  unfold powerWeight
  congr 2
  ring

theorem correctedWeight_eq_power (d : TailData) (c : ℝ → Coeff) (eta : ℝ)
    {y : ℝ} (hy : tailEnd d ≤ y) : correctedWeight d c eta y = powerWeight d y := by
  have hR : d.releaseStart ≤ y := by
    have ht := tailStart_gt_release d
    dsimp [tailEnd] at hy
    linarith
  rw [correctedWeight_eq_release d c eta hR]
  unfold releaseWeight
  rw [finalAngular_eventual_power d 0 hy]
  exact weighted_power d y

theorem releaseWeight_eq_power (d : TailData) {y : ℝ} (hy : tailEnd d ≤ y) :
    releaseWeight d y = powerWeight d y := by
  unfold releaseWeight
  rw [finalAngular_eventual_power d 0 hy]
  exact weighted_power d y

theorem tailEnd_pos (d : TailData) : 0 < tailEnd d := by
  have hR : 0 < d.releaseStart := (flattenEnd_pos d).trans (releaseStart_gt_flattenEnd d)
  have ht := tailStart_gt_release d
  dsimp [tailEnd]
  linarith

theorem powerWeight_integrable (d : TailData) (y : ℝ) : IntegrableOn (powerWeight d) (Iic y) :=
  (integrableOn_exp_mul_Iic d.one_sub_h_pos y).const_mul (powerConstant d)

theorem powerWeight_integral (d : TailData) (y : ℝ) :
    (∫ t in Iic y, powerWeight d t) = powerWeight d y / (1 - d.h) := by
  unfold powerWeight
  rw [integral_const_mul, integral_exp_mul_Iic d.one_sub_h_pos]
  ring

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)

theorem renormalized_log_integrable (eta : ℝ) :
    Integrable (fun y => correctedWeight d w.coefficients eta y - powerWeight d y) := by
  have hi : IntegrableOn (fun y => correctedWeight d w.coefficients eta y - powerWeight d y)
      (Iic (tailEnd d)) :=
    (history_integrable w eta (tailEnd_pos d).le).sub (powerWeight_integrable d _)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro y hy
  rw [correctedWeight_eq_power d w.coefficients eta (le_of_lt (not_le.mp hy)), sub_self]

theorem renormalized_log_integral (eta : ℝ) :
    (∫ y, correctedWeight d w.coefficients eta y - powerWeight d y) = 0 := by
  have hrestrict : (∫ y in Iic (tailEnd d), correctedWeight d w.coefficients eta y - powerWeight d
      y) =
      ∫ y, correctedWeight d w.coefficients eta y - powerWeight d y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [correctedWeight_eq_power d w.coefficients eta (le_of_lt (not_le.mp hy)), sub_self]
  rw [← hrestrict, integral_sub (history_integrable w eta (tailEnd_pos d).le)
      (powerWeight_integrable d _),
    ← history_eq_integral w eta (tailEnd_pos d).le, history_eventual_power w eta le_rfl,
    releaseWeight_eq_power d le_rfl, powerWeight_integral, sub_self]

end ResetWitness

/-- Radial H, given by `Real.sqrt (2 * X) * correctedAngular d c (Real.log X, eta)`. -/
noncomputable def radialH (d : TailData) (c : ℝ → Coeff) (eta X : ℝ) : ℝ :=
  Real.sqrt (2 * X) * correctedAngular d c (Real.log X, eta)

/-- Radial power H, given by `Real.sqrt (2 * X) * (powerConstant d * X ^ (-(1 / 2 + d.h)))`. -/
noncomputable def radialPowerH (d : TailData) (X : ℝ) : ℝ :=
  Real.sqrt (2 * X) * (powerConstant d * X ^ (-(1 / 2 + d.h)))

theorem exponential_radial_weight (y : ℝ) :
    Real.exp y * Real.sqrt (2 * Real.exp y) = Real.sqrt 2 * Real.exp (3 * y / 2) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), AngularMomentReset.sqrt_exp_half]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem radialH_comp_exp (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) :
    |Real.exp y| • radialH d c eta (Real.exp y) = Real.sqrt 2 * correctedWeight d c eta y := by
  rw [abs_of_pos (Real.exp_pos y), smul_eq_mul]
  unfold radialH correctedWeight
  rw [Real.log_exp, ← mul_assoc, exponential_radial_weight]
  ring

theorem radialPowerH_comp_exp (d : TailData) (y : ℝ) :
    |Real.exp y| • radialPowerH d (Real.exp y) = Real.sqrt 2 * powerWeight d y := by
  rw [abs_of_pos (Real.exp_pos y), smul_eq_mul]
  unfold radialPowerH
  rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp, ← mul_assoc, exponential_radial_weight]
  have he : Real.exp (y * (-(1 / 2 + d.h))) = Real.exp (-(1 / 2 + d.h) * y) := by congr 1; ring
  rw [he, mul_assoc, weighted_power]

theorem radial_difference_comp_exp (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) :
    |Real.exp y| • (radialH d c eta (Real.exp y) - radialPowerH d (Real.exp y)) =
      Real.sqrt 2 * (correctedWeight d c eta y - powerWeight d y) := by
  rw [smul_sub, radialH_comp_exp, radialPowerH_comp_exp, mul_sub]

theorem image_exp_Iic (y : ℝ) : Real.exp '' Iic y = Ioc 0 (Real.exp y) := by
  ext X
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.exp_pos t, Real.exp_le_exp.mpr ht⟩
  · intro hX
    refine ⟨Real.log X, ?_, Real.exp_log hX.1⟩
    exact Real.exp_le_exp.mp (by rw [Real.exp_log hX.1]; exact hX.2)

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)

theorem radial_history_integrable (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (radialH d w.coefficients eta) (Ioc 0 (Real.exp y)) := by
  rw [← image_exp_Iic]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iic
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn _).mpr
  simp_rw [radialH_comp_exp]
  exact (history_integrable w eta hy).const_mul (Real.sqrt 2)

theorem radial_history_eq (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (∫ X in Ioc 0 (Real.exp y), radialH d w.coefficients eta X) =
      Real.sqrt 2 * history d w.coefficients eta y := by
  rw [← image_exp_Iic,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [radialH_comp_exp]
  rw [integral_const_mul, ← history_eq_integral w eta hy]

theorem radial_history_eta_independent (eta eta' : ℝ) {X : ℝ} (hX : 0 < X)
    (hrel : d.releaseStart ≤ Real.log X) :
    (∫ u in Ioc 0 X, radialH d w.coefficients eta u) =
      ∫ u in Ioc 0 X, radialH d w.coefficients eta' u := by
  have hy0 : 0 ≤ Real.log X :=
    (flattenEnd_pos d).le.trans ((releaseStart_gt_flattenEnd d).le.trans hrel)
  have hi := radial_history_eq w eta hy0
  have hi' := radial_history_eq w eta' hy0
  rw [Real.exp_log hX] at hi hi'
  rw [hi, hi', history_eta_independent w eta eta' hrel]

theorem radial_history_contDiff_eta {X : ℝ} (hX : 0 < X)
    (hrel : d.releaseStart ≤ Real.log X) :
    ContDiff ℝ ∞ (fun eta => ∫ u in Ioc 0 X, radialH d w.coefficients eta u) := by
  have he : (fun eta => ∫ u in Ioc 0 X, radialH d w.coefficients eta u) =
      fun _ : ℝ => ∫ u in Ioc 0 X, radialH d w.coefficients 0 u :=
    funext (fun eta => radial_history_eta_independent w eta 0 hX hrel)
  rw [he]
  exact contDiff_const

/-- The eventual physical history, in the manuscript's `X` coordinate. -/
theorem radial_history_eventual (eta : ℝ) {X : ℝ} (hX : 0 < X)
    (hfar : tailEnd d ≤ Real.log X) :
    (∫ u in Ioc 0 X, radialH d w.coefficients eta u) = X * radialH d w.coefficients eta X / (1 -
        d.h) := by
  have hy0 : 0 ≤ Real.log X := (tailEnd_pos d).le.trans hfar
  have hyR : d.releaseStart ≤ Real.log X := by
    have ht := tailStart_gt_release d
    dsimp [tailEnd] at hfar
    linarith
  have hr := radial_history_eq w eta hy0
  rw [Real.exp_log hX, history_eventual_power w eta hfar] at hr
  rw [hr]
  have hW := radialH_comp_exp d w.coefficients eta (Real.log X)
  rw [Real.exp_log hX, abs_of_pos hX, smul_eq_mul,
    correctedWeight_eq_release d w.coefficients eta hyR] at hW
  rw [hW]
  ring

theorem renormalized_radial_integrable (eta : ℝ) :
    IntegrableOn (fun X => radialH d w.coefficients eta X - radialPowerH d X) (Ioi 0) := by
  rw [← Real.range_exp, ← image_univ]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn _).mpr
  simp_rw [radial_difference_comp_exp]
  exact ((renormalized_log_integrable w eta).const_mul (Real.sqrt 2)).integrableOn

/-- The exact renormalized angular moment (12), for the actual corrected field
and the actual eventual power coefficient. -/
theorem renormalized_angular_moment (eta : ℝ) :
    (∫ X in Ioi 0, radialH d w.coefficients eta X - radialPowerH d X) = 0 := by
  rw [← Real.range_exp, ← image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [radial_difference_comp_exp]
  rw [setIntegral_univ, integral_const_mul, renormalized_log_integral w eta, mul_zero]

end ResetWitness

/-- The actual scheduled correction has the exact renormalized angular
moment and eventual physical history for a common small-`lam` threshold. -/
theorem complete_release_moments :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.lam < lam0 →
      ∃ c : ℝ → Coeff, ContDiff ℝ ∞ (correctedAngular d c) ∧
        ∀ eta : ℝ,
          IntegrableOn (fun X => radialH d c eta X - radialPowerH d X) (Ioi 0) ∧
          (∫ X in Ioi 0, radialH d c eta X - radialPowerH d X) = 0 ∧
          ∀ X : ℝ, 0 < X → tailEnd d ≤ Real.log X →
            (∫ u in Ioc 0 X, radialH d c eta u) = X * radialH d c eta X / (1 - d.h) := by
  obtain ⟨lam0, K, hlam0, _, hreset⟩ := exists_scheduled_reset
  refine ⟨lam0, hlam0, ?_⟩
  intro d hd
  obtain ⟨w⟩ := hreset d hd
  exact ⟨w.coefficients, correctedAngular_contDiff d w.coefficients w.smooth,
    fun eta => ⟨ResetWitness.renormalized_radial_integrable w eta,
      ResetWitness.renormalized_angular_moment w eta,
      fun _ hX hfar => ResetWitness.radial_history_eventual w eta hX hfar⟩⟩

end NavierStokes.ReleaseMoments
