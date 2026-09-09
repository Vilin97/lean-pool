/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingTail
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

@[expose] public section

/-!
# Energy of the constructed outgoing tail

The integrands in this file are the actual `OutgoingTail.finalAngular`.
The long release plateau is retained in the estimates; bounding the release
only by its terminal slope would give an incorrect uniformity claim in `h`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

namespace NavierStokes.TailEnergyBounds

noncomputable def energyDensity (d : TailData) (eta y : ℝ) : ℝ :=
  Real.exp y * finalAngular d (y, eta) ^ 2

theorem energyDensity_pos (d : TailData) (eta y : ℝ) :
    0 < energyDensity d eta y :=
  mul_pos (Real.exp_pos _) (sq_pos_of_pos (finalAngular_pos d _))

theorem energyDensity_continuous (d : TailData) (eta : ℝ) :
    Continuous (energyDensity d eta) :=
  Real.continuous_exp.mul
    (((finalAngular_contDiff d).continuous.comp
      (continuous_id.prodMk continuous_const)).pow 2)

noncomputable def releasePrimitive (d : TailData) : ℝ → ℝ :=
  primitive (releaseSlope d)

theorem releaseAdjustment_eq (d : TailData) (t : ℝ) :
    releaseAdjustment d t = releasePrimitive d t + d.core.lam * t := by
  unfold releaseAdjustment releasePrimitive primitive
  rw [intervalIntegral.integral_add
    ((releaseSlope_contDiff d).continuous.intervalIntegrable 0 t)
    (continuous_const.intervalIntegrable 0 t)]
  simp [mul_comm]

theorem primitive_increment_le {g : ℝ → ℝ} (hg : Continuous g)
    {a b c : ℝ} (hab : a ≤ b) (hc : ∀ t ∈ Icc a b, g t ≤ c) :
    primitive g b ≤ primitive g a + (b - a) * c := by
  have hi : (∫ t in a..b, g t) ≤ ∫ _t in a..b, c := intervalIntegral.integral_mono_on hab
    (hg.intervalIntegrable a b) (continuous_const.intervalIntegrable a b) hc
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 a) (hg.intervalIntegrable a b)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  unfold primitive
  linarith

theorem releasePrimitive_increment_le (d : TailData) {a b : ℝ} (hab : a ≤ b) :
    releasePrimitive d b ≤ releasePrimitive d a - d.h * (b - a) := by
  have h := primitive_increment_le (releaseSlope_contDiff d).continuous hab
    (c := -d.h) (fun t _ => (releaseSlope_bounds d t).2)
  change primitive (releaseSlope d) b ≤ primitive (releaseSlope d) a - d.h * (b - a)
  linarith

@[simp] theorem releasePrimitive_zero (d : TailData) : releasePrimitive d 0 = 0 := by
  simp [releasePrimitive, primitive]

theorem releasePrimitive_nonpos (d : TailData) {t : ℝ} (ht : 0 ≤ t) :
    releasePrimitive d t ≤ 0 := by
  have h := releasePrimitive_increment_le d ht
  simp only [releasePrimitive_zero, sub_zero, zero_sub] at h
  exact h.trans (neg_nonpos.mpr (mul_nonneg d.h_pos.le ht))

theorem releasePrimitive_plateau_le (d : TailData) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ d.secondRampStart) :
    releasePrimitive d t ≤ 1 - t := by
  by_cases h1 : t ≤ 1
  · exact (releasePrimitive_nonpos d ht).trans (sub_nonneg.mpr h1)
  · have h1' : 1 ≤ t := le_of_not_ge h1
    have hinc := primitive_increment (releaseSlope_contDiff d).continuous 1 t (-1)
      (fun v hv => releaseSlope_plateau d (uIcc_of_le h1' ▸ hv).1
        ((uIcc_of_le h1' ▸ hv).2.trans ht'))
    change releasePrimitive d t = releasePrimitive d 1 + (t - 1) * (-1) at hinc
    linarith [releasePrimitive_nonpos d (by norm_num : (0 : ℝ) ≤ 1)]

theorem releasePrimitive_late_le (d : TailData) {t : ℝ}
    (ht : d.secondRampStart ≤ t) :
    releasePrimitive d t ≤ -d.longHold - d.h * (t - d.secondRampStart) := by
  have hb : 0 ≤ d.secondRampStart := by
    dsimp [TailData.secondRampStart]
    linarith [d.longHold_pos]
  have hp := releasePrimitive_plateau_le d hb le_rfl
  have hi := releasePrimitive_increment_le d ht
  have hb' : 1 - d.secondRampStart = -d.longHold := by
    dsimp [TailData.secondRampStart]
    ring
  rw [hb'] at hp
  linarith

theorem plateau_suppression (d : TailData) :
    Real.exp (-2 * d.longHold) = d.h ^ 8 := by
  have he : Real.exp (Real.log d.h) = d.h := Real.exp_log d.h_pos
  calc
    Real.exp (-2 * d.longHold) = Real.exp (8 * Real.log d.h) := by
      congr 1
      simp only [TailData.longHold, one_div, Real.log_inv]
      ring
    _ = (Real.exp (Real.log d.h)) ^ 8 := by
      simpa using Real.exp_nat_mul (Real.log d.h) 8
    _ = _ := by rw [he]

theorem h_secondRampStart_le (d : TailData) : d.h * d.secondRampStart ≤ 4 := by
  have hi := Real.log_le_sub_one_of_pos (one_div_pos.mpr d.h_pos)
  have hi' := mul_le_mul_of_nonneg_left hi d.h_pos.le
  have hn : d.h ≠ 0 := d.h_pos.ne'
  have hid : d.h * (1 / d.h - 1) = 1 - d.h := by field_simp
  rw [hid] at hi'
  dsimp [TailData.secondRampStart, TailData.longHold]
  nlinarith [d.h_pos]

theorem release_exp_bound (d : TailData) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (2 * releasePrimitive d t) ≤
      Real.exp 2 * Real.exp (-2 * t) +
        d.h ^ 8 * Real.exp 8 * Real.exp (-(2 * d.h) * t) := by
  by_cases hb : t ≤ d.secondRampStart
  · have hp := Real.exp_le_exp.mpr (show 2 * releasePrimitive d t ≤ 2 + -2 * t by
      linarith [releasePrimitive_plateau_le d ht hb])
    rw [Real.exp_add] at hp
    exact hp.trans (le_add_of_nonneg_right (by positivity))
  · have hp := Real.exp_le_exp.mpr (show 2 * releasePrimitive d t ≤
        (-2 * d.longHold) + 2 * (d.h * d.secondRampStart) + -(2 * d.h) * t by
      nlinarith [releasePrimitive_late_le d (le_of_not_ge hb)])
    rw [Real.exp_add, Real.exp_add, plateau_suppression] at hp
    have he : Real.exp (2 * (d.h * d.secondRampStart)) ≤ Real.exp 8 :=
      Real.exp_le_exp.mpr (by linarith [h_secondRampStart_le d])
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (pow_nonneg d.h_pos.le 8))
      (Real.exp_pos (-(2 * d.h) * t)).le
    exact (hp.trans hm).trans (le_add_of_nonneg_left (by positivity))

theorem energyDensity_release_eq (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    energyDensity d eta y = energyDensity d eta d.releaseStart *
      Real.exp (2 * releasePrimitive d (y - d.releaseStart)) *
      (tailShape d (y - tailStart d) / (1 - d.rho)) ^ 2 := by
  have hR : d.core.holdStart ≤ d.releaseStart := by
    linarith [coreEndpoint_ge_hold d, flattenEnd_gt_core d, releaseStart_gt_flattenEnd d]
  have hrad := radialAmplitude_hold d.core.dropLength_pos.le hR hy
    (P := d.core.P) (lam := d.core.lam)
  have hf : d.flattenEnd ≤ y := (releaseStart_gt_flattenEnd d).le.trans hy
  unfold energyDensity
  rw [finalAngular_uniform d eta hf,
    finalAngular_uniform_wait d eta (releaseStart_gt_flattenEnd d).le le_rfl,
    carrier, hrad, releaseAdjustment_eq]
  have hex : Real.exp y *
      (Real.exp (-(1 / 2 + d.core.lam) * (y - d.releaseStart)) *
        Real.exp (releasePrimitive d (y - d.releaseStart) +
          d.core.lam * (y - d.releaseStart))) ^ 2 =
      Real.exp d.releaseStart * Real.exp (2 * releasePrimitive d (y - d.releaseStart)) := by
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (radialAmplitude d.core.P d.core.dropLength d.core.lam d.releaseStart / 2) ^ 2 *
      (Real.exp y *
        (Real.exp (-(1 / 2 + d.core.lam) * (y - d.releaseStart)) *
          Real.exp (releasePrimitive d (y - d.releaseStart) +
            d.core.lam * (y - d.releaseStart))) ^ 2) *
        (tailShape d (y - tailStart d) / (1 - d.rho)) ^ 2 := by ring
    _ = _ := by rw [hex]; ring

theorem tailShape_ratio_sq_le (d : TailData) (t : ℝ) :
    (tailShape d t / (1 - d.rho)) ^ 2 ≤ 4 := by
  have hden : 0 < 1 - d.rho := by linarith [d.rho_lt_half]
  have hlo := div_nonneg (tailShape_pos d t).le hden.le
  have hup : tailShape d t / (1 - d.rho) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith [(tailShape_bounds d t).2, d.rho_lt_half]
  nlinarith

theorem energyDensity_release_bound (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    energyDensity d eta y ≤ 4 * energyDensity d eta d.releaseStart *
      (Real.exp 2 * Real.exp (-2 * (y - d.releaseStart)) +
        d.h ^ 8 * Real.exp 8 * Real.exp (-(2 * d.h) * (y - d.releaseStart))) := by
  rw [energyDensity_release_eq d eta hy]
  have hE := (energyDensity_pos d eta d.releaseStart).le
  have h1 := mul_le_mul_of_nonneg_left (tailShape_ratio_sq_le d (y - tailStart d))
    (mul_nonneg hE (Real.exp_pos (2 * releasePrimitive d (y - d.releaseStart))).le)
  have h2 := mul_le_mul_of_nonneg_left
    (release_exp_bound d (sub_nonneg.mpr hy)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hE)
  nlinarith

/-! ## The improper release integral -/

theorem integrableOn_shift_exp {a : ℝ} (ha : 0 < a) (R : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-a * (y - R))) (Ioi R) := by
  have he : (fun y : ℝ => Real.exp (-a * (y - R))) =
      (fun y => Real.exp (a * R) * Real.exp (-a * y)) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) R).const_mul _

theorem integral_shift_exp {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (∫ y in Ioi R, Real.exp (-a * (y - R))) = 1 / a := by
  have he : (fun y : ℝ => Real.exp (-a * (y - R))) =
      (fun y => Real.exp (a * R) * Real.exp (-a * y)) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  rw [neg_mul, Real.exp_neg]
  field_simp

noncomputable def releaseEnvelope (d : TailData) (y : ℝ) : ℝ :=
  Real.exp 2 * Real.exp (-2 * (y - d.releaseStart)) +
    d.h ^ 8 * Real.exp 8 * Real.exp (-(2 * d.h) * (y - d.releaseStart))

theorem releaseEnvelope_integrable (d : TailData) :
    IntegrableOn (releaseEnvelope d) (Ioi d.releaseStart) :=
  ((integrableOn_shift_exp (by norm_num : (0 : ℝ) < 2) d.releaseStart).const_mul _).add
    ((integrableOn_shift_exp (mul_pos (by norm_num) d.h_pos) d.releaseStart).const_mul _)

theorem integral_releaseEnvelope (d : TailData) :
    (∫ y in Ioi d.releaseStart, releaseEnvelope d y) =
      Real.exp 2 / 2 + d.h ^ 7 * Real.exp 8 / 2 := by
  unfold releaseEnvelope
  rw [integral_add
    ((integrableOn_shift_exp (by norm_num : (0 : ℝ) < 2) d.releaseStart).const_mul _)
    ((integrableOn_shift_exp (mul_pos (by norm_num) d.h_pos) d.releaseStart).const_mul _)]
  rw [integral_const_mul, integral_const_mul,
    integral_shift_exp (by norm_num : (0 : ℝ) < 2),
    integral_shift_exp (mul_pos (by norm_num) d.h_pos)]
  field_simp [d.h_pos.ne']

noncomputable def releaseConstant : ℝ := 2 * (Real.exp 2 + Real.exp 8)

theorem releaseConstant_pos : 0 < releaseConstant := by
  unfold releaseConstant
  positivity

theorem energyDensity_integrable_release (d : TailData) (eta : ℝ) :
    IntegrableOn (energyDensity d eta) (Ioi d.releaseStart) := by
  have hm := (releaseEnvelope_integrable d).const_mul (4 * energyDensity d eta d.releaseStart)
  refine hm.mono' (energyDensity_continuous d eta).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (energyDensity_pos d eta y)]
  exact energyDensity_release_bound d eta hy.le

/-- The release cost is independent of both `h` and `lam`. -/
theorem integral_energyDensity_release_le (d : TailData) (eta : ℝ) :
    (∫ y in Ioi d.releaseStart, energyDensity d eta y) ≤
      releaseConstant * energyDensity d eta d.releaseStart := by
  have hm := (releaseEnvelope_integrable d).const_mul (4 * energyDensity d eta d.releaseStart)
  have h := setIntegral_mono_on (energyDensity_integrable_release d eta) hm
    measurableSet_Ioi (fun y hy => energyDensity_release_bound d eta hy.le)
  rw [integral_const_mul, integral_releaseEnvelope] at h
  have hp : d.h ^ 7 ≤ 1 := pow_le_one₀ d.h_pos.le (by linarith [d.h_lt_half])
  have hE := (energyDensity_pos d eta d.releaseStart).le
  have he := (Real.exp_pos (8 : ℝ)).le
  have hp' := mul_le_mul_of_nonneg_right hp he
  have hp'' := mul_le_mul_of_nonneg_left hp' hE
  dsimp [releaseConstant]
  nlinarith

/-! ## Flattening and the uniform wait -/

theorem finalAngular_before_release (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.releaseStart) : finalAngular d (y, eta) = flattened d (y, eta) := by
  have ht : y - tailStart d ≤ 1 := by linarith [tailStart_gt_release d]
  have hn : 1 - d.rho ≠ 0 := by linarith [d.rho_lt_half]
  simp [finalAngular, releaseAdjustment_early d (sub_nonpos.mpr hy), tailShape_early d ht, hn]

theorem flattenFactor_le_one (d : TailData) (eta y : ℝ) (heta : eta ^ 2 ≤ 1) :
    flattenFactor d (y, eta) ≤ 1 := by
  have hlog : logShape eta ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by nlinarith)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos (sigma_nonneg _) (sub_nonpos.mpr hlog)

theorem core_energy_hold (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) :
    Real.exp y * angular d.core.P d.core.dropLength d.core.lam (y, eta) ^ 2 =
      energyDensity d eta d.core.endpoint * Real.exp (-2 * d.core.lam * (y - d.core.endpoint)) := by
  have hr := radialAmplitude_hold d.core.dropLength_pos.le (coreEndpoint_ge_hold d) hy
    (P := d.core.P) (lam := d.core.lam)
  unfold energyDensity
  rw [finalAngular_before d eta le_rfl]
  simp only [angular]
  rw [hr]
  have he : Real.exp y * Real.exp (-(1 / 2 + d.core.lam) * (y - d.core.endpoint)) ^ 2 =
      Real.exp d.core.endpoint * Real.exp (-2 * d.core.lam * (y - d.core.endpoint)) := by
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (radialAmplitude d.core.P d.core.dropLength d.core.lam d.core.endpoint * shape eta) ^ 2 *
      (Real.exp y * Real.exp (-(1 / 2 + d.core.lam) * (y - d.core.endpoint)) ^ 2) := by ring
    _ = _ := by rw [he]; ring

theorem energyDensity_prefix_le (d : TailData) (eta : ℝ) (heta : eta ^ 2 ≤ 1)
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    energyDensity d eta y ≤ energyDensity d eta d.core.endpoint := by
  have hf0 : 0 ≤ flattenFactor d (y, eta) := (Real.exp_pos _).le
  have hf1 := flattenFactor_le_one d eta y heta
  have hf2 : flattenFactor d (y, eta) ^ 2 ≤ 1 := by nlinarith
  have he0 := (Real.exp_pos (-2 * d.core.lam * (y - d.core.endpoint))).le
  have he1 : Real.exp (-2 * d.core.lam * (y - d.core.endpoint)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [d.core.lam_pos, sub_nonneg.mpr hy]
  have hE := (energyDensity_pos d eta d.core.endpoint).le
  have hid : energyDensity d eta y = energyDensity d eta d.core.endpoint *
      Real.exp (-2 * d.core.lam * (y - d.core.endpoint)) * flattenFactor d (y, eta) ^ 2 := by
    change Real.exp y * finalAngular d (y, eta) ^ 2 = _
    rw [finalAngular_before_release d eta hy']
    dsimp only [flattened]
    rw [mul_pow, ← mul_assoc, core_energy_hold d eta hy]
  rw [hid]
  calc
    _ ≤ energyDensity d eta d.core.endpoint * Real.exp (-2 * d.core.lam * (y - d.core.endpoint)) :=
      by
      nlinarith [mul_nonneg hE he0]
    _ ≤ energyDensity d eta d.core.endpoint := by nlinarith

theorem endpoint_le_releaseStart (d : TailData) : d.core.endpoint ≤ d.releaseStart :=
  (flattenEnd_gt_core d).le.trans (releaseStart_gt_flattenEnd d).le

theorem energyDensity_integrable_postPulse (d : TailData) (eta : ℝ) :
    IntegrableOn (energyDensity d eta) (Ioi d.core.endpoint) := by
  rw [← Ioc_union_Ioi_eq_Ioi (endpoint_le_releaseStart d)]
  exact integrableOn_union.mpr
    ⟨(energyDensity_continuous d eta).integrableOn_Ioc, energyDensity_integrable_release d eta⟩

noncomputable def postPulseEnergy (d : TailData) (eta : ℝ) : ℝ :=
  ∫ y in Ioi d.core.endpoint, energyDensity d eta y

theorem postPulseEnergy_nonneg (d : TailData) (eta : ℝ) : 0 ≤ postPulseEnergy d eta :=
  integral_nonneg (fun y => (energyDensity_pos d eta y).le)

theorem postPulseEnergy_split (d : TailData) (eta : ℝ) {a : ℝ}
    (ha : d.core.endpoint ≤ a) :
    postPulseEnergy d eta = (∫ y in d.core.endpoint..a, energyDensity d eta y) +
      ∫ y in Ioi a, energyDensity d eta y := by
  have hdis : Disjoint (Ioc d.core.endpoint a) (Ioi a) := by
    rw [disjoint_left]
    intro y hy hy'
    exact (not_lt_of_ge hy.2) hy'
  have hint := (energyDensity_integrable_postPulse d eta).mono_set
    (show Ioi a ⊆ Ioi d.core.endpoint from fun y hy => lt_of_le_of_lt ha hy)
  rw [postPulseEnergy, ← Ioc_union_Ioi_eq_Ioi ha,
    setIntegral_union hdis measurableSet_Ioi (energyDensity_continuous d eta).integrableOn_Ioc hint,
    intervalIntegral.integral_of_le ha]

theorem postPulseEnergy_le_length (d : TailData) (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    postPulseEnergy d eta ≤
      (d.releaseStart - d.core.endpoint + releaseConstant) * energyDensity d eta d.core.endpoint :=
        by
  have hle := endpoint_le_releaseStart d
  have hp := intervalIntegral.integral_mono_on (μ := volume) hle
    ((energyDensity_continuous d eta).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)
    (fun y hy => energyDensity_prefix_le d eta heta hy.1 hy.2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hp
  have hr := integral_energyDensity_release_le d eta
  have hR := mul_le_mul_of_nonneg_left (energyDensity_prefix_le d eta heta hle le_rfl)
    releaseConstant_pos.le
  rw [postPulseEnergy_split d eta hle]
  nlinarith

noncomputable def tailConstant : ℝ := flattenLength + 30 + releaseConstant

theorem tailConstant_pos : 0 < tailConstant := by
  unfold tailConstant
  linarith [flattenLength_pos, releaseConstant_pos]

/-- Actual outgoing energy, with a constant independent of every parameter. -/
theorem postPulseEnergy_le (d : TailData) (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    postPulseEnergy d eta ≤ tailConstant * (1 + Real.log (1 / d.core.lam)) *
      energyDensity d eta d.core.endpoint := by
  have hlog : 0 ≤ Real.log (1 / d.core.lam) := by
    have := d.uniformWait_pos
    dsimp [TailData.uniformWait] at this
    linarith
  have hc : d.releaseStart - d.core.endpoint + releaseConstant ≤
      tailConstant * (1 + Real.log (1 / d.core.lam)) := by
    dsimp [TailData.releaseStart, TailData.flattenEnd, TailData.uniformWait, tailConstant]
    nlinarith [mul_nonneg (add_nonneg flattenLength_pos.le releaseConstant_pos.le) hlog]
  exact (postPulseEnergy_le_length d eta heta).trans
    (mul_le_mul_of_nonneg_right hc (energyDensity_pos d eta d.core.endpoint).le)

/-! ## Genuine parameter regularity and derivative bounds -/

theorem energyDensity_contDiff (d : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => energyDensity d p.1 p.2) :=
  contDiff_snd.exp.mul
    (((finalAngular_contDiff d).comp (contDiff_snd.prodMk contDiff_fst)).pow 2)

theorem postPulseEnergy_split_flattenEnd (d : TailData) (eta : ℝ) :
    postPulseEnergy d eta =
      (∫ y in d.core.endpoint..d.flattenEnd, energyDensity d eta y) +
        ∫ y in Ioi d.flattenEnd, energyDensity d 0 y := by
  rw [postPulseEnergy_split d eta (flattenEnd_gt_core d).le]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  unfold energyDensity
  rw [finalAngular_eta_independent d eta 0 hy.le]

theorem postPulseEnergy_contDiff (d : TailData) : ContDiff ℝ ∞ (postPulseEnergy d) := by
  have hi := ParametricRephase.intervalIntegral_contDiffOn_of_joint
    (fun p : ℝ × ℝ => energyDensity d p.1 p.2) univ isOpen_univ
    (energyDensity_contDiff d).contDiffOn d.core.endpoint d.flattenEnd (flattenEnd_gt_core d).le
  have hi' : ContDiff ℝ ∞ (fun eta => ∫ y in d.core.endpoint..d.flattenEnd, energyDensity d eta y)
    :=
    contDiffOn_univ.mp hi
  have heq : postPulseEnergy d = (fun eta =>
      (∫ y in d.core.endpoint..d.flattenEnd, energyDensity d eta y) +
        ∫ y in Ioi d.flattenEnd, energyDensity d 0 y) :=
    funext (postPulseEnergy_split_flattenEnd d)
  rw [heq]
  exact hi'.add contDiff_const

noncomputable def etaCoefficient (d : TailData) (eta y : ℝ) : ℝ :=
  -(4 * (1 - sigma ((y - d.core.endpoint) / flattenLength)) * eta / (1 + eta ^ 2))

theorem etaCoefficient_continuous (d : TailData) (eta : ℝ) :
    Continuous (etaCoefficient d eta) := by
  have hs := sigma_contDiff.continuous
  unfold etaCoefficient
  fun_prop

theorem finalAngular_hasDerivAt_eta (d : TailData) (eta y : ℝ) :
    HasDerivAt (fun q => finalAngular d (y, q))
      (-(2 * (1 - sigma ((y - d.core.endpoint) / flattenLength)) * eta / (1 + eta ^ 2)) *
        finalAngular d (y, eta)) eta := by
  have hq : HasDerivAt (fun q : ℝ => 1 + q ^ 2) (2 * eta) eta := by
    simpa using ((hasDerivAt_id eta).pow 2).const_add 1
  have hn : 1 + eta ^ 2 ≠ 0 := by positivity
  have hrho : 1 - d.rho ≠ 0 := by linarith [d.rho_lt_half]
  have hs := hq.inv hn
  have hl := ((hq.log hn).sub_const (Real.log 2)).const_mul
    (sigma ((y - d.core.endpoint) / flattenLength))
  have hf := ((hs.const_mul (radialAmplitude d.core.P d.core.dropLength d.core.lam y)).mul hl.exp)
  have hE := (hf.mul_const (Real.exp (releaseAdjustment d (y - d.releaseStart)))).mul_const
    (tailShape d (y - tailStart d) / (1 - d.rho))
  convert! hE using 1
  dsimp [finalAngular, flattened, angular, shape, flattenFactor, logShape]
  field_simp [hn, hrho] ; ring

theorem energyDensity_hasDerivAt_eta (d : TailData) (eta y : ℝ) :
    HasDerivAt (fun q => energyDensity d q y)
      (etaCoefficient d eta y * energyDensity d eta y) eta := by
  convert! ((finalAngular_hasDerivAt_eta d eta y).pow 2).const_mul (Real.exp y) using 1
  dsimp [etaCoefficient, energyDensity]
  ring

theorem etaCoefficient_abs_le (d : TailData) (eta y : ℝ) : |etaCoefficient d eta y| ≤ 2 := by
  have hs0 := sigma_nonneg ((y - d.core.endpoint) / flattenLength)
  have hs1 := sigma_le_one ((y - d.core.endpoint) / flattenLength)
  have hp : 0 < 1 + eta ^ 2 := by positivity
  have heta : 2 * |eta| ≤ 1 + eta ^ 2 := by
    nlinarith [sq_nonneg (|eta| - 1), sq_abs eta]
  have hprod : 4 * (1 - sigma ((y - d.core.endpoint) / flattenLength)) * |eta| ≤
      4 * |eta| := by nlinarith [abs_nonneg eta]
  dsimp [etaCoefficient]
  rw [abs_neg, abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_nonneg (sub_nonneg.mpr hs1), abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (by linarith)

theorem energyDensity_eta_bound (d : TailData) (eta y : ℝ) :
    |etaCoefficient d eta y * energyDensity d eta y| ≤ 2 * energyDensity d eta y := by
  rw [abs_mul, abs_of_pos (energyDensity_pos d eta y)]
  exact mul_le_mul_of_nonneg_right (etaCoefficient_abs_le d eta y) (energyDensity_pos d eta y).le

theorem integral_energyDensity_hasDerivAt (d : TailData) (eta a b : ℝ) :
    HasDerivAt (fun q => ∫ y in a..b, energyDensity d q y)
      (∫ y in a..b, etaCoefficient d eta y * energyDensity d eta y) eta := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      etaCoefficient d p.1 p.2 * energyDensity d p.1 p.2) := by
    apply Continuous.mul _ (energyDensity_contDiff d).continuous
    unfold etaCoefficient
    have hs : Continuous (fun p : ℝ × ℝ => sigma ((p.2 - d.core.endpoint) / flattenLength)) :=
      sigma_contDiff.continuous.comp ((continuous_snd.sub continuous_const).div_const _)
    exact (((continuous_const.mul (continuous_const.sub hs)).mul continuous_fst).div
      (continuous_const.fun_add (continuous_fst.fun_pow 2)) (fun p => by positivity)).neg
  obtain ⟨C, hC⟩ := ((isCompact_closedBall eta 1).prod
    (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn hc.continuousOn
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := energyDensity d)
    (F' := fun q y => etaCoefficient d q y * energyDensity d q y)
    (bound := fun _ => C) (Metric.ball_mem_nhds eta (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun q => (energyDensity_continuous d q).aestronglyMeasurable)
    ((energyDensity_continuous d eta).intervalIntegrable a b)
    ((etaCoefficient_continuous d eta).mul (energyDensity_continuous d eta)).aestronglyMeasurable
    (Eventually.of_forall fun t ht q hq =>
      hC (q, t) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hq).le, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ q _ => energyDensity_hasDerivAt_eta d q t)).2

theorem postPulseEnergy_hasDerivAt (d : TailData) (eta : ℝ) :
    HasDerivAt (postPulseEnergy d)
      (∫ y in d.core.endpoint..d.flattenEnd,
        etaCoefficient d eta y * energyDensity d eta y) eta := by
  have heq : postPulseEnergy d = (fun q =>
      (∫ y in d.core.endpoint..d.flattenEnd, energyDensity d q y) +
        ∫ y in Ioi d.flattenEnd, energyDensity d 0 y) :=
    funext (postPulseEnergy_split_flattenEnd d)
  rw [heq]
  exact (integral_energyDensity_hasDerivAt d eta d.core.endpoint d.flattenEnd).add_const _

/-- Parameter variation occurs only on the fixed flattening interval. -/
theorem abs_deriv_postPulseEnergy_le (d : TailData) (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    |deriv (postPulseEnergy d) eta| ≤
      2 * flattenLength * energyDensity d eta d.core.endpoint := by
  rw [(postPulseEnergy_hasDerivAt d eta).deriv]
  have hbound : ∀ y ∈ uIoc d.core.endpoint d.flattenEnd,
      ‖etaCoefficient d eta y * energyDensity d eta y‖ ≤
        2 * energyDensity d eta d.core.endpoint := by
    intro y hy
    have hy' := uIoc_of_le (flattenEnd_gt_core d).le ▸ hy
    have hE := energyDensity_prefix_le d eta heta hy'.1.le
      (hy'.2.trans (releaseStart_gt_flattenEnd d).le)
    simpa only [Real.norm_eq_abs] using (energyDensity_eta_bound d eta y).trans
      (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (flattenEnd_gt_core d).le)] at h
  have hlen : d.flattenEnd - d.core.endpoint = flattenLength := by
    dsimp [TailData.flattenEnd]
    ring
  rw [hlen] at h
  nlinarith

/-! ## Relation to the pulse normalization -/

theorem energyDensity_endpoint_eq (d : TailData) (eta : ℝ) :
    energyDensity d eta d.core.endpoint =
      (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2) * Real.exp (-26) :=
        by
  have hy : d.core.pulseStart ≤ d.core.endpoint := by
    dsimp [OutgoingSchedule.Parameters.endpoint]
    linarith [d.core.pulseLength_pos]
  unfold energyDensity
  rw [finalAngular_before d eta le_rfl, angular_pulse d.core eta hy]
  have he : Real.exp d.core.endpoint *
      Real.exp (-(1 / 2 + d.core.lam) * (d.core.endpoint - d.core.pulseStart)) ^ 2 =
      Real.exp d.core.pulseStart * Real.exp (-26) := by
    simp only [pow_two, ← Real.exp_add]
    congr 1
    dsimp [OutgoingSchedule.Parameters.endpoint, OutgoingSchedule.Parameters.pulseLength]
    field_simp [d.core.lam_pos.ne'] ; ring
  calc
    _ = (pulseAmplitude d.core ^ 2 * shape eta ^ 2) *
      (Real.exp d.core.endpoint *
        Real.exp (-(1 / 2 + d.core.lam) * (d.core.endpoint - d.core.pulseStart)) ^ 2) := by ring
    _ = _ := by rw [he]; ring

theorem energyDensity_endpoint_le (d : TailData) (eta : ℝ) :
    energyDensity d eta d.core.endpoint ≤
      Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2 := by
  rw [energyDensity_endpoint_eq]
  have he : Real.exp (-26 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hp : 0 ≤ Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2 := by
    positivity
  nlinarith

theorem normalized_postPulseEnergy_le (d : TailData) (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    d.core.lam * postPulseEnergy d eta /
      (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2) ≤
      tailConstant * d.core.lam * (1 + Real.log (1 / d.core.lam)) := by
  have hpos : 0 < Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2 :=
    mul_pos (mul_pos (Real.exp_pos _) (sq_pos_of_pos (pulseAmplitude_pos d.core)))
      (sq_pos_of_pos (shape_pos eta))
  apply (div_le_iff₀ hpos).mpr
  have hlog : 0 ≤ 1 + Real.log (1 / d.core.lam) := by
    have := d.uniformWait_pos
    dsimp [TailData.uniformWait] at this
    linarith
  have hbase := (postPulseEnergy_le d eta heta).trans
    (mul_le_mul_of_nonneg_left (energyDensity_endpoint_le d eta)
      (mul_nonneg tailConstant_pos.le hlog))
  have h := mul_le_mul_of_nonneg_left hbase d.core.lam_pos.le
  nlinarith

/-- Normalization of the derivative of the energy. The derivative of the
normalized quotient also has the elementary derivative of `shape eta ^ 2`. -/
theorem normalized_deriv_postPulseEnergy_le (d : TailData) (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    d.core.lam * |deriv (postPulseEnergy d) eta| /
      (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2) ≤
      2 * flattenLength * d.core.lam := by
  have hpos : 0 < Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2 :=
    mul_pos (mul_pos (Real.exp_pos _) (sq_pos_of_pos (pulseAmplitude_pos d.core)))
      (sq_pos_of_pos (shape_pos eta))
  apply (div_le_iff₀ hpos).mpr
  have hbase := (abs_deriv_postPulseEnergy_le d eta heta).trans
    (mul_le_mul_of_nonneg_left (energyDensity_endpoint_le d eta)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) flattenLength_pos.le))
  have h := mul_le_mul_of_nonneg_left hbase d.core.lam_pos.le
  nlinarith

/-! ## Differentiating the fully normalized quotient -/

noncomputable def normalizedPostPulseEnergy (d : TailData) (eta : ℝ) : ℝ :=
  d.core.lam * postPulseEnergy d eta /
    (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2)

theorem normalizedPostPulseEnergy_eq (d : TailData) (eta : ℝ) :
    normalizedPostPulseEnergy d eta =
      (d.core.lam / (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2)) *
        postPulseEnergy d eta * (1 + eta ^ 2) ^ 2 := by
  have hp : 1 + eta ^ 2 ≠ 0 := by positivity
  simp only [normalizedPostPulseEnergy, shape]
  field_simp [hp]

theorem normalizedPostPulseEnergy_nonneg (d : TailData) (eta : ℝ) :
    0 ≤ normalizedPostPulseEnergy d eta := by
  unfold normalizedPostPulseEnergy
  exact div_nonneg (mul_nonneg d.core.lam_pos.le (postPulseEnergy_nonneg d eta)) (by positivity)

theorem normalizedPostPulseEnergy_contDiff (d : TailData) :
    ContDiff ℝ ∞ (normalizedPostPulseEnergy d) := by
  have he : normalizedPostPulseEnergy d = (fun eta =>
      (d.core.lam / (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2)) *
        postPulseEnergy d eta * (1 + eta ^ 2) ^ 2) :=
    funext (normalizedPostPulseEnergy_eq d)
  rw [he]
  exact (contDiff_const.mul (postPulseEnergy_contDiff d)).mul
    ((contDiff_const.add (contDiff_id.pow 2)).pow 2)

theorem normalizedPostPulseEnergy_hasDerivAt (d : TailData) (eta : ℝ) :
    HasDerivAt (normalizedPostPulseEnergy d)
      (d.core.lam * deriv (postPulseEnergy d) eta /
          (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2) +
        (4 * eta / (1 + eta ^ 2)) * normalizedPostPulseEnergy d eta) eta := by
  have hE := ((postPulseEnergy_contDiff d).differentiable (by simp) eta).hasDerivAt
  have hp : HasDerivAt (fun q : ℝ => (1 + q ^ 2) ^ 2) (4 * eta * (1 + eta ^ 2)) eta := by
    convert! (((hasDerivAt_id eta).fun_pow 2).const_add 1).fun_pow 2 using 1
    simp only [id_eq]
    ring
  have hd := (hE.const_mul
    (d.core.lam / (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2))).fun_mul hp
  have he : normalizedPostPulseEnergy d = (fun eta =>
      (d.core.lam / (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2)) *
        postPulseEnergy d eta * (1 + eta ^ 2) ^ 2) :=
    funext (normalizedPostPulseEnergy_eq d)
  rw [he]
  convert! hd using 1
  have hp0 : 1 + eta ^ 2 ≠ 0 := by positivity
  have hN : Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 ≠ 0 :=
    (mul_pos (Real.exp_pos _) (sq_pos_of_pos (pulseAmplitude_pos d.core))).ne'
  simp only [shape]
  field_simp [hp0, hN]

/-- This is the derivative of the full quotient, including its shape factor. -/
theorem abs_deriv_normalizedPostPulseEnergy_le (d : TailData) (eta : ℝ)
    (heta : eta ^ 2 ≤ 1) :
    |deriv (normalizedPostPulseEnergy d) eta| ≤
      (2 * flattenLength + 4 * tailConstant) * d.core.lam *
        (1 + Real.log (1 / d.core.lam)) := by
  have hden : 0 < Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2 :=
    mul_pos (mul_pos (Real.exp_pos _) (sq_pos_of_pos (pulseAmplitude_pos d.core)))
      (sq_pos_of_pos (shape_pos eta))
  have hp : 0 < 1 + eta ^ 2 := by positivity
  have habs : |eta| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (eta + 1), sq_nonneg (eta - 1)]
  have hcoef : |4 * eta / (1 + eta ^ 2)| ≤ 4 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg eta]
  have hE0 := normalizedPostPulseEnergy_nonneg d eta
  have hE := normalized_postPulseEnergy_le d eta heta
  change normalizedPostPulseEnergy d eta ≤ _ at hE
  have hEd := normalized_deriv_postPulseEnergy_le d eta heta
  have hfirst :
      |d.core.lam * deriv (postPulseEnergy d) eta /
        (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2)| ≤
        2 * flattenLength * d.core.lam := by
    simpa only [abs_div, abs_mul, abs_of_pos d.core.lam_pos, abs_of_pos hden] using hEd
  have hsecond : |(4 * eta / (1 + eta ^ 2)) * normalizedPostPulseEnergy d eta| ≤
      4 * (tailConstant * d.core.lam * (1 + Real.log (1 / d.core.lam))) := by
    rw [abs_mul, abs_of_nonneg hE0]
    exact (mul_le_mul_of_nonneg_right hcoef hE0).trans
      (mul_le_mul_of_nonneg_left hE (by norm_num))
  have hlog : 1 ≤ 1 + Real.log (1 / d.core.lam) := by
    have := d.uniformWait_pos
    dsimp [TailData.uniformWait] at this
    linarith
  have hpad := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) flattenLength_pos.le) d.core.lam_pos.le)
  rw [(normalizedPostPulseEnergy_hasDerivAt d eta).deriv]
  calc
    _ ≤ |d.core.lam * deriv (postPulseEnergy d) eta /
          (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2)| +
        |(4 * eta / (1 + eta ^ 2)) * normalizedPostPulseEnergy d eta| := abs_add_le _ _
    _ ≤ 2 * flattenLength * d.core.lam +
        4 * (tailConstant * d.core.lam * (1 + Real.log (1 / d.core.lam))) :=
      add_le_add hfirst hsecond
    _ ≤ _ := by nlinarith

theorem abs_deriv_normalized_postPulseEnergy_le (d : TailData) (eta : ℝ)
    (heta : eta ^ 2 ≤ 1) :
    |deriv (fun q => d.core.lam * postPulseEnergy d q /
      (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape q ^ 2)) eta| ≤
      (2 * flattenLength + 4 * tailConstant) * d.core.lam *
        (1 + Real.log (1 / d.core.lam)) :=
  abs_deriv_normalizedPostPulseEnergy_le d eta heta

end NavierStokes.TailEnergyBounds
