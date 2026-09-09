/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TailEnergyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingPulseBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialSchedule
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual pulse energy and its scalar amplitude

The pulse constant is the integral of the constructed smooth pulse from
`OutgoingSchedule`, rather than an abstract coefficient satisfying assumed
bounds. All energy coefficients below refer to the actual outgoing profiles.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators
open NavierStokes.OutgoingSchedule

namespace NavierStokes.PulseAmplitude

theorem pulseRamp_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ pulseRamp z :=
  intervalIntegral.integral_nonneg_of_forall hz (fun _ => sigma_nonneg _)

theorem pulseRamp_le {z : ℝ} (hz : 0 ≤ z) : pulseRamp z ≤ z := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) hz
    ((sigma_contDiff.continuous.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 z)
    (continuous_const.intervalIntegrable 0 z)
    (fun t _ => sigma_le_one (50 * t))
  simpa only [pulseRamp, primitive, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one, Function.comp_def, Pi.mul_apply, id_eq] using hi

theorem pulseRamp_lower {z : ℝ} (hz : 1 / 50 ≤ z) : z - 1 / 50 ≤ pulseRamp z := by
  have hc : Continuous (fun t : ℝ => sigma (50 * t)) :=
    sigma_contDiff.continuous.comp (continuous_const.mul continuous_id)
  have hi := intervalIntegral.integral_mono_interval (μ := volume) (f := fun t : ℝ => sigma (50 *
      t))
    (by norm_num : (0 : ℝ) ≤ 1 / 50) hz le_rfl
    (Eventually.of_forall (fun _ => sigma_nonneg _)) (hc.intervalIntegrable 0 z)
  have he : (∫ t in (1 / 50 : ℝ)..z, sigma (50 * t)) = z - 1 / 50 := by
    calc
      _ = ∫ _t in (1 / 50 : ℝ)..z, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply sigma_one
        have ht' := (uIcc_of_le hz ▸ ht).1
        linarith
      _ = _ := by simp
  simpa only [he, pulseRamp, primitive] using hi

theorem mainPulse_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ mainPulse z :=
  mul_nonneg (pulseRamp_nonneg hz) (sub_nonneg.mpr (sigma_le_one _))

theorem mainPulse_le {z : ℝ} (hz : 0 ≤ z) : mainPulse z ≤ z := by
  have hp := pulseRamp_nonneg hz
  have hs := sigma_nonneg (z - 10)
  have hl := pulseRamp_le hz
  unfold mainPulse
  nlinarith

theorem mainPulse_lower {z : ℝ} (hz : 1 / 50 ≤ z) (hz' : z ≤ 10) :
    z - 1 / 50 ≤ mainPulse z := by
  simpa [mainPulse, sigma_zero (by linarith : z - 10 ≤ 0)] using pulseRamp_lower hz

/-- Pulse constant, given by `∫ z in (0 : ℝ)..13, Real.exp (-2 * z) * mainPulse z ^ 2`. -/
def pulseConstant : ℝ := ∫ z in (0 : ℝ)..13, Real.exp (-2 * z) * mainPulse z ^ 2

theorem energyWeight_continuous : Continuous (fun z : ℝ => Real.exp (-2 * z)) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_id)

/-- Weighted square primitive, given by `-Real.exp (-2 * z) * ((z - a) ^ 2 / 2 + (z - a) / 2 + 1
/ 4)`. -/
def weightedSquarePrimitive (a z : ℝ) : ℝ :=
  -Real.exp (-2 * z) * ((z - a) ^ 2 / 2 + (z - a) / 2 + 1 / 4)

theorem weightedSquarePrimitive_hasDerivAt (a z : ℝ) :
    HasDerivAt (weightedSquarePrimitive a) (Real.exp (-2 * z) * (z - a) ^ 2) z := by
  have ht := (hasDerivAt_id z).sub_const a
  have he := ((hasDerivAt_id z).const_mul (-2)).exp.fun_neg
  convert! he.fun_mul (((ht.fun_pow 2).div_const 2 |>.fun_add (ht.div_const 2)).add_const (1 / 4))
      using 1
  simp only [id_eq]
  ring

theorem weightedSquare_integral (a l u : ℝ) :
    (∫ z in l..u, Real.exp (-2 * z) * (z - a) ^ 2) =
      weightedSquarePrimitive a u - weightedSquarePrimitive a l := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => weightedSquarePrimitive_hasDerivAt a z)
  exact (energyWeight_continuous.fun_mul
    ((continuous_id.fun_sub continuous_const).fun_pow 2)).intervalIntegrable l u

theorem pulseConstant_upper : pulseConstant ≤ 1 / 4 := by
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 13)
    ((energyWeight_continuous.fun_mul
      (mainPulse_contDiff.continuous.fun_pow 2)).intervalIntegrable 0 13)
    ((energyWeight_continuous.fun_mul (continuous_id.fun_pow 2)).intervalIntegrable 0 13)
    (fun z hz => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mainPulse_nonneg hz.1) (mainPulse_le hz.1) 2) (Real.exp_pos _).le)
  have hi := weightedSquare_integral 0 0 13
  norm_num [weightedSquarePrimitive] at hi
  dsimp [pulseConstant]
  have he := (Real.exp_pos (-26 : ℝ)).le
  simp only [id_eq, neg_mul] at *
  linarith

private theorem exp_neg_ten_le : Real.exp (-10 : ℝ) ≤ 1 / 1024 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (1024 : ℝ) ≤ Real.exp 10 := calc
    (1024 : ℝ) = 2 ^ 10 := by norm_num
    _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he 10
    _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1024) hp

theorem pulseConstant_lower : 1 / 5 < pulseConstant := by
  have hw : Continuous (fun z : ℝ => Real.exp (-2 * z) * mainPulse z ^ 2) :=
    energyWeight_continuous.fun_mul (mainPulse_contDiff.continuous.fun_pow 2)
  have hsub := intervalIntegral.integral_mono_interval (μ := volume)
    (f := fun z : ℝ => Real.exp (-2 * z) * mainPulse z ^ 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 50) (by norm_num : (1 / 50 : ℝ) ≤ 5)
    (by norm_num : (5 : ℝ) ≤ 13)
    (Eventually.of_forall (fun z => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
    (hw.intervalIntegrable 0 13)
  have hlo := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 / 50 : ℝ) ≤ 5)
    ((energyWeight_continuous.fun_mul
      ((continuous_id.fun_sub continuous_const).fun_pow 2)).intervalIntegrable (1 / 50) 5)
    (hw.intervalIntegrable (1 / 50) 5) (fun z hz =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hz.1)
        (mainPulse_lower hz.1 (by linarith [hz.2])) 2) (Real.exp_pos _).le)
  have hi := weightedSquare_integral (1 / 50) (1 / 50) 5
  norm_num [weightedSquarePrimitive] at hi
  have he : (24 / 25 : ℝ) ≤ Real.exp (-1 / 25) := by
    linarith [Real.add_one_le_exp (-1 / 25 : ℝ)]
  have hten := exp_neg_ten_le
  change (∫ z in (1 / 50 : ℝ)..5, Real.exp (-2 * z) * mainPulse z ^ 2) ≤ pulseConstant at hsub
  simp only [id_eq, neg_mul] at *
  linarith

theorem pulseConstant_bounds : 1 / 5 < pulseConstant ∧ pulseConstant ≤ 1 / 4 :=
  ⟨pulseConstant_lower, pulseConstant_upper⟩

/-! ## The actual affine correction and the actual pulse quadratic -/

/-- Eta polynomial, given by `eta * (1 + eta ^ 2)`. -/
def etaPolynomial (eta : ℝ) : ℝ := eta * (1 + eta ^ 2)

/-- Prefix repair, given by `LocalizedMomentRepair.repair c.exponents c.lower c.upper (fun i =>
-prefixCoefficient c i) (Real.exp y)`. -/
def prefixRepair (c : Parameters) (y : ℝ) : ℝ :=
  LocalizedMomentRepair.repair c.exponents c.lower c.upper
    (fun i => -prefixCoefficient c i) (Real.exp y)

/-- Amplitude repair, given by `LocalizedMomentRepair.repair c.exponents c.lower c.upper (fun i
=> -mainMoment c i) (Real.exp y)`. -/
def amplitudeRepair (c : Parameters) (y : ℝ) : ℝ :=
  LocalizedMomentRepair.repair c.exponents c.lower c.upper
    (fun i => -mainMoment c i) (Real.exp y)

/-- Amplitude shape, given by `mainPulse (c.lam * y) + amplitudeRepair c y`. -/
def amplitudeShape (c : Parameters) (y : ℝ) : ℝ :=
  mainPulse (c.lam * y) + amplitudeRepair c y

theorem prefixRepair_contDiff (c : Parameters) : ContDiff ℝ ∞ (prefixRepair c) :=
  (LocalizedMomentRepair.repair_contDiff _ _ _ _).comp Real.contDiff_exp

theorem amplitudeRepair_contDiff (c : Parameters) : ContDiff ℝ ∞ (amplitudeRepair c) :=
  (LocalizedMomentRepair.repair_contDiff _ _ _ _).comp Real.contDiff_exp

theorem amplitudeShape_contDiff (c : Parameters) : ContDiff ℝ ∞ (amplitudeShape c) :=
  (mainPulse_contDiff.comp (contDiff_const.mul contDiff_id)).add (amplitudeRepair_contDiff c)

theorem correction_eq_affine (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    correction c amp eta (Real.exp y) =
      etaPolynomial eta * prefixRepair c y + amp eta * amplitudeRepair c y := by
  have he : debt c amp eta =
      etaPolynomial eta • (fun i => -prefixCoefficient c i) +
        amp eta • (fun i => -mainMoment c i) := by
    funext i
    simp only [debt, etaPolynomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [correction, he, LocalizedMomentRepair.repair_add,
    LocalizedMomentRepair.repair_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    prefixRepair, amplitudeRepair]

theorem pulseRatio_eq_affine (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    pulseRatio c amp (y, eta) =
      amp eta * amplitudeShape c y + etaPolynomial eta * prefixRepair c y := by
  simp only [pulseRatio, correction_eq_affine, amplitudeShape]
  ring

theorem prefixRepair_eq_correction (c : Parameters) (y : ℝ) :
    2 * prefixRepair c y = correction c (fun _ => 0) 1 (Real.exp y) := by
  rw [correction_eq_affine]
  norm_num [etaPolynomial]

theorem amplitudeRepair_eq_correction (c : Parameters) (y : ℝ) :
    amplitudeRepair c y = correction c (fun _ => 1) 0 (Real.exp y) := by
  rw [correction_eq_affine]
  norm_num [etaPolynomial]

theorem mainPulse_mul_correction (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    mainPulse (c.lam * y) * correction c amp eta (Real.exp y) = 0 := by
  by_cases hy : y ≤ 11 / c.lam
  · rw [correction_zero_on_main_pulse c amp eta hy, mul_zero]
  · have h : 11 ≤ c.lam * y := by
      have hp := (div_lt_iff₀ c.lam_pos).mp (lt_of_not_ge hy)
      linarith
    rw [mainPulse_zero_right h, zero_mul]

theorem mainPulse_mul_amplitudeRepair (c : Parameters) (y : ℝ) :
    mainPulse (c.lam * y) * amplitudeRepair c y = 0 := by
  rw [amplitudeRepair_eq_correction]
  exact mainPulse_mul_correction c (fun _ => 1) 0 y

theorem mainPulse_mul_prefixRepair (c : Parameters) (y : ℝ) :
    mainPulse (c.lam * y) * prefixRepair c y = 0 := by
  have he := mainPulse_mul_correction c (fun _ => 0) 1 y
  rw [← prefixRepair_eq_correction] at he
  nlinarith

/-- Pulse weight, given by `Real.exp (-2 * c.lam * y)`. -/
def pulseWeight (c : Parameters) (y : ℝ) : ℝ := Real.exp (-2 * c.lam * y)

theorem pulseWeight_continuous (c : Parameters) : Continuous (pulseWeight c) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_id)

theorem pulse_rescale_integral (c : Parameters) (f : ℝ → ℝ) :
    c.lam * (∫ y in (0 : ℝ)..c.pulseLength, f (c.lam * y)) = ∫ z in (0 : ℝ)..13, f z := by
  simpa only [smul_eq_mul, mul_zero, Parameters.pulseLength, mul_div_cancel₀ _ c.lam_pos.ne'] using
    intervalIntegral.smul_integral_comp_mul_left f c.lam (a := 0) (b := c.pulseLength)

/-- Quadratic coefficient, given by `c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y *
amplitudeShape c y ^ 2`. -/
def quadraticCoefficient (c : Parameters) : ℝ :=
  c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * amplitudeShape c y ^ 2

/-- Linear coefficient, given by `2 * c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y *
amplitudeShape c y * prefixRepair c y`. -/
def linearCoefficient (c : Parameters) : ℝ :=
  2 * c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * amplitudeShape c y * prefixRepair c y

/-- Constant correction, given by `c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y *
prefixRepair c y ^ 2`. -/
def constantCorrection (c : Parameters) : ℝ :=
  c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * prefixRepair c y ^ 2

/-- Scaled pulse energy, given by `c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y *
(pulseRatio c (fun _ => A) (y, eta) ^ 2 - 1 / 2)`. -/
def scaledPulseEnergy (c : Parameters) (A eta : ℝ) : ℝ :=
  c.lam * ∫ y in (0 : ℝ)..c.pulseLength,
    pulseWeight c y * (pulseRatio c (fun _ => A) (y, eta) ^ 2 - 1 / 2)

theorem normalized_main_energy (c : Parameters) :
    c.lam * (∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * mainPulse (c.lam * y) ^ 2) =
      pulseConstant := by
  convert! pulse_rescale_integral c (fun z => Real.exp (-2 * z) * mainPulse z ^ 2) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro y _
  simp only [pulseWeight, mul_assoc]

theorem normalized_negative_energy (c : Parameters) :
    c.lam * (∫ y in (0 : ℝ)..c.pulseLength, (1 / 2 : ℝ) * pulseWeight c y) =
      RadialSchedule.pulseEnergyDebt := by
  rw [RadialSchedule.pulseEnergyDebt, ← RadialSchedule.pulse_negative_energy_integral]
  convert! pulse_rescale_integral c (fun z => (1 / 2 : ℝ) * Real.exp (-2 * z)) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro y _
  simp only [pulseWeight, mul_assoc]

theorem quadraticCoefficient_eq (c : Parameters) :
    quadraticCoefficient c = pulseConstant +
      c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * amplitudeRepair c y ^ 2 := by
  have hp : Continuous (fun y => pulseWeight c y * mainPulse (c.lam * y) ^ 2) :=
    (pulseWeight_continuous c).mul
      ((mainPulse_contDiff.continuous.comp (continuous_const.mul continuous_id)).pow 2)
  have hr : Continuous (fun y => pulseWeight c y * amplitudeRepair c y ^ 2) :=
    (pulseWeight_continuous c).mul ((amplitudeRepair_contDiff c).continuous.pow 2)
  have he : (fun y => pulseWeight c y * amplitudeShape c y ^ 2) =
      (fun y => pulseWeight c y * mainPulse (c.lam * y) ^ 2 +
        pulseWeight c y * amplitudeRepair c y ^ 2) := by
    funext y
    unfold amplitudeShape
    have hz := mainPulse_mul_amplitudeRepair c y
    nlinarith [congrArg (fun x : ℝ => pulseWeight c y * x) hz]
  unfold quadraticCoefficient
  rw [he, intervalIntegral.integral_add (hp.intervalIntegrable _ _) (hr.intervalIntegrable _ _),
    mul_add, normalized_main_energy]

theorem quadraticCoefficient_ge (c : Parameters) : pulseConstant ≤ quadraticCoefficient c := by
  rw [quadraticCoefficient_eq]
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) c.pulseLength_pos.le
    (fun y => mul_nonneg (Real.exp_pos (-2 * c.lam * y)).le (sq_nonneg (amplitudeRepair c y)))
  exact le_add_of_nonneg_right (mul_nonneg c.lam_pos.le hn)

theorem scaledPulseEnergy_eq (c : Parameters) (A eta : ℝ) :
    scaledPulseEnergy c A eta = quadraticCoefficient c * A ^ 2 +
      linearCoefficient c * etaPolynomial eta * A +
      constantCorrection c * etaPolynomial eta ^ 2 - RadialSchedule.pulseEnergyDebt := by
  have hq : Continuous (fun y => pulseWeight c y * amplitudeShape c y ^ 2) :=
    (pulseWeight_continuous c).mul ((amplitudeShape_contDiff c).continuous.pow 2)
  have hl : Continuous (fun y => pulseWeight c y * amplitudeShape c y * prefixRepair c y) :=
    ((pulseWeight_continuous c).mul (amplitudeShape_contDiff c).continuous).mul
      (prefixRepair_contDiff c).continuous
  have hc : Continuous (fun y => pulseWeight c y * prefixRepair c y ^ 2) :=
    (pulseWeight_continuous c).mul ((prefixRepair_contDiff c).continuous.pow 2)
  have hn : Continuous (fun y => (1 / 2 : ℝ) * pulseWeight c y) :=
    continuous_const.mul (pulseWeight_continuous c)
  have he : (fun y => pulseWeight c y * (pulseRatio c (fun _ => A) (y, eta) ^ 2 - 1 / 2)) =
      (fun y => A ^ 2 * (pulseWeight c y * amplitudeShape c y ^ 2) +
        (2 * etaPolynomial eta * A) * (pulseWeight c y * amplitudeShape c y * prefixRepair c y) +
        etaPolynomial eta ^ 2 * (pulseWeight c y * prefixRepair c y ^ 2) -
        (1 / 2 : ℝ) * pulseWeight c y) := by
    funext y
    rw [pulseRatio_eq_affine]
    ring
  unfold scaledPulseEnergy
  rw [he, intervalIntegral.integral_sub
    ((((continuous_const.fun_mul hq).fun_add (continuous_const.fun_mul hl)).fun_add
      (continuous_const.fun_mul hc)).intervalIntegrable _ _)
      (hn.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add
    (((continuous_const.fun_mul hq).fun_add (continuous_const.fun_mul hl)).intervalIntegrable _ _)
    ((continuous_const.fun_mul hc).intervalIntegrable _ _),
    intervalIntegral.integral_add ((continuous_const.fun_mul hq).intervalIntegrable _ _)
      ((continuous_const.fun_mul hl).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul]
  have hn' := normalized_negative_energy c
  simp only [intervalIntegral.integral_const_mul] at hn'
  unfold quadraticCoefficient linearCoefficient constantCorrection
  nlinarith

/-! ## Exact prefix coefficients and uniform bounds -/

/-- Core energy weight, given by `Real.exp y * radialAmplitude c.P c.dropLength c.lam y ^ 2`. -/
def coreEnergyWeight (c : Parameters) (y : ℝ) : ℝ :=
  Real.exp y * radialAmplitude c.P c.dropLength c.lam y ^ 2

/-- Normalization, given by `Real.exp c.pulseStart * pulseAmplitude c ^ 2`. -/
def normalization (c : Parameters) : ℝ := Real.exp c.pulseStart * pulseAmplitude c ^ 2

theorem normalization_pos (c : Parameters) : 0 < normalization c :=
  mul_pos (Real.exp_pos _) (sq_pos_of_pos (pulseAmplitude_pos c))

theorem coreEnergyWeight_nonneg (c : Parameters) (y : ℝ) : 0 ≤ coreEnergyWeight c y :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem coreEnergyWeight_contDiff (c : Parameters) : ContDiff ℝ ∞ (coreEnergyWeight c) :=
  Real.contDiff_exp.mul ((radialAmplitude_contDiff _ _ _).pow 2)

theorem coreEnergyWeight_hasDerivAt (c : Parameters) (y : ℝ) :
    HasDerivAt (coreEnergyWeight c) (2 * slope c.dropLength c.lam y * coreEnergyWeight c y) y := by
  convert! (Real.hasDerivAt_exp y).fun_mul ((radialAmplitude_hasDerivAt c.P c.dropLength c.lam
      y).fun_pow 2)
    using 1
  simp only [coreEnergyWeight]
  ring

theorem slope_ge_neg_lambda (c : Parameters) (y : ℝ) : -c.lam ≤ slope c.dropLength c.lam y := by
  have h0 := sigma_nonneg y
  have h1 := sigma_le_one y
  have h2 := sigma_le_one (y - (c.dropLength + 1))
  unfold OutgoingSchedule.slope
  nlinarith [c.lam_pos]

theorem weightedCore_monotone (c : Parameters) :
    Monotone (fun y => coreEnergyWeight c y * Real.exp (2 * c.lam * y)) := by
  have hd : ∀ y, HasDerivAt (fun y => coreEnergyWeight c y * Real.exp (2 * c.lam * y))
      (2 * (slope c.dropLength c.lam y + c.lam) *
        (coreEnergyWeight c y * Real.exp (2 * c.lam * y))) y := by
    intro y
    convert! (coreEnergyWeight_hasDerivAt c y).mul
      (((hasDerivAt_id y).const_mul (2 * c.lam)).exp) using 1
    simp only [id_eq]
    ring
  apply monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
  intro y
  rw [(hd y).deriv]
  exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [slope_ge_neg_lambda c y]))
    (mul_nonneg (coreEnergyWeight_nonneg c y) (Real.exp_pos _).le)

theorem prefix_weight_bound (c : Parameters) {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ c.pulseStart) :
    coreEnergyWeight c y ≤ normalization c * Real.exp (2 * c.lam * c.pulseStart) := by
  have hm := weightedCore_monotone c hy'
  have he : 1 ≤ Real.exp (2 * c.lam * y) := Real.one_le_exp
    (mul_nonneg (mul_nonneg (by norm_num) c.lam_pos.le) hy)
  exact (le_mul_of_one_le_right (coreEnergyWeight_nonneg c y) he).trans hm

theorem initial_weight_bound (c : Parameters) :
    c.P ^ 2 ≤ normalization c * Real.exp (2 * c.lam * c.pulseStart) := by
  have h := prefix_weight_bound c (y := 0) le_rfl c.pulseStart_pos.le
  simpa [coreEnergyWeight, radialAmplitude, logAmplitude, primitive] using h

/-- Prefix axial energy, given by `16 + ∫ y in (0 : ℝ)..c.pulseStart, Real.exp y *
dropCoefficient c.m y ^ 2`. -/
def prefixAxialEnergy (c : Parameters) : ℝ :=
  16 + ∫ y in (0 : ℝ)..c.pulseStart, Real.exp y * dropCoefficient c.m y ^ 2

/-- Prefix angular energy, given by `(5 / 12) * c.P ^ 2 + ∫ y in (0 : ℝ)..c.pulseStart,
coreEnergyWeight c y / 2`. -/
def prefixAngularEnergy (c : Parameters) : ℝ :=
  (5 / 12) * c.P ^ 2 + ∫ y in (0 : ℝ)..c.pulseStart, coreEnergyWeight c y / 2

/-- Prefix energy, given by `prefixAxialEnergy c * eta ^ 2 - prefixAngularEnergy c * shape eta ^
2`. -/
def prefixEnergy (c : Parameters) (eta : ℝ) : ℝ :=
  prefixAxialEnergy c * eta ^ 2 - prefixAngularEnergy c * shape eta ^ 2

theorem prefixAngularEnergy_bound (c : Parameters) :
    prefixAngularEnergy c ≤ (5 / 12 + c.pulseStart / 2) *
      (normalization c * Real.exp (2 * c.lam * c.pulseStart)) := by
  have hm := intervalIntegral.integral_mono_on (μ := volume) c.pulseStart_pos.le
    (((coreEnergyWeight_contDiff c).continuous.div_const 2).intervalIntegrable 0 c.pulseStart)
    (continuous_const.intervalIntegrable 0 c.pulseStart)
    (fun y hy => div_le_div_of_nonneg_right (prefix_weight_bound c hy.1 hy.2) (by norm_num))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
  unfold prefixAngularEnergy
  nlinarith [initial_weight_bound c]

theorem prefixAxialEnergy_bound (c : Parameters) :
    prefixAxialEnergy c ≤ 16 * Real.exp (Real.exp c.m) := by
  let L := Real.exp c.m
  have hL : 0 ≤ L := (Real.exp_pos _).le
  have hLB : L ≤ c.pulseStart := by
    have h := c.pulseStart_ge_hold
    dsimp [Parameters.holdStart, Parameters.dropLength, L] at *
    linarith
  have hc : Continuous (fun y => Real.exp y * dropCoefficient c.m y ^ 2) :=
    Real.continuous_exp.mul ((dropCoefficient_contDiff c.m_pos).continuous.pow 2)
  have hz : (∫ y in L..c.pulseStart, Real.exp y * dropCoefficient c.m y ^ 2) = 0 := by
    calc
      _ = ∫ _y in L..c.pulseStart, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        change Real.exp y * dropCoefficient c.m y ^ 2 = 0
        rw [dropCoefficient_late c.m_pos ((uIcc_of_le hLB ▸ hy).1)]
        ring
      _ = 0 := by simp
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 L) (hc.intervalIntegrable L c.pulseStart)
  have hm := intervalIntegral.integral_mono_on (μ := volume) (g := fun y => 16 * Real.exp y)
    hL (hc.intervalIntegrable 0 L)
    ((continuous_const.mul Real.continuous_exp).intervalIntegrable 0 L)
    (fun y _ => by
      have hb := dropCoefficient_bounds c.m y
      nlinarith [mul_nonneg (Real.exp_pos y).le
        (show 0 ≤ 16 - dropCoefficient c.m y ^ 2 by nlinarith)])
  rw [intervalIntegral.integral_const_mul, integral_exp] at hm
  simp only [Real.exp_zero] at hm
  rw [hz, add_zero] at hs
  unfold prefixAxialEnergy
  rw [← hs]
  linarith

/-! ## The complete outgoing energy is an actual improper integral -/

/-- Energy integrand, given by `Real.exp y * (axial d.core (fun _ => A) (y, eta) ^ 2 -
OutgoingTail.finalAngular d (y, eta) ^ 2 / 2)`. -/
def energyIntegrand (d : OutgoingTail.TailData) (A eta y : ℝ) : ℝ :=
  Real.exp y * (axial d.core (fun _ => A) (y, eta) ^ 2 -
    OutgoingTail.finalAngular d (y, eta) ^ 2 / 2)

/-- Total energy, given by `∫ y, energyIntegrand d A eta y`. -/
def totalEnergy (d : OutgoingTail.TailData) (A eta : ℝ) : ℝ :=
  ∫ y, energyIntegrand d A eta y

/-- Tail energy, given by `∫ y in Ioi d.core.endpoint, Real.exp y * OutgoingTail.finalAngular d
(y, eta) ^ 2`. -/
def tailEnergy (d : OutgoingTail.TailData) (eta : ℝ) : ℝ :=
  ∫ y in Ioi d.core.endpoint, Real.exp y * OutgoingTail.finalAngular d (y, eta) ^ 2

theorem energyIntegrand_continuous (d : OutgoingTail.TailData) (A eta : ℝ) :
    Continuous (energyIntegrand d A eta) :=
  Real.continuous_exp.mul (((axial_radial_contDiff d.core (fun _ => A) eta).continuous.pow 2).sub
    ((((OutgoingTail.finalAngular_contDiff d).comp
      (contDiff_id.prodMk contDiff_const)).continuous.pow 2).div_const 2))

theorem coreEndpoint_pos (c : Parameters) : 0 < c.endpoint := by
  unfold Parameters.endpoint
  linarith [c.pulseStart_pos, c.pulseLength_pos]

theorem pulseStart_le_endpoint (c : Parameters) : c.pulseStart ≤ c.endpoint := by
  unfold Parameters.endpoint
  linarith [c.pulseLength_pos]

theorem energyIntegrand_ideal (d : OutgoingTail.TailData) (A eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    energyIntegrand d A eta y = 16 * eta ^ 2 * Real.exp y -
      (d.core.P ^ 2 * shape eta ^ 2 / 2) * Real.exp ((6 / 5) * y) := by
  unfold energyIntegrand
  rw [axial_ideal d.core (fun _ => A) eta hy,
    OutgoingTail.finalAngular_before d eta (hy.trans (coreEndpoint_pos d.core).le),
    angular_ideal d.core.dropLength_pos.le hy]
  have he : Real.exp y * Real.exp (y / 10) ^ 2 = Real.exp ((6 / 5) * y) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 16 * eta ^ 2 * Real.exp y -
        (d.core.P ^ 2 * shape eta ^ 2 / 2) * (Real.exp y * Real.exp (y / 10) ^ 2) := by ring
    _ = _ := by rw [he]

theorem energyIntegrand_integrable_ideal (d : OutgoingTail.TailData) (A eta : ℝ) :
    IntegrableOn (energyIntegrand d A eta) (Iic 0) := by
  refine IntegrableOn.congr_fun (s := Iic (0 : ℝ))
    (((integrableOn_exp_Iic 0).const_mul (16 * eta ^ 2)).sub
    ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 6 / 5) 0).const_mul
      (d.core.P ^ 2 * shape eta ^ 2 / 2))) ?_ measurableSet_Iic
  intro y hy
  exact (energyIntegrand_ideal d A eta hy).symm

theorem energyIntegrand_integral_ideal (d : OutgoingTail.TailData) (A eta : ℝ) :
    (∫ y in Iic 0, energyIntegrand d A eta y) =
      16 * eta ^ 2 - (5 / 12) * d.core.P ^ 2 * shape eta ^ 2 := by
  have he : (∫ y in Iic 0, energyIntegrand d A eta y) =
      ∫ y in Iic 0, 16 * eta ^ 2 * Real.exp y -
        (d.core.P ^ 2 * shape eta ^ 2 / 2) * Real.exp ((6 / 5) * y) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro y hy
    exact energyIntegrand_ideal d A eta hy
  rw [he, integral_sub ((integrableOn_exp_Iic 0).const_mul _)
    ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 6 / 5) 0).const_mul _),
    integral_const_mul, integral_const_mul, integral_exp_Iic_zero,
    integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 6 / 5) 0]
  norm_num
  ring

theorem energyIntegrand_prefix (d : OutgoingTail.TailData) (A eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.pulseStart) :
    energyIntegrand d A eta y =
      eta ^ 2 * (Real.exp y * dropCoefficient d.core.m y ^ 2) -
        shape eta ^ 2 * (coreEnergyWeight d.core y / 2) := by
  unfold energyIntegrand
  rw [axial_before_pulse d.core (fun _ => A) eta hy,
    OutgoingTail.finalAngular_before d eta (hy.trans (pulseStart_le_endpoint d.core))]
  unfold angular coreEnergyWeight
  ring

theorem energyIntegrand_integrable_Iic (d : OutgoingTail.TailData) (A eta : ℝ) {b : ℝ}
    (hb : 0 ≤ b) : IntegrableOn (energyIntegrand d A eta) (Iic b) := by
  rw [← Iic_union_Ioc_eq_Iic hb]
  exact (energyIntegrand_integrable_ideal d A eta).union
    (energyIntegrand_continuous d A eta).integrableOn_Ioc

theorem energyIntegrand_integral_prefix (d : OutgoingTail.TailData) (A eta : ℝ) :
    (∫ y in Iic d.core.pulseStart, energyIntegrand d A eta y) = prefixEnergy d.core eta := by
  have hfin : (∫ y in (0 : ℝ)..d.core.pulseStart, energyIntegrand d A eta y) =
      eta ^ 2 * (∫ y in (0 : ℝ)..d.core.pulseStart, Real.exp y * dropCoefficient d.core.m y ^ 2) -
        shape eta ^ 2 * (∫ y in (0 : ℝ)..d.core.pulseStart, coreEnergyWeight d.core y / 2) := by
    calc
      _ = ∫ y in (0 : ℝ)..d.core.pulseStart,
          eta ^ 2 * (Real.exp y * dropCoefficient d.core.m y ^ 2) -
            shape eta ^ 2 * (coreEnergyWeight d.core y / 2) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact energyIntegrand_prefix d A eta ((uIcc_of_le d.core.pulseStart_pos.le ▸ hy).2)
      _ = _ := by
        rw [intervalIntegral.integral_sub
          ((continuous_const.fun_mul (Real.continuous_exp.fun_mul
            ((dropCoefficient_contDiff d.core.m_pos).continuous.fun_pow 2))).intervalIntegrable _ _)
          ((continuous_const.fun_mul ((coreEnergyWeight_contDiff d.core).continuous.div_const
              2)).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hs := intervalIntegral.integral_Iic_sub_Iic
    (energyIntegrand_integrable_ideal d A eta)
    (energyIntegrand_integrable_Iic d A eta d.core.pulseStart_pos.le)
  rw [energyIntegrand_integral_ideal, hfin] at hs
  unfold prefixEnergy prefixAxialEnergy prefixAngularEnergy
  linarith

theorem energyIntegrand_pulse (d : OutgoingTail.TailData) (A eta : ℝ) {y : ℝ}
    (hy : d.core.pulseStart ≤ y) (hy' : y ≤ d.core.endpoint) :
    energyIntegrand d A eta y = normalization d.core * shape eta ^ 2 *
      (pulseWeight d.core (y - d.core.pulseStart) *
        (pulseRatio d.core (fun _ => A) (y - d.core.pulseStart, eta) ^ 2 - 1 / 2)) := by
  unfold energyIntegrand
  rw [axial_pulse d.core (fun _ => A) eta hy, radialPulse_exp,
    OutgoingTail.finalAngular_before d eta hy', angular_pulse d.core eta hy]
  have he : Real.exp y * Real.exp (-(1 / 2 + d.core.lam) * (y - d.core.pulseStart)) ^ 2 =
      Real.exp d.core.pulseStart * pulseWeight d.core (y - d.core.pulseStart) := by
    unfold pulseWeight
    rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold normalization
  calc
    _ = pulseAmplitude d.core ^ 2 * shape eta ^ 2 *
        (pulseRatio d.core (fun _ => A) (y - d.core.pulseStart, eta) ^ 2 - 1 / 2) *
          (Real.exp y * Real.exp (-(1 / 2 + d.core.lam) * (y - d.core.pulseStart)) ^ 2) := by ring
    _ = _ := by rw [he]; ring

theorem energyIntegrand_integral_pulse (d : OutgoingTail.TailData) (A eta : ℝ) :
    (∫ y in d.core.pulseStart..d.core.endpoint, energyIntegrand d A eta y) =
      normalization d.core * shape eta ^ 2 / d.core.lam * scaledPulseEnergy d.core A eta := by
  calc
    _ = ∫ y in d.core.pulseStart..d.core.endpoint,
        normalization d.core * shape eta ^ 2 *
          (pulseWeight d.core (y - d.core.pulseStart) *
            (pulseRatio d.core (fun _ => A) (y - d.core.pulseStart, eta) ^ 2 - 1 / 2)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hm := uIcc_of_le (pulseStart_le_endpoint d.core) ▸ hy
      exact energyIntegrand_pulse d A eta hm.1 hm.2
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right
          (fun t => pulseWeight d.core t * (pulseRatio d.core (fun _ => A) (t, eta) ^ 2 - 1 / 2))]
      simp only [Parameters.endpoint, sub_self, add_sub_cancel_left]
      unfold scaledPulseEnergy
      field_simp [d.core.lam_pos.ne']; ring_nf

theorem energyIntegrand_late (d : OutgoingTail.TailData) (A eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) :
    energyIntegrand d A eta y = -(Real.exp y * OutgoingTail.finalAngular d (y, eta) ^ 2) / 2 := by
  unfold energyIntegrand
  rw [axial_after_pulse d.core (fun _ => A) eta hy]
  ring

theorem totalEnergy_eq_of_integrable (d : OutgoingTail.TailData) (A eta : ℝ)
    (htail : IntegrableOn (fun y => Real.exp y * OutgoingTail.finalAngular d (y, eta) ^ 2)
      (Ioi d.core.endpoint)) :
    totalEnergy d A eta = prefixEnergy d.core eta +
      normalization d.core * shape eta ^ 2 / d.core.lam * scaledPulseEnergy d.core A eta -
        tailEnergy d eta / 2 := by
  have hlate : IntegrableOn (energyIntegrand d A eta) (Ioi d.core.endpoint) := by
    refine IntegrableOn.congr_fun (s := Ioi d.core.endpoint) (htail.neg.div_const 2) ?_
        measurableSet_Ioi
    intro y hy
    exact (energyIntegrand_late d A eta hy.le).symm
  have hI : (∫ y in Ioi d.core.endpoint, energyIntegrand d A eta y) = -tailEnergy d eta / 2 := by
    calc
      _ = ∫ y in Ioi d.core.endpoint, -(Real.exp y * OutgoingTail.finalAngular d (y, eta) ^ 2) / 2
          := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        exact energyIntegrand_late d A eta hy.le
      _ = _ := by rw [integral_div, integral_neg]; rfl
  have hs := intervalIntegral.integral_Iic_sub_Iic
    (energyIntegrand_integrable_Iic d A eta d.core.pulseStart_pos.le)
    (energyIntegrand_integrable_Iic d A eta (coreEndpoint_pos d.core).le)
  rw [energyIntegrand_integral_prefix, energyIntegrand_integral_pulse] at hs
  unfold totalEnergy
  rw [← intervalIntegral.integral_Iic_add_Ioi
    (energyIntegrand_integrable_Iic d A eta (coreEndpoint_pos d.core).le) hlate, hI]
  linarith

theorem tailEnergy_eq (d : OutgoingTail.TailData) (eta : ℝ) :
    tailEnergy d eta = TailEnergyBounds.postPulseEnergy d eta := rfl

theorem tailEnergy_contDiff (d : OutgoingTail.TailData) : ContDiff ℝ ∞ (tailEnergy d) :=
  TailEnergyBounds.postPulseEnergy_contDiff d

theorem totalEnergy_eq (d : OutgoingTail.TailData) (A eta : ℝ) :
    totalEnergy d A eta = prefixEnergy d.core eta +
      normalization d.core * shape eta ^ 2 / d.core.lam * scaledPulseEnergy d.core A eta -
        tailEnergy d eta / 2 :=
  totalEnergy_eq_of_integrable d A eta (TailEnergyBounds.energyDensity_integrable_postPulse d eta)

/-- Normalized prefix axial, given by `c.lam * prefixAxialEnergy c / normalization c`. -/
def normalizedPrefixAxial (c : Parameters) : ℝ := c.lam * prefixAxialEnergy c / normalization c
/-- Normalized prefix angular, given by `c.lam * prefixAngularEnergy c / normalization c`. -/
def normalizedPrefixAngular (c : Parameters) : ℝ := c.lam * prefixAngularEnergy c / normalization c
/-- Normalized tail, given by `d.core.lam * tailEnergy d eta / (2 * normalization d.core * shape
eta ^ 2)`. -/
def normalizedTail (d : OutgoingTail.TailData) (eta : ℝ) : ℝ :=
  d.core.lam * tailEnergy d eta / (2 * normalization d.core * shape eta ^ 2)

/-- Linear term, given by `linearCoefficient c * etaPolynomial eta`. -/
def linearTerm (c : Parameters) (eta : ℝ) : ℝ := linearCoefficient c * etaPolynomial eta
/-- Constant term as an element of `ℝ`. -/
def constantTerm (d : OutgoingTail.TailData) (eta : ℝ) : ℝ :=
  (constantCorrection d.core + normalizedPrefixAxial d.core) * etaPolynomial eta ^ 2 -
    RadialSchedule.pulseEnergyDebt - normalizedPrefixAngular d.core - normalizedTail d eta

/-- Energy polynomial, given by `quadraticCoefficient d.core * A ^ 2 + linearTerm d.core eta * A
+ constantTerm d eta`. -/
def energyPolynomial (d : OutgoingTail.TailData) (A eta : ℝ) : ℝ :=
  quadraticCoefficient d.core * A ^ 2 + linearTerm d.core eta * A + constantTerm d eta

theorem totalEnergy_normalized (d : OutgoingTail.TailData) (A eta : ℝ) :
    d.core.lam * totalEnergy d A eta / (normalization d.core * shape eta ^ 2) =
      energyPolynomial d A eta := by
  have hN := (normalization_pos d.core).ne'
  have hf := (shape_pos eta).ne'
  have hq : eta ^ 2 = shape eta ^ 2 * etaPolynomial eta ^ 2 := by
    unfold shape etaPolynomial
    field_simp [show (1 + eta ^ 2 : ℝ) ≠ 0 by positivity]
  have hpre : d.core.lam * prefixEnergy d.core eta / (normalization d.core * shape eta ^ 2) =
      normalizedPrefixAxial d.core * etaPolynomial eta ^ 2 - normalizedPrefixAngular d.core := by
    unfold prefixEnergy normalizedPrefixAxial normalizedPrefixAngular
    rw [hq]
    field_simp [hN, hf]
  rw [totalEnergy_eq]
  calc
    _ = scaledPulseEnergy d.core A eta +
        d.core.lam * prefixEnergy d.core eta / (normalization d.core * shape eta ^ 2) -
        d.core.lam * tailEnergy d eta / (2 * normalization d.core * shape eta ^ 2) := by
      field_simp [hN, hf, d.core.lam_pos.ne']; ring
    _ = _ := by
      rw [hpre, scaledPulseEnergy_eq]
      unfold energyPolynomial linearTerm constantTerm normalizedTail
      ring

theorem etaPolynomial_contDiff : ContDiff ℝ ∞ etaPolynomial :=
  contDiff_id.mul (contDiff_const.add (contDiff_id.pow 2))

theorem normalizedTail_contDiff (d : OutgoingTail.TailData) : ContDiff ℝ ∞ (normalizedTail d) :=
  (contDiff_const.mul (tailEnergy_contDiff d)).div
    (contDiff_const.mul (shape_contDiff.pow 2)) (fun eta => by
      exact ne_of_gt (mul_pos (mul_pos (by norm_num) (normalization_pos d.core))
        (sq_pos_of_pos (shape_pos eta))))

theorem linearTerm_contDiff (c : Parameters) : ContDiff ℝ ∞ (linearTerm c) :=
  contDiff_const.mul etaPolynomial_contDiff

theorem constantTerm_contDiff (d : OutgoingTail.TailData) : ContDiff ℝ ∞ (constantTerm d) :=
  (((contDiff_const.mul (etaPolynomial_contDiff.pow 2)).sub contDiff_const).sub
    contDiff_const).sub (normalizedTail_contDiff d)

/-- A globally smooth extension of a negative constant coefficient. It
agrees with the original coefficient below `-1/5`; the physical parameter
band will be proved to lie strictly in that region. -/
def negativeClamp (x : ℝ) : ℝ :=
  (1 - sigma (10 * (x + 1 / 5))) * x - sigma (10 * (x + 1 / 5)) / 10

theorem negativeClamp_contDiff : ContDiff ℝ ∞ negativeClamp :=
  ((contDiff_const.sub (sigma_contDiff.comp (contDiff_const.mul
    (contDiff_id.add contDiff_const)))).mul contDiff_id).sub
      ((sigma_contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const))).div_const 10)

theorem negativeClamp_eq {x : ℝ} (hx : x ≤ -(1 / 5)) : negativeClamp x = x := by
  unfold negativeClamp
  rw [sigma_zero (by linarith : 10 * (x + 1 / 5) ≤ 0)]
  ring

theorem negativeClamp_le (x : ℝ) : negativeClamp x ≤ -(1 / 10) := by
  by_cases hx : x ≤ -(1 / 10)
  · have h0 := sigma_nonneg (10 * (x + 1 / 5))
    have h1 := sigma_le_one (10 * (x + 1 / 5))
    unfold negativeClamp
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ -(1 / 10) - x by linarith)]
  · simp only [negativeClamp, sigma_one (by linarith : 1 ≤ 10 * (x + 1 / 5))]
    norm_num

theorem negativeClamp_neg (x : ℝ) : negativeClamp x < 0 :=
  lt_of_le_of_lt (negativeClamp_le x) (by norm_num)

/-- Discriminant, given by `linearTerm d.core eta ^ 2 - 4 * quadraticCoefficient d.core *
negativeClamp (constantTerm d eta)`. -/
def discriminant (d : OutgoingTail.TailData) (eta : ℝ) : ℝ :=
  linearTerm d.core eta ^ 2 -
    4 * quadraticCoefficient d.core * negativeClamp (constantTerm d eta)

theorem quadraticCoefficient_pos (c : Parameters) : 0 < quadraticCoefficient c :=
  lt_of_lt_of_le (lt_trans (by norm_num) pulseConstant_lower) (quadraticCoefficient_ge c)

theorem discriminant_pos (d : OutgoingTail.TailData) (eta : ℝ) : 0 < discriminant d eta := by
  unfold discriminant
  have hp := quadraticCoefficient_pos d.core
  have hn := negativeClamp_neg (constantTerm d eta)
  nlinarith [sq_nonneg (linearTerm d.core eta), mul_neg_of_pos_of_neg hp hn]

/-- A globally C∞ amplitude. The negative clamp only extends the formula
outside the physical parameter band; the theorem below proves its exact
agreement with the actual energy equation where the coefficient is small. -/
def amplitude (d : OutgoingTail.TailData) (eta : ℝ) : ℝ :=
  (-linearTerm d.core eta + Real.sqrt (discriminant d eta)) / (2 * quadraticCoefficient d.core)

theorem amplitude_contDiff (d : OutgoingTail.TailData) : ContDiff ℝ ∞ (amplitude d) := by
  have hd : ContDiff ℝ ∞ (discriminant d) :=
    ((linearTerm_contDiff d.core).pow 2).sub (contDiff_const.mul
      (negativeClamp_contDiff.comp (constantTerm_contDiff d)))
  exact ((linearTerm_contDiff d.core).neg.add
    (hd.sqrt (fun eta => (discriminant_pos d eta).ne'))).div_const _

theorem amplitude_pos (d : OutgoingTail.TailData) (eta : ℝ) : 0 < amplitude d eta := by
  have ha := quadraticCoefficient_pos d.core
  have hc := negativeClamp_neg (constantTerm d eta)
  have hd := Real.sq_sqrt (discriminant_pos d eta).le
  have hs := Real.sqrt_nonneg (discriminant d eta)
  have hb : linearTerm d.core eta < Real.sqrt (discriminant d eta) := by
    dsimp only [discriminant] at hd hs ⊢
    nlinarith [mul_neg_of_pos_of_neg ha hc]
  exact div_pos (by linarith) (mul_pos (by norm_num) ha)

theorem amplitude_clamped_equation (d : OutgoingTail.TailData) (eta : ℝ) :
    quadraticCoefficient d.core * amplitude d eta ^ 2 +
      linearTerm d.core eta * amplitude d eta + negativeClamp (constantTerm d eta) = 0 := by
  have hs := Real.sq_sqrt (discriminant_pos d eta).le
  have hp : Real.sqrt (discriminant d eta) ^ 2 - linearTerm d.core eta ^ 2 +
      4 * quadraticCoefficient d.core * negativeClamp (constantTerm d eta) = 0 := by
    rw [hs]
    unfold discriminant
    ring
  unfold amplitude
  field_simp [(quadraticCoefficient_pos d.core).ne']
  linear_combination hp

theorem amplitude_energy_equation (d : OutgoingTail.TailData) (eta : ℝ)
    (hc : constantTerm d eta ≤ -(1 / 5)) : energyPolynomial d (amplitude d eta) eta = 0 := by
  have h := amplitude_clamped_equation d eta
  rwa [negativeClamp_eq hc] at h

theorem amplitude_totalEnergy_zero (d : OutgoingTail.TailData) (eta : ℝ)
    (hc : constantTerm d eta ≤ -(1 / 5)) : totalEnergy d (amplitude d eta) eta = 0 := by
  have h := totalEnergy_normalized d (amplitude d eta) eta
  rw [amplitude_energy_equation d eta hc] at h
  have hmul := (div_eq_zero_iff).mp h
  rcases hmul with hmul | hz
  · exact (mul_eq_zero.mp hmul).resolve_left d.core.lam_pos.ne'
  · exact False.elim ((mul_pos (normalization_pos d.core) (sq_pos_of_pos (shape_pos eta))).ne' hz)

/-! ## Actual coefficient estimates for the paper's wait duration -/

/-- Logarithmic rate, given by `lam * (1 + Real.log (1 / lam))`. -/
def logarithmicRate (lam : ℝ) : ℝ := lam * (1 + Real.log (1 / lam))

theorem log_inverse_nonneg (c : Parameters) : 0 ≤ Real.log (1 / c.lam) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ c.lam_pos).mpr
  linarith [c.lam_lt]

theorem logarithmicRate_pos (c : Parameters) : 0 < logarithmicRate c.lam :=
  mul_pos c.lam_pos (by linarith [log_inverse_nonneg c])

theorem lambda_le_logarithmicRate (c : Parameters) : c.lam ≤ logarithmicRate c.lam := by
  unfold logarithmicRate
  nlinarith [mul_nonneg c.lam_pos.le (log_inverse_nonneg c)]

theorem prefixAxialEnergy_nonneg (c : Parameters) : 0 ≤ prefixAxialEnergy c := by
  have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume) c.pulseStart_pos.le
    (fun y => mul_nonneg (Real.exp_pos y).le (sq_nonneg (dropCoefficient c.m y)))
  unfold prefixAxialEnergy
  linarith

theorem prefixAngularEnergy_nonneg (c : Parameters) : 0 ≤ prefixAngularEnergy c := by
  have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume) c.pulseStart_pos.le
    (fun y => div_nonneg (coreEnergyWeight_nonneg c y) (by norm_num : (0 : ℝ) ≤ 2))
  unfold prefixAngularEnergy
  nlinarith [sq_nonneg c.P]

theorem normalizedPrefix_nonneg (c : Parameters) :
    0 ≤ normalizedPrefixAxial c ∧ 0 ≤ normalizedPrefixAngular c :=
  ⟨div_nonneg (mul_nonneg c.lam_pos.le (prefixAxialEnergy_nonneg c)) (normalization_pos c).le,
    div_nonneg (mul_nonneg c.lam_pos.le (prefixAngularEnergy_nonneg c)) (normalization_pos c).le⟩

theorem normalizedPrefix_bound_raw (c : Parameters) :
    normalizedPrefixAxial c + normalizedPrefixAngular c ≤
      c.lam * Real.exp (2 * c.lam * c.pulseStart) *
        (16 * Real.exp (Real.exp c.m) / c.P ^ 2 + 5 / 12 + c.pulseStart / 2) := by
  have hN := normalization_pos c
  have hP := sq_pos_of_pos c.P_pos
  have hinv : 1 / normalization c ≤ Real.exp (2 * c.lam * c.pulseStart) / c.P ^ 2 := by
    apply (div_le_div_iff₀ hN hP).mpr
    simpa only [one_mul, mul_one, mul_comm] using initial_weight_bound c
  have hax : prefixAxialEnergy c / normalization c ≤
      (16 * Real.exp (Real.exp c.m)) * (Real.exp (2 * c.lam * c.pulseStart) / c.P ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul (prefixAxialEnergy_bound c) hinv (by positivity)
        (show 0 ≤ 16 * Real.exp (Real.exp c.m) by positivity)
  have hang : prefixAngularEnergy c / normalization c ≤
      (5 / 12 + c.pulseStart / 2) * Real.exp (2 * c.lam * c.pulseStart) := by
    apply (div_le_iff₀ hN).mpr
    convert! prefixAngularEnergy_bound c using 1
    ring
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hax hang) c.lam_pos.le
  unfold normalizedPrefixAxial normalizedPrefixAngular
  convert! hsum using 1 <;> ring

/-- Prefix bound constant, given by `Real.exp ((Real.exp m + 12) / 5 + 120) * (16 * Real.exp
(Real.exp m) / P ^ 2 + 5 / 12 + (Real.exp m + 12) / 2 + 30)`. -/
def prefixBoundConstant (P m : ℝ) : ℝ :=
  Real.exp ((Real.exp m + 12) / 5 + 120) *
    (16 * Real.exp (Real.exp m) / P ^ 2 + 5 / 12 + (Real.exp m + 12) / 2 + 30)

theorem prefixBoundConstant_pos (P m : ℝ) : 0 < prefixBoundConstant P m := by
  unfold prefixBoundConstant
  positivity

theorem wait_exponential_bound (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) :
    Real.exp (2 * c.lam * c.pulseStart) ≤ Real.exp ((Real.exp c.m + 12) / 5 + 120) := by
  have hl := Real.log_le_sub_one_of_pos (one_div_pos.mpr c.lam_pos)
  have hm := mul_le_mul_of_nonneg_left hl c.lam_pos.le
  have hc : c.lam * (1 / c.lam - 1) = 1 - c.lam := by field_simp [c.lam_pos.ne']
  rw [hc] at hm
  have hb : c.pulseStart = Real.exp c.m + 12 + 60 * Real.log (1 / c.lam) := by
    simp only [Parameters.pulseStart, Parameters.holdStart, Parameters.dropLength, hwait]
    ring
  apply Real.exp_le_exp.mpr
  rw [hb]
  nlinarith [c.lam_pos, mul_nonneg (show 0 ≤ Real.exp c.m + 12 by positivity)
    (show 0 ≤ 1 / 10 - c.lam by linarith [c.lam_lt])]

theorem normalizedPrefix_bound (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) :
    normalizedPrefixAxial c + normalizedPrefixAngular c ≤
      prefixBoundConstant c.P c.m * logarithmicRate c.lam := by
  have hb : c.pulseStart = Real.exp c.m + 12 + 60 * Real.log (1 / c.lam) := by
    simp only [Parameters.pulseStart, Parameters.holdStart, Parameters.dropLength, hwait]
    ring
  let F := 16 * Real.exp (Real.exp c.m) / c.P ^ 2 + 5 / 12 + (Real.exp c.m + 12) / 2 + 30
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfac : 16 * Real.exp (Real.exp c.m) / c.P ^ 2 + 5 / 12 + c.pulseStart / 2 ≤
      F * (1 + Real.log (1 / c.lam)) := by
    rw [hb]
    dsimp [F]
    nlinarith [mul_nonneg (show 0 ≤ 16 * Real.exp (Real.exp c.m) / c.P ^ 2 +
      5 / 12 + (Real.exp c.m + 12) / 2 by positivity) (log_inverse_nonneg c)]
  calc
    normalizedPrefixAxial c + normalizedPrefixAngular c ≤
        c.lam * Real.exp (2 * c.lam * c.pulseStart) *
          (16 * Real.exp (Real.exp c.m) / c.P ^ 2 + 5 / 12 + c.pulseStart / 2) :=
      normalizedPrefix_bound_raw c
    _ ≤ c.lam * Real.exp ((Real.exp c.m + 12) / 5 + 120) *
        (F * (1 + Real.log (1 / c.lam))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (wait_exponential_bound c hwait) c.lam_pos.le
      · exact hfac
      · exact add_nonneg (add_nonneg (div_nonneg (by positivity) (sq_nonneg _))
          (by norm_num)) (div_nonneg c.pulseStart_pos.le (by norm_num))
      · exact mul_nonneg c.lam_pos.le (Real.exp_pos _).le
    _ = prefixBoundConstant c.P c.m * logarithmicRate c.lam := by
      dsimp [prefixBoundConstant, logarithmicRate, F]
      ring

theorem normalizedTail_nonneg (d : OutgoingTail.TailData) (eta : ℝ) : 0 ≤ normalizedTail d eta := by
  apply div_nonneg
  · exact mul_nonneg d.core.lam_pos.le (TailEnergyBounds.postPulseEnergy_nonneg d eta)
  · exact mul_nonneg (mul_nonneg (by norm_num) (normalization_pos d.core).le) (sq_nonneg _)

theorem normalizedTail_bound (d : OutgoingTail.TailData) (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    normalizedTail d eta ≤ (TailEnergyBounds.tailConstant / 2) * logarithmicRate d.core.lam := by
  have h := TailEnergyBounds.normalized_postPulseEnergy_le d eta heta
  unfold normalizedTail logarithmicRate normalization
  change d.core.lam * TailEnergyBounds.postPulseEnergy d eta /
    (2 * (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2) * shape eta ^ 2) ≤ _
  calc
    _ = (d.core.lam * TailEnergyBounds.postPulseEnergy d eta /
      (Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2 * shape eta ^ 2)) / 2 := by ring
    _ ≤ (TailEnergyBounds.tailConstant * d.core.lam * (1 + Real.log (1 / d.core.lam))) / 2 := by
      exact div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring

theorem pulseWeight_le_one (c : Parameters) {y : ℝ} (hy : 0 ≤ y) : pulseWeight c y ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg c.lam_pos.le hy]

theorem weighted_square_bound (c : Parameters) (f : ℝ → ℝ) (hf : Continuous f)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y, |f y| ≤ M) :
    0 ≤ c.lam * (∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * f y ^ 2) ∧
      c.lam * (∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * f y ^ 2) ≤ 13 * M ^ 2 := by
  have hw : Continuous (fun y => pulseWeight c y * f y ^ 2) :=
    (pulseWeight_continuous c).mul (hf.pow 2)
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) c.pulseLength_pos.le
    (fun y => mul_nonneg (Real.exp_pos (-2 * c.lam * y)).le (sq_nonneg (f y)))
  have hi := intervalIntegral.integral_mono_on (μ := volume) c.pulseLength_pos.le
    (hw.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun y hy => show pulseWeight c y * f y ^ 2 ≤ M ^ 2 from by
      have hs : f y ^ 2 ≤ M ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr (hbound y)
      exact (mul_le_mul_of_nonneg_right (pulseWeight_le_one c hy.1) (sq_nonneg _)).trans
        (by simpa using hs))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have hmul := mul_le_mul_of_nonneg_left hi c.lam_pos.le
  have hL : c.lam * c.pulseLength = 13 := by
    dsimp [Parameters.pulseLength]
    field_simp [c.lam_pos.ne']
  refine ⟨mul_nonneg c.lam_pos.le hn, ?_⟩
  nlinarith [hmul, hL]

theorem weighted_product_bound (c : Parameters) (f g : ℝ → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (hg : ∀ y, |g y| ≤ M) :
    |c.lam * (∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * f y * g y)| ≤ 13 * M ^ 2 := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := c.pulseLength) (C := M ^ 2)
    (f := fun y => pulseWeight c y * f y * g y) (fun y hy => by
      have hy0 : 0 ≤ y := (uIoc_of_le c.pulseLength_pos.le ▸ hy).1.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (show 0 < pulseWeight c y from Real.exp_pos _)]
      calc
        pulseWeight c y * |f y| * |g y| ≤ 1 * M * M := by
          exact mul_le_mul (mul_le_mul (pulseWeight_le_one c hy0) (hf y)
            (abs_nonneg _) (by norm_num)) (hg y) (abs_nonneg _) (by simpa using hM)
        _ = M ^ 2 := by ring)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg c.pulseLength_pos.le] at hi
  rw [abs_mul, abs_of_pos c.lam_pos]
  have hmul := mul_le_mul_of_nonneg_left hi c.lam_pos.le
  have hL : c.lam * c.pulseLength = 13 := by
    dsimp [Parameters.pulseLength]
    field_simp [c.lam_pos.ne']
  nlinarith [hmul, hL]

theorem etaPolynomial_hasDerivAt (eta : ℝ) :
    HasDerivAt etaPolynomial (1 + 3 * eta ^ 2) eta := by
  convert! (hasDerivAt_id eta).fun_mul (((hasDerivAt_id eta).fun_pow 2).const_add 1) using 1
  simp only [id_eq]
  ring

theorem etaPolynomial_bounds {eta : ℝ} (heta : eta ^ 2 ≤ 1) :
    |etaPolynomial eta| ≤ 2 ∧ |deriv etaPolynomial eta| ≤ 4 := by
  have he : |eta| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  constructor
  · rw [etaPolynomial, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + eta ^ 2)]
    nlinarith [mul_nonneg (show 0 ≤ 1 - |eta| by linarith) (show 0 ≤ 1 + eta ^ 2 by positivity)]
  · rw [(etaPolynomial_hasDerivAt eta).deriv, abs_of_nonneg (by positivity : 0 ≤ 1 + 3 * eta ^ 2)]
    linarith

theorem quadratic_root_bracket {a b c r : ℝ}
    (ha : 1 / 5 ≤ a) (ha' : a ≤ 13 / 50) (hb : |b| ≤ 1 / 100)
    (hc : -(13 / 50) ≤ c) (hc' : c ≤ -(23 / 100))
    (hr : 0 < r) (heq : a * r ^ 2 + b * r + c = 0) :
    9 / 10 < r ∧ r < 6 / 5 := by
  obtain ⟨hbl, hbu⟩ := abs_le.mp hb
  constructor
  · by_contra h
    have hrl : r ≤ 9 / 10 := le_of_not_gt h
    have hs : r ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 9 / 10 - r by linarith) (show 0 ≤ 9 / 10 + r by linarith)]
    have haR := mul_le_mul_of_nonneg_right ha' (sq_nonneg r)
    have hbR := mul_le_mul_of_nonneg_right hbu hr.le
    nlinarith
  · by_contra h
    have hru : 6 / 5 ≤ r := le_of_not_gt h
    have hs := mul_nonneg (show 0 ≤ r - 6 / 5 by linarith) hr.le
    have haR := mul_le_mul_of_nonneg_right ha (sq_nonneg r)
    have hbR := mul_le_mul_of_nonneg_right hbl hr.le
    nlinarith

theorem amplitude_derivative_identity (d : OutgoingTail.TailData) (eta : ℝ)
    (hc : constantTerm d eta < -(1 / 5)) :
    (2 * quadraticCoefficient d.core * amplitude d eta + linearTerm d.core eta) *
        deriv (amplitude d) eta +
      deriv (linearTerm d.core) eta * amplitude d eta + deriv (constantTerm d) eta = 0 := by
  let F : ℝ → ℝ := fun t => energyPolynomial d (amplitude d t) t
  have he : F =ᶠ[𝓝 eta] (fun _ => 0) := by
    filter_upwards [(isOpen_lt (constantTerm_contDiff d).continuous continuous_const).mem_nhds hc]
      with t ht
    exact amplitude_energy_equation d t ht.le
  have hz : deriv F eta = 0 := by rw [he.deriv_eq]; exact deriv_const _ _
  have hA := ((amplitude_contDiff d).differentiable (by simp) eta).hasDerivAt
  have hb := ((linearTerm_contDiff d.core).differentiable (by simp) eta).hasDerivAt
  have hcc := ((constantTerm_contDiff d).differentiable (by simp) eta).hasDerivAt
  have hd := (((hA.pow 2).const_mul (quadraticCoefficient d.core)).add (hb.mul hA)).add hcc
  change HasDerivAt F _ eta at hd
  rw [hd.deriv] at hz
  convert! hz using 1
  ring

theorem prefixRepair_eq_affineProfile (c : Parameters) (y : ℝ) :
    prefixRepair c y = OutgoingPulseBounds.affineProfile c 1 0 y := by
  unfold prefixRepair LocalizedMomentRepair.repair OutgoingPulseBounds.affineProfile
    OutgoingPulseBounds.affineCoefficients OutgoingPulseBounds.affineDebt
  simp only [one_mul, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [OutgoingPulseBounds.bump_log_translate]

theorem amplitudeRepair_eq_affineProfile (c : Parameters) (y : ℝ) :
    amplitudeRepair c y = OutgoingPulseBounds.affineProfile c 0 1 y := by
  unfold amplitudeRepair LocalizedMomentRepair.repair OutgoingPulseBounds.affineProfile
    OutgoingPulseBounds.affineCoefficients OutgoingPulseBounds.affineDebt
  simp only [one_mul, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [OutgoingPulseBounds.bump_log_translate]

theorem repairBasis_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120) (y : ℝ) :
    |prefixRepair c y| ≤ OutgoingPulseBounds.correctionJetBound c.P c.m 0 *
        Real.exp (-(1 / (4 * c.lam))) ∧
      |amplitudeRepair c y| ≤ OutgoingPulseBounds.correctionJetBound c.P c.m 0 *
        Real.exp (-(1 / (4 * c.lam))) := by
  rw [prefixRepair_eq_affineProfile, amplitudeRepair_eq_affineProfile]
  constructor
  · simpa using OutgoingPulseBounds.affineProfile_jet_bound c hsmall 1 0 0 y
  · simpa using OutgoingPulseBounds.affineProfile_jet_bound c hsmall 0 1 0 y

theorem exp_inverse_bound {lam : ℝ} (hlam : 0 < lam) :
    Real.exp (-(1 / (4 * lam))) ^ 2 ≤ 4 * lam := by
  have hp : 0 < 1 / (4 * lam) := by positivity
  have he : 1 / (4 * lam) ≤ Real.exp (1 / (4 * lam)) := by
    linarith [Real.add_one_le_exp (1 / (4 * lam))]
  have hinv := one_div_le_one_div_of_le hp he
  have hlin : Real.exp (-(1 / (4 * lam))) ≤ 4 * lam := by
    rw [Real.exp_neg]
    simpa only [one_div, inv_inv] using hinv
  have hu : Real.exp (-(1 / (4 * lam))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hm := mul_le_mul hlin hu (Real.exp_pos _).le (by positivity : 0 ≤ 4 * lam)
  nlinarith

/-- Correction energy constant, given by `104 * OutgoingPulseBounds.correctionJetBound P m 0 ^
2`. -/
def correctionEnergyConstant (P m : ℝ) : ℝ :=
  104 * OutgoingPulseBounds.correctionJetBound P m 0 ^ 2

theorem correctionEnergyConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < correctionEnergyConstant P m := by
  unfold correctionEnergyConstant
  exact mul_pos (by norm_num) (sq_pos_of_pos (OutgoingPulseBounds.correctionJetBound_pos hP m 0))

theorem correctionEnergy_bounds (c : Parameters) (hsmall : c.lam ≤ 1 / 120) :
    0 ≤ quadraticCoefficient c - pulseConstant ∧
      quadraticCoefficient c - pulseConstant ≤ correctionEnergyConstant c.P c.m * c.lam ∧
      |linearCoefficient c| ≤ correctionEnergyConstant c.P c.m * c.lam ∧
      0 ≤ constantCorrection c ∧
      constantCorrection c ≤ correctionEnergyConstant c.P c.m * c.lam := by
  let M := OutgoingPulseBounds.correctionJetBound c.P c.m 0 * Real.exp (-(1 / (4 * c.lam)))
  have hM : 0 ≤ M := mul_nonneg (OutgoingPulseBounds.correctionJetBound_pos c.P_pos c.m 0).le
    (Real.exp_pos _).le
  have h0 : ∀ y, |prefixRepair c y| ≤ M := fun y => (repairBasis_bound c hsmall y).1
  have h1 : ∀ y, |amplitudeRepair c y| ≤ M := fun y => (repairBasis_bound c hsmall y).2
  have hb0 := weighted_square_bound c (prefixRepair c) (prefixRepair_contDiff c).continuous M hM h0
  have hb1 := weighted_square_bound c (amplitudeRepair c) (amplitudeRepair_contDiff c).continuous M
      hM h1
  have hcross := weighted_product_bound c (amplitudeRepair c) (prefixRepair c) M hM h1 h0
  have hlin : linearCoefficient c = 2 * (c.lam *
      ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * amplitudeRepair c y * prefixRepair c y) := by
    unfold linearCoefficient
    rw [mul_assoc]
    congr 2
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    calc
      _ = pulseWeight c y * (mainPulse (c.lam * y) * prefixRepair c y) +
          pulseWeight c y * amplitudeRepair c y * prefixRepair c y := by unfold amplitudeShape; ring
      _ = _ := by rw [mainPulse_mul_prefixRepair, mul_zero, zero_add]
  have hqeq : quadraticCoefficient c - pulseConstant =
      c.lam * ∫ y in (0 : ℝ)..c.pulseLength, pulseWeight c y * amplitudeRepair c y ^ 2 := by
    rw [quadraticCoefficient_eq]
    ring
  rw [← hqeq] at hb1
  have hlarge : 26 * M ^ 2 ≤ correctionEnergyConstant c.P c.m * c.lam := by
    have he := mul_le_mul_of_nonneg_left (exp_inverse_bound c.lam_pos)
      (sq_nonneg (OutgoingPulseBounds.correctionJetBound c.P c.m 0))
    dsimp [M, correctionEnergyConstant]
    nlinarith
  have hq : 13 * M ^ 2 ≤ 26 * M ^ 2 := by nlinarith [sq_nonneg M]
  refine ⟨hb1.1, hb1.2.trans (hq.trans hlarge), ?_, hb0.1, hb0.2.trans (hq.trans hlarge)⟩
  rw [hlin, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by nlinarith [hlarge])

/-- Error constant, given by `1 + prefixBoundConstant P m + correctionEnergyConstant P m + 2 *
OutgoingTail.flattenLength + 4 * TailEnergyBounds.tailConstant`. -/
def errorConstant (P m : ℝ) : ℝ :=
  1 + prefixBoundConstant P m + correctionEnergyConstant P m +
    2 * OutgoingTail.flattenLength + 4 * TailEnergyBounds.tailConstant

theorem errorConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < errorConstant P m := by
  unfold errorConstant
  linarith [prefixBoundConstant_pos P m, correctionEnergyConstant_pos hP m,
    OutgoingTail.flattenLength_pos, TailEnergyBounds.tailConstant_pos]

theorem errorConstant_ge {P : ℝ} (hP : 0 < P) (m : ℝ) :
    prefixBoundConstant P m ≤ errorConstant P m ∧
      correctionEnergyConstant P m ≤ errorConstant P m ∧
      TailEnergyBounds.tailConstant / 2 ≤ errorConstant P m ∧
      OutgoingTail.flattenLength + 2 * TailEnergyBounds.tailConstant ≤ errorConstant P m := by
  unfold errorConstant
  have hp := prefixBoundConstant_pos P m
  have hc := correctionEnergyConstant_pos hP m
  have hf := OutgoingTail.flattenLength_pos
  have ht := TailEnergyBounds.tailConstant_pos
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Error scale, given by `errorConstant c.P c.m * logarithmicRate c.lam`. -/
def errorScale (c : Parameters) : ℝ := errorConstant c.P c.m * logarithmicRate c.lam

theorem errorScale_pos (c : Parameters) : 0 < errorScale c :=
  mul_pos (errorConstant_pos c.P_pos c.m) (logarithmicRate_pos c)

/-- Bounds on the actual integral coefficients. This proposition is proved
from the explicit schedule in `actual_energy_error_bounds` below. -/
structure EnergyErrorBounds (d : OutgoingTail.TailData) (eta e : ℝ) : Prop where
  scale_nonneg : 0 ≤ e
  quadratic_error : quadraticCoefficient d.core - pulseConstant ≤ e
  linear_error : |linearCoefficient d.core| ≤ e
  correction_nonneg : 0 ≤ constantCorrection d.core
  correction_error : constantCorrection d.core ≤ e
  prefix_axial_nonneg : 0 ≤ normalizedPrefixAxial d.core
  prefix_axial_error : normalizedPrefixAxial d.core ≤ e
  prefix_angular_nonneg : 0 ≤ normalizedPrefixAngular d.core
  prefix_angular_error : normalizedPrefixAngular d.core ≤ e
  tail_nonneg : 0 ≤ normalizedTail d eta
  tail_error : normalizedTail d eta ≤ e

theorem actual_energy_error_bounds (d : OutgoingTail.TailData)
    (hsmall : d.core.lam ≤ 1 / 120) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) : EnergyErrorBounds d eta (errorScale d.core) := by
  obtain ⟨_, hq, hl, hc0, hc⟩ := correctionEnergy_bounds d.core hsmall
  have hC := errorConstant_ge d.core.P_pos d.core.m
  have hrate := logarithmicRate_pos d.core
  have hcorr : correctionEnergyConstant d.core.P d.core.m * d.core.lam ≤ errorScale d.core := by
    exact (mul_le_mul_of_nonneg_left (lambda_le_logarithmicRate d.core)
      (correctionEnergyConstant_pos d.core.P_pos d.core.m).le).trans
      (mul_le_mul_of_nonneg_right hC.2.1 hrate.le)
  have hpre : normalizedPrefixAxial d.core + normalizedPrefixAngular d.core ≤ errorScale d.core :=
    (normalizedPrefix_bound d.core hwait).trans (mul_le_mul_of_nonneg_right hC.1 hrate.le)
  have hn := normalizedPrefix_nonneg d.core
  exact ⟨(errorScale_pos d.core).le, hq.trans hcorr, hl.trans hcorr, hc0, hc.trans hcorr,
    hn.1, by linarith, hn.2, by linarith, normalizedTail_nonneg d eta,
    (normalizedTail_bound d eta heta).trans (mul_le_mul_of_nonneg_right hC.2.2.1 hrate.le)⟩

theorem numerical_coefficient_bounds (d : OutgoingTail.TailData) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : EnergyErrorBounds d eta e) (he : e ≤ 1 / 1000) :
    1 / 5 ≤ quadraticCoefficient d.core ∧ quadraticCoefficient d.core ≤ 13 / 50 ∧
      |linearTerm d.core eta| ≤ 1 / 100 ∧
      -(13 / 50) ≤ constantTerm d eta ∧ constantTerm d eta ≤ -(23 / 100) := by
  have hq := etaPolynomial_bounds heta
  have hq2 : etaPolynomial eta ^ 2 ≤ 4 := by
    have hb := abs_le.mp hq.1
    nlinarith [sq_nonneg (etaPolynomial eta)]
  have hprod0 : 0 ≤ (constantCorrection d.core + normalizedPrefixAxial d.core) * etaPolynomial eta
      ^ 2 :=
    mul_nonneg (add_nonneg h.correction_nonneg h.prefix_axial_nonneg) (sq_nonneg _)
  have hprod : (constantCorrection d.core + normalizedPrefixAxial d.core) * etaPolynomial eta ^ 2 ≤
      8 * e := by
    have hm := mul_le_mul (add_le_add h.correction_error h.prefix_axial_error) hq2
      (sq_nonneg (etaPolynomial eta)) (by linarith [h.scale_nonneg])
    nlinarith
  have hb : |linearTerm d.core eta| ≤ e * 2 := by
    unfold linearTerm
    rw [abs_mul]
    exact mul_le_mul h.linear_error hq.1 (abs_nonneg _) h.scale_nonneg
  have hD := RadialSchedule.pulse_energy_debt_bounds
  refine ⟨pulseConstant_lower.le.trans (quadraticCoefficient_ge d.core), ?_, by linarith, ?_, ?_⟩
  · linarith [h.quadratic_error, pulseConstant_upper]
  · unfold constantTerm
    linarith [h.prefix_angular_error, h.tail_error]
  · unfold constantTerm
    linarith [h.prefix_angular_nonneg, h.tail_nonneg]

theorem amplitude_spec_of_error_bound (d : OutgoingTail.TailData) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : EnergyErrorBounds d eta e) (he : e ≤ 1 / 1000) :
    9 / 10 < amplitude d eta ∧ amplitude d eta < 6 / 5 ∧
      totalEnergy d (amplitude d eta) eta = 0 := by
  obtain ⟨ha, ha', hb, hc, hc'⟩ := numerical_coefficient_bounds d eta e heta h he
  have hsmall : constantTerm d eta ≤ -(1 / 5) := by linarith
  have heq := amplitude_energy_equation d eta hsmall
  have hr := quadratic_root_bracket ha ha' hb hc hc' (amplitude_pos d eta) heq
  exact ⟨hr.1, hr.2, amplitude_totalEnergy_zero d eta hsmall⟩

theorem normalizedTail_derivative_bound (d : OutgoingTail.TailData) (eta : ℝ)
    (heta : eta ^ 2 ≤ 1) : |deriv (normalizedTail d) eta| ≤ errorScale d.core := by
  have he : normalizedTail d = (fun t => TailEnergyBounds.normalizedPostPulseEnergy d t / 2) := by
    funext t
    unfold normalizedTail TailEnergyBounds.normalizedPostPulseEnergy normalization
    rw [tailEnergy_eq]
    ring
  have hd := (((TailEnergyBounds.normalizedPostPulseEnergy_contDiff d).differentiable
    (by simp) eta).hasDerivAt.div_const 2).deriv
  rw [he, hd, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := TailEnergyBounds.abs_deriv_normalizedPostPulseEnergy_le d eta heta
  have hm := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
  have hC := (errorConstant_ge d.core.P_pos d.core.m).2.2.2
  calc
    _ ≤ (OutgoingTail.flattenLength + 2 * TailEnergyBounds.tailConstant) *
        logarithmicRate d.core.lam := by
      unfold logarithmicRate
      nlinarith
    _ ≤ errorScale d.core := mul_le_mul_of_nonneg_right hC (logarithmicRate_pos d.core).le

theorem linearTerm_hasDerivAt (c : Parameters) (eta : ℝ) :
    HasDerivAt (linearTerm c) (linearCoefficient c * (1 + 3 * eta ^ 2)) eta :=
  (etaPolynomial_hasDerivAt eta).const_mul _

theorem constantTerm_hasDerivAt (d : OutgoingTail.TailData) (eta : ℝ) :
    HasDerivAt (constantTerm d)
      (2 * (constantCorrection d.core + normalizedPrefixAxial d.core) *
        etaPolynomial eta * (1 + 3 * eta ^ 2) - deriv (normalizedTail d) eta) eta := by
  have hd := (((((etaPolynomial_hasDerivAt eta).pow 2).const_mul
    (constantCorrection d.core + normalizedPrefixAxial d.core)).sub_const
      RadialSchedule.pulseEnergyDebt).sub_const (normalizedPrefixAngular d.core)).sub
        (((normalizedTail_contDiff d).differentiable (by simp) eta).hasDerivAt)
  convert! hd using 1
  ring

theorem coefficient_derivative_bounds (d : OutgoingTail.TailData) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : EnergyErrorBounds d eta e)
    (hT : |deriv (normalizedTail d) eta| ≤ e) :
    |deriv (linearTerm d.core) eta| ≤ 4 * e ∧ |deriv (constantTerm d) eta| ≤ 33 * e := by
  have hq := etaPolynomial_bounds heta
  have hq' : 0 ≤ 1 + 3 * eta ^ 2 := by positivity
  have hq4 : 1 + 3 * eta ^ 2 ≤ 4 := by linarith
  have hsum : 0 ≤ constantCorrection d.core + normalizedPrefixAxial d.core :=
    add_nonneg h.correction_nonneg h.prefix_axial_nonneg
  have hsum' : constantCorrection d.core + normalizedPrefixAxial d.core ≤ 2 * e := by
    linarith [h.correction_error, h.prefix_axial_error]
  constructor
  · rw [(linearTerm_hasDerivAt d.core eta).deriv, abs_mul, abs_of_nonneg hq']
    have hm := mul_le_mul h.linear_error hq4 hq' h.scale_nonneg
    nlinarith
  · rw [(constantTerm_hasDerivAt d eta).deriv]
    calc
      _ ≤ |2 * (constantCorrection d.core + normalizedPrefixAxial d.core) *
          etaPolynomial eta * (1 + 3 * eta ^ 2)| + |deriv (normalizedTail d) eta| := abs_sub _ _
      _ ≤ 32 * e + e := by
        apply add_le_add _ hT
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hsum, abs_of_nonneg hq']
        have hm := mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hsum' (by norm_num : (0 : ℝ) ≤ 2)) hq.1
            (abs_nonneg _) (by linarith [h.scale_nonneg])) hq4 hq'
              (by linarith [h.scale_nonneg])
        nlinarith
      _ = 33 * e := by ring

theorem amplitude_derivative_bound_of_error (d : OutgoingTail.TailData) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : EnergyErrorBounds d eta e) (he : e ≤ 1 / 1000)
    (hT : |deriv (normalizedTail d) eta| ≤ e) : |deriv (amplitude d) eta| ≤ 128 * e := by
  obtain ⟨ha, _, hb, _, hc⟩ := numerical_coefficient_bounds d eta e heta h he
  obtain ⟨hr, hr', _⟩ := amplitude_spec_of_error_bound d eta e heta h he
  obtain ⟨hdb, hdc⟩ := coefficient_derivative_bounds d eta e heta h hT
  have hden : 1 / 3 ≤ 2 * quadraticCoefficient d.core * amplitude d eta + linearTerm d.core eta :=
      by
    have hm := mul_le_mul_of_nonneg_right ha (amplitude_pos d eta).le
    have hbl := (abs_le.mp hb).1
    nlinarith
  have hid := amplitude_derivative_identity d eta (by linarith)
  have heq : (2 * quadraticCoefficient d.core * amplitude d eta + linearTerm d.core eta) *
      deriv (amplitude d) eta =
        -(deriv (linearTerm d.core) eta * amplitude d eta + deriv (constantTerm d) eta) := by
            linarith
  have hbound : (2 * quadraticCoefficient d.core * amplitude d eta + linearTerm d.core eta) *
      |deriv (amplitude d) eta| ≤
        |deriv (linearTerm d.core) eta| * amplitude d eta + |deriv (constantTerm d) eta| := by
    calc
      _ = |(2 * quadraticCoefficient d.core * amplitude d eta + linearTerm d.core eta) *
          deriv (amplitude d) eta| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * quadraticCoefficient d.core *
          amplitude d eta + linearTerm d.core eta by linarith)]
      _ = |deriv (linearTerm d.core) eta * amplitude d eta + deriv (constantTerm d) eta| := by
        rw [heq, abs_neg]
      _ ≤ |deriv (linearTerm d.core) eta * amplitude d eta| + |deriv (constantTerm d) eta| :=
          abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_pos (amplitude_pos d eta)]
  have hupper := mul_le_mul hdb hr'.le (amplitude_pos d eta).le
    (by linarith [h.scale_nonneg] : 0 ≤ 4 * e)
  have hlower := mul_le_mul_of_nonneg_right hden (abs_nonneg (deriv (amplitude d) eta))
  nlinarith [h.scale_nonneg]

theorem logarithmicRate_tendsto_zero : Tendsto logarithmicRate (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left inf_le_left
  have hl : Tendsto (fun x : ℝ => Real.log x * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)
  have h := hid.sub hl
  convert! h using 1
  · funext x
    simp only [logarithmicRate, one_div, Real.log_inv]
    ring
  · simp

theorem exists_rate_threshold (C : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ lam : ℝ, 0 < lam → lam < delta →
      C * logarithmicRate lam ≤ 1 / 1000 := by
  have ht := logarithmicRate_tendsto_zero.const_mul C
  have he : ∀ᶠ lam in 𝓝[>] (0 : ℝ), C * logarithmicRate lam < 1 / 1000 :=
    ht.eventually (gt_mem_nhds (by norm_num : C * (0 : ℝ) < 1 / 1000))
  obtain ⟨delta, hd, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨delta, hd, fun lam hl hu => (hsub ⟨hl, hu⟩).le⟩

theorem energyPolynomial_strictMonoOn (d : OutgoingTail.TailData) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : EnergyErrorBounds d eta e) (he : e ≤ 1 / 1000) :
    StrictMonoOn (fun A => energyPolynomial d A eta) (Ici (9 / 10 : ℝ)) := by
  obtain ⟨ha, _, hb, _, _⟩ := numerical_coefficient_bounds d eta e heta h he
  intro A hA B hB hAB
  have hsum : 0 ≤ A + B := by simp only [mem_Ici] at hA hB; linarith
  have hm := mul_le_mul_of_nonneg_right ha hsum
  have hcoef : 0 < quadraticCoefficient d.core * (A + B) + linearTerm d.core eta := by
    have hb' := (abs_le.mp hb).1
    simp only [mem_Ici] at hA hB
    nlinarith
  have hp := mul_pos (sub_pos.mpr hAB) hcoef
  change quadraticCoefficient d.core * A ^ 2 + linearTerm d.core eta * A + constantTerm d eta <
    quadraticCoefficient d.core * B ^ 2 + linearTerm d.core eta * B + constantTerm d eta
  nlinarith only [hp]

theorem amplitude_unique (d : OutgoingTail.TailData) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : EnergyErrorBounds d eta e) (he : e ≤ 1 / 1000)
    (A : ℝ) (hA : A ∈ Icc (9 / 10 : ℝ) (6 / 5)) (hzero : totalEnergy d A eta = 0) :
    A = amplitude d eta := by
  have hr := amplitude_spec_of_error_bound d eta e heta h he
  have hnorm := totalEnergy_normalized d A eta
  rw [hzero, mul_zero, zero_div] at hnorm
  have hnorm' := totalEnergy_normalized d (amplitude d eta) eta
  rw [hr.2.2, mul_zero, zero_div] at hnorm'
  exact (energyPolynomial_strictMonoOn d eta e heta h he).injOn hA.1 hr.1.le
    (hnorm.symm.trans hnorm')

theorem axial_eq_of_amplitude_eq (c : Parameters) (amp₁ amp₂ : ℝ → ℝ) (eta y : ℝ)
    (hamp : amp₁ eta = amp₂ eta) : axial c amp₁ (y, eta) = axial c amp₂ (y, eta) := by
  have hd : debt c amp₁ eta = debt c amp₂ eta := by
    funext i
    simp only [debt, hamp]
  have hc : correction c amp₁ eta (Real.exp (y - c.pulseStart)) =
      correction c amp₂ eta (Real.exp (y - c.pulseStart)) := by
    unfold correction
    rw [hd]
  simp only [axial, pulseRatio, hamp, hc]

theorem realized_energy_eq (d : OutgoingTail.TailData) (eta : ℝ) :
    (∫ y, Real.exp y * (axial d.core (amplitude d) (y, eta) ^ 2 -
      OutgoingTail.finalAngular d (y, eta) ^ 2 / 2)) = totalEnergy d (amplitude d eta) eta := by
  unfold totalEnergy energyIntegrand
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    dsimp only
    rw [axial_eq_of_amplitude_eq d.core (amplitude d) (fun _ => amplitude d eta) eta y rfl])

/-- All smallness conditions refer to proved explicit constants and the
actual schedule parameter. The amplitude is a concrete globally C∞ function. -/
theorem amplitude_spec (d : OutgoingTail.TailData)
    (hsmall : d.core.lam ≤ 1 / 120) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hscale : errorScale d.core ≤ 1 / 1000) :
    ContDiff ℝ ∞ (amplitude d) ∧ ∀ eta : ℝ, eta ^ 2 ≤ 1 →
      9 / 10 < amplitude d eta ∧ amplitude d eta < 6 / 5 ∧
      (∫ y, Real.exp y * (axial d.core (amplitude d) (y, eta) ^ 2 -
        OutgoingTail.finalAngular d (y, eta) ^ 2 / 2)) = 0 ∧
      |deriv (amplitude d) eta| ≤ 128 * errorScale d.core ∧
      (∀ A ∈ Icc (9 / 10 : ℝ) (6 / 5), totalEnergy d A eta = 0 → A = amplitude d eta) := by
  refine ⟨amplitude_contDiff d, fun eta heta => ?_⟩
  have h := actual_energy_error_bounds d hsmall hwait eta heta
  have hr := amplitude_spec_of_error_bound d eta (errorScale d.core) heta h hscale
  exact ⟨hr.1, hr.2.1, (realized_energy_eq d eta).trans hr.2.2,
    amplitude_derivative_bound_of_error d eta (errorScale d.core) heta h hscale
      (normalizedTail_derivative_bound d eta heta),
    fun A hA hz => amplitude_unique d eta (errorScale d.core) heta h hscale A hA hz⟩

/-- One threshold works for all terminal parameters `0 < h < lam/2`.
The constructed core with `OutgoingTail.finalAngular` has zero total energy,
with an actual smooth amplitude in the manuscript's bracket and the claimed
derivative rate. The separate angular-moment reset is not included here. -/
theorem exists_uniform_amplitude_threshold (P m : ℝ) (hP : 0 < P) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ d : OutgoingTail.TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam₀ →
      ContDiff ℝ ∞ (amplitude d) ∧ ∀ eta : ℝ, eta ^ 2 ≤ 1 →
        9 / 10 < amplitude d eta ∧ amplitude d eta < 6 / 5 ∧
        (∫ y, Real.exp y * (axial d.core (amplitude d) (y, eta) ^ 2 -
          OutgoingTail.finalAngular d (y, eta) ^ 2 / 2)) = 0 ∧
        |deriv (amplitude d) eta| ≤ C * d.core.lam * (1 + Real.log (1 / d.core.lam)) ∧
        (∀ A ∈ Icc (9 / 10 : ℝ) (6 / 5), totalEnergy d A eta = 0 → A = amplitude d eta) := by
  obtain ⟨delta, hd, hsmall⟩ := exists_rate_threshold (errorConstant P m)
  refine ⟨min delta (1 / 120), 128 * errorConstant P m, lt_min hd (by norm_num),
    mul_pos (by norm_num) (errorConstant_pos hP m), ?_⟩
  intro d hdP hdm hwait hlam
  have hl : d.core.lam ≤ 1 / 120 :=
    (lt_of_lt_of_le hlam (min_le_right _ _)).le
  have hscale : errorScale d.core ≤ 1 / 1000 := by
    unfold errorScale
    rw [hdP, hdm]
    exact hsmall _ d.core.lam_pos (lt_of_lt_of_le hlam (min_le_left _ _))
  obtain ⟨hs, hspec⟩ := amplitude_spec d hl hwait hscale
  refine ⟨hs, fun eta heta => ?_⟩
  obtain ⟨hr, hr', hz, hderiv, huniq⟩ := hspec eta heta
  refine ⟨hr, hr', hz, ?_, huniq⟩
  convert! hderiv using 1
  unfold errorScale logarithmicRate
  rw [hdP, hdm]
  ring

/-! ## The same equality in the actual radial variable -/

theorem energyIntegrand_integrable (d : OutgoingTail.TailData) (A eta : ℝ) :
    Integrable (energyIntegrand d A eta) := by
  have htail := TailEnergyBounds.energyDensity_integrable_postPulse d eta
  have hr : IntegrableOn (energyIntegrand d A eta) (Ioi d.core.endpoint) := by
    refine IntegrableOn.congr_fun (s := Ioi d.core.endpoint) (htail.neg.div_const 2) ?_
        measurableSet_Ioi
    intro y hy
    exact (energyIntegrand_late d A eta hy.le).symm
  have h := (energyIntegrand_integrable_Iic d A eta (coreEndpoint_pos d.core).le).union hr
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

/-- Radial energy integrand, given by `axial d.core amp (Real.log (X / XR), eta) ^ 2 -
OutgoingTail.finalAngular d (Real.log (X / XR), eta) ^ 2 / 2`. -/
def radialEnergyIntegrand (d : OutgoingTail.TailData) (amp : ℝ → ℝ) (eta XR X : ℝ) : ℝ :=
  axial d.core amp (Real.log (X / XR), eta) ^ 2 -
    OutgoingTail.finalAngular d (Real.log (X / XR), eta) ^ 2 / 2

private theorem radialCoordinate_image (XR : ℝ) (hXR : 0 < XR) :
    (fun y : ℝ => XR * Real.exp y) '' univ = Ioi 0 := by
  ext X
  constructor
  · rintro ⟨y, _, rfl⟩
    exact mul_pos hXR (Real.exp_pos _)
  · intro hX
    refine ⟨Real.log (X / XR), mem_univ _, ?_⟩
    dsimp only
    rw [Real.exp_log (div_pos hX hXR)]
    field_simp [hXR.ne']

private theorem radialCoordinate_transform (d : OutgoingTail.TailData) (amp : ℝ → ℝ)
    (eta XR : ℝ) (hXR : 0 < XR) :
    (fun y => |XR * Real.exp y| • radialEnergyIntegrand d amp eta XR (XR * Real.exp y)) =
      (fun y => XR * energyIntegrand d (amp eta) eta y) := by
  funext y
  have hlog : Real.log (XR * Real.exp y / XR) = y := by
    rw [mul_comm XR, mul_div_cancel_right₀ _ hXR.ne', Real.log_exp]
  simp only [radialEnergyIntegrand, hlog, abs_of_pos (mul_pos hXR (Real.exp_pos _)), smul_eq_mul,
    energyIntegrand]
  rw [axial_eq_of_amplitude_eq d.core amp (fun _ => amp eta) eta y rfl]
  ring

theorem radialEnergy_integrable (d : OutgoingTail.TailData) (amp : ℝ → ℝ)
    (eta XR : ℝ) (hXR : 0 < XR) :
    IntegrableOn (radialEnergyIntegrand d amp eta XR) (Ioi 0) := by
  have hd : ∀ y ∈ (univ : Set ℝ), HasDerivWithinAt (fun y => XR * Real.exp y)
      (XR * Real.exp y) univ y := fun y _ => ((Real.hasDerivAt_exp y).const_mul XR).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => XR * Real.exp y) univ := by
    intro x _ y _ h
    exact Real.exp_injective (mul_left_cancel₀ hXR.ne' h)
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj
    (radialEnergyIntegrand d amp eta XR)
  rw [radialCoordinate_image XR hXR, radialCoordinate_transform d amp eta XR hXR,
    integrableOn_univ] at h
  exact h.mpr ((energyIntegrand_integrable d (amp eta) eta).const_mul XR)

theorem radialEnergy_integral (d : OutgoingTail.TailData) (amp : ℝ → ℝ)
    (eta XR : ℝ) (hXR : 0 < XR) :
    (∫ X in Ioi 0, radialEnergyIntegrand d amp eta XR X) = XR * totalEnergy d (amp eta) eta := by
  have hd : ∀ y ∈ (univ : Set ℝ), HasDerivWithinAt (fun y => XR * Real.exp y)
      (XR * Real.exp y) univ y := fun y _ => ((Real.hasDerivAt_exp y).const_mul XR).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => XR * Real.exp y) univ := by
    intro x _ y _ h
    exact Real.exp_injective (mul_left_cancel₀ hXR.ne' h)
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj
    (radialEnergyIntegrand d amp eta XR)
  rw [radialCoordinate_image XR hXR, radialCoordinate_transform d amp eta XR hXR,
    setIntegral_univ, integral_const_mul] at h
  exact h

theorem radialEnergy_zero (d : OutgoingTail.TailData)
    (hsmall : d.core.lam ≤ 1 / 120) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hscale : errorScale d.core ≤ 1 / 1000) (eta : ℝ) (heta : eta ^ 2 ≤ 1)
    (XR : ℝ) (hXR : 0 < XR) :
    (∫ X in Ioi 0, radialEnergyIntegrand d (amplitude d) eta XR X) = 0 := by
  rw [radialEnergy_integral d (amplitude d) eta XR hXR]
  have h := amplitude_spec_of_error_bound d eta (errorScale d.core) heta
    (actual_energy_error_bounds d hsmall hwait eta heta) hscale
  rw [h.2.2, mul_zero]

end NavierStokes.PulseAmplitude
