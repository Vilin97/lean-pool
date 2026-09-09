/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseAmplitude
public import LeanPool.NavierStokesAndEuler.NavierStokes.ResetEnergyBounds
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Pulse amplitude after the actual angular-moment reset

The scalar energy equation here uses `UniformAngularReset.correctedAngular`.
Its signed reset energy is retained in the constant coefficient, and the
reset witness and amplitude are constructed together for small `lam`.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

namespace NavierStokes.CorrectedPulseAmplitude

/-- Energy integrand, given by `Real.exp y * (axial d.core (fun _ => A) (y, eta) ^ 2 -
correctedAngular d c (y, eta) ^ 2 / 2)`. -/
def energyIntegrand (d : TailData) (c : ℝ → Coeff) (A eta y : ℝ) : ℝ :=
  Real.exp y * (axial d.core (fun _ => A) (y, eta) ^ 2 - correctedAngular d c (y, eta) ^ 2 / 2)

/-- Total energy, given by `∫ y, energyIntegrand d c A eta y`. -/
def totalEnergy (d : TailData) (c : ℝ → Coeff) (A eta : ℝ) : ℝ :=
  ∫ y, energyIntegrand d c A eta y

theorem energyIntegrand_eq (d : TailData) (c : ℝ → Coeff) (A eta y : ℝ) :
    energyIntegrand d c A eta y = PulseAmplitude.energyIntegrand d A eta y -
      ResetEnergyBounds.resetDensity d c eta y / 2 := by
  unfold energyIntegrand PulseAmplitude.energyIntegrand ResetEnergyBounds.resetDensity
  ring

theorem energyIntegrand_integrable (d : TailData) (c : ℝ → Coeff) (A eta : ℝ) :
    Integrable (energyIntegrand d c A eta) := by
  have he : energyIntegrand d c A eta = (fun y => PulseAmplitude.energyIntegrand d A eta y -
      ResetEnergyBounds.resetDensity d c eta y / 2) := funext (energyIntegrand_eq d c A eta)
  rw [he]
  exact (PulseAmplitude.energyIntegrand_integrable d A eta).sub
    ((ResetEnergyBounds.resetDensity_integrable d c eta).div_const 2)

theorem totalEnergy_eq (d : TailData) (c : ℝ → Coeff) (A eta : ℝ) :
    totalEnergy d c A eta = PulseAmplitude.totalEnergy d A eta - ResetEnergyBounds.resetEnergy d c
        eta / 2 := by
  unfold totalEnergy
  simp_rw [energyIntegrand_eq]
  rw [integral_sub (PulseAmplitude.energyIntegrand_integrable d A eta)
    ((ResetEnergyBounds.resetDensity_integrable d c eta).div_const 2), integral_div]
  rfl

/-- Energy shift, given by `ResetEnergyBounds.normalizedResetEnergy d c eta / 2`. -/
def energyShift (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  ResetEnergyBounds.normalizedResetEnergy d c eta / 2

/-- Constant term, given by `PulseAmplitude.constantTerm d eta - energyShift d c eta`. -/
def constantTerm (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  PulseAmplitude.constantTerm d eta - energyShift d c eta

/-- Energy polynomial, given by `PulseAmplitude.quadraticCoefficient d.core * A ^ 2 +
PulseAmplitude.linearTerm d.core eta * A + constantTerm d c eta`. -/
def energyPolynomial (d : TailData) (c : ℝ → Coeff) (A eta : ℝ) : ℝ :=
  PulseAmplitude.quadraticCoefficient d.core * A ^ 2 +
    PulseAmplitude.linearTerm d.core eta * A + constantTerm d c eta

theorem totalEnergy_normalized (d : TailData) (c : ℝ → Coeff) (A eta : ℝ) :
    d.core.lam * totalEnergy d c A eta / (PulseAmplitude.normalization d.core * shape eta ^ 2) =
      energyPolynomial d c A eta := by
  rw [totalEnergy_eq, mul_sub, sub_div, PulseAmplitude.totalEnergy_normalized]
  unfold energyPolynomial constantTerm energyShift PulseAmplitude.energyPolynomial
    ResetEnergyBounds.normalizedResetEnergy ResetEnergyBounds.pulseNormalization
        PulseAmplitude.normalization
  ring

theorem energyShift_contDiff (d : TailData) {c : ℝ → Coeff} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (energyShift d c) :=
  (ResetEnergyBounds.normalizedResetEnergy_contDiff d hc).div_const 2

theorem constantTerm_contDiff (d : TailData) {c : ℝ → Coeff} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (constantTerm d c) :=
  (PulseAmplitude.constantTerm_contDiff d).sub (energyShift_contDiff d hc)

/-- Discriminant, constructed using `PulseAmplitude.linearTerm`. -/
def discriminant (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  PulseAmplitude.linearTerm d.core eta ^ 2 - 4 * PulseAmplitude.quadraticCoefficient d.core *
    PulseAmplitude.negativeClamp (constantTerm d c eta)

theorem discriminant_pos (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : 0 < discriminant d c eta := by
  unfold discriminant
  have ha := PulseAmplitude.quadraticCoefficient_pos d.core
  have hc := PulseAmplitude.negativeClamp_neg (constantTerm d c eta)
  nlinarith [sq_nonneg (PulseAmplitude.linearTerm d.core eta), mul_neg_of_pos_of_neg ha hc]

/-- Amplitude, given by `(-PulseAmplitude.linearTerm d.core eta + Real.sqrt (discriminant d c
eta)) / (2 * PulseAmplitude.quadraticCoefficient d.core)`. -/
def amplitude (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  (-PulseAmplitude.linearTerm d.core eta + Real.sqrt (discriminant d c eta)) /
    (2 * PulseAmplitude.quadraticCoefficient d.core)

theorem amplitude_contDiff (d : TailData) {c : ℝ → Coeff} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (amplitude d c) := by
  have hd : ContDiff ℝ ∞ (discriminant d c) :=
    ((PulseAmplitude.linearTerm_contDiff d.core).pow 2).sub (contDiff_const.mul
      (PulseAmplitude.negativeClamp_contDiff.comp (constantTerm_contDiff d hc)))
  exact ((PulseAmplitude.linearTerm_contDiff d.core).neg.add
    (hd.sqrt (fun eta => (discriminant_pos d c eta).ne'))).div_const _

theorem amplitude_pos (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : 0 < amplitude d c eta := by
  have ha := PulseAmplitude.quadraticCoefficient_pos d.core
  have hc := PulseAmplitude.negativeClamp_neg (constantTerm d c eta)
  have hd := Real.sq_sqrt (discriminant_pos d c eta).le
  have hs := Real.sqrt_nonneg (discriminant d c eta)
  have hb : PulseAmplitude.linearTerm d.core eta < Real.sqrt (discriminant d c eta) := by
    dsimp only [discriminant] at hd hs ⊢
    nlinarith [mul_neg_of_pos_of_neg ha hc]
  exact div_pos (by linarith) (mul_pos (by norm_num) ha)

theorem amplitude_clamped_equation (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    PulseAmplitude.quadraticCoefficient d.core * amplitude d c eta ^ 2 +
      PulseAmplitude.linearTerm d.core eta * amplitude d c eta +
      PulseAmplitude.negativeClamp (constantTerm d c eta) = 0 := by
  have hs := Real.sq_sqrt (discriminant_pos d c eta).le
  have hp : Real.sqrt (discriminant d c eta) ^ 2 - PulseAmplitude.linearTerm d.core eta ^ 2 +
      4 * PulseAmplitude.quadraticCoefficient d.core *
        PulseAmplitude.negativeClamp (constantTerm d c eta) = 0 := by
    rw [hs]
    unfold discriminant
    ring
  unfold amplitude
  field_simp [(PulseAmplitude.quadraticCoefficient_pos d.core).ne']
  linear_combination hp

theorem amplitude_energy_equation (d : TailData) (c : ℝ → Coeff) (eta : ℝ)
    (hc : constantTerm d c eta ≤ -(1 / 5)) : energyPolynomial d c (amplitude d c eta) eta = 0 := by
  have h := amplitude_clamped_equation d c eta
  rwa [PulseAmplitude.negativeClamp_eq hc] at h

theorem amplitude_totalEnergy_zero (d : TailData) (c : ℝ → Coeff) (eta : ℝ)
    (hc : constantTerm d c eta ≤ -(1 / 5)) : totalEnergy d c (amplitude d c eta) eta = 0 := by
  have h := totalEnergy_normalized d c (amplitude d c eta) eta
  rw [amplitude_energy_equation d c eta hc] at h
  rcases div_eq_zero_iff.mp h with hmul | hz
  · exact (mul_eq_zero.mp hmul).resolve_left d.core.lam_pos.ne'
  · exact False.elim ((mul_pos (PulseAmplitude.normalization_pos d.core)
      (sq_pos_of_pos (shape_pos eta))).ne' hz)

/-- Combined constant, given by `PulseAmplitude.errorConstant P m + 36 * K + 1`. -/
def combinedConstant (P m K : ℝ) : ℝ := PulseAmplitude.errorConstant P m + 36 * K + 1
/-- Combined scale, given by `combinedConstant d.core.P d.core.m K *
PulseAmplitude.logarithmicRate d.core.lam`. -/
def combinedScale (d : TailData) (K : ℝ) : ℝ :=
  combinedConstant d.core.P d.core.m K * PulseAmplitude.logarithmicRate d.core.lam

theorem combinedConstant_pos {P : ℝ} (hP : 0 < P) (m K : ℝ) (hK : 0 < K) :
    0 < combinedConstant P m K := by
  unfold combinedConstant
  linarith [PulseAmplitude.errorConstant_pos hP m]

theorem oldScale_le (d : TailData) (K : ℝ) (hK : 0 < K) :
    PulseAmplitude.errorScale d.core ≤ combinedScale d K := by
  apply mul_le_mul_of_nonneg_right _ (PulseAmplitude.logarithmicRate_pos d.core).le
  unfold combinedConstant
  linarith

theorem power29_le_lambda (d : TailData) : d.core.lam ^ (29 : ℕ) ≤ d.core.lam := by
  have hpow : d.core.lam ^ (28 : ℕ) ≤ 1 :=
    pow_le_one₀ d.core.lam_pos.le (by linarith [d.core.lam_lt])
  calc
    _ = d.core.lam * d.core.lam ^ (28 : ℕ) := by ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow d.core.lam_pos.le]

theorem energyShift_bounds {d : TailData} {K : ℝ} (w : ResetWitness d K) (hK : 0 < K) (eta : ℝ)
    (heta : eta ^ 2 ≤ 1) :
    |energyShift d w.coefficients eta| ≤ combinedScale d K ∧
      |deriv (energyShift d w.coefficients) eta| ≤ combinedScale d K := by
  have h0 := ResetEnergyBounds.normalizedResetEnergy_abs_le w eta heta
  have h1 := ResetEnergyBounds.normalizedResetEnergy_deriv_abs_le w eta heta
  have hpow := power29_le_lambda d
  have hcap : 36 * K * d.core.lam ^ (29 : ℕ) ≤ combinedScale d K := by
    calc
      _ ≤ 36 * K * d.core.lam := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 36 * K * PulseAmplitude.logarithmicRate d.core.lam :=
        mul_le_mul_of_nonneg_left (PulseAmplitude.lambda_le_logarithmicRate d.core) (by positivity)
      _ ≤ combinedScale d K := by
        apply mul_le_mul_of_nonneg_right _ (PulseAmplitude.logarithmicRate_pos d.core).le
        unfold combinedConstant
        linarith [PulseAmplitude.errorConstant_pos d.core.P_pos d.core.m]
  have hd := (((ResetEnergyBounds.normalizedResetEnergy_contDiff d w.smooth).differentiable
    (by simp) eta).hasDerivAt.div_const 2).deriv
  constructor
  · unfold energyShift
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_nonneg hK.le (pow_nonneg d.core.lam_pos.le (29 : ℕ))]
  · change |deriv (fun t => ResetEnergyBounds.normalizedResetEnergy d w.coefficients t / 2) eta| ≤ _
    rw [hd, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith

theorem old_error_bounds (d : TailData) (K : ℝ) (hK : 0 < K)
    (hsmall : d.core.lam ≤ 1 / 120) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) : PulseAmplitude.EnergyErrorBounds d eta (combinedScale d K) :=
        by
  have h := PulseAmplitude.actual_energy_error_bounds d hsmall hwait eta heta
  have hm := oldScale_le d K hK
  exact ⟨h.scale_nonneg.trans hm, h.quadratic_error.trans hm, h.linear_error.trans hm,
    h.correction_nonneg, h.correction_error.trans hm, h.prefix_axial_nonneg,
    h.prefix_axial_error.trans hm, h.prefix_angular_nonneg, h.prefix_angular_error.trans hm,
    h.tail_nonneg, h.tail_error.trans hm⟩

theorem numerical_coefficient_bounds (d : TailData) (c : ℝ → Coeff) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : PulseAmplitude.EnergyErrorBounds d eta e)
    (hshift : |energyShift d c eta| ≤ e) (he : e ≤ 1 / 1000) :
    1 / 5 ≤ PulseAmplitude.quadraticCoefficient d.core ∧
      PulseAmplitude.quadraticCoefficient d.core ≤ 13 / 50 ∧
      |PulseAmplitude.linearTerm d.core eta| ≤ 1 / 100 ∧
      -(13 / 50) ≤ constantTerm d c eta ∧ constantTerm d c eta ≤ -(23 / 100) := by
  obtain ⟨ha, ha', hb, _, _⟩ := PulseAmplitude.numerical_coefficient_bounds d eta e heta h he
  have hq := (PulseAmplitude.etaPolynomial_bounds heta).1
  have hq2 : PulseAmplitude.etaPolynomial eta ^ 2 ≤ 4 := by
    have hbq := abs_le.mp hq
    nlinarith
  have hprod0 : 0 ≤ (PulseAmplitude.constantCorrection d.core +
      PulseAmplitude.normalizedPrefixAxial d.core) * PulseAmplitude.etaPolynomial eta ^ 2 :=
    mul_nonneg (add_nonneg h.correction_nonneg h.prefix_axial_nonneg) (sq_nonneg _)
  have hprod : (PulseAmplitude.constantCorrection d.core + PulseAmplitude.normalizedPrefixAxial
      d.core) *
      PulseAmplitude.etaPolynomial eta ^ 2 ≤ 8 * e := by
    have hm := mul_le_mul (add_le_add h.correction_error h.prefix_axial_error) hq2
      (sq_nonneg (PulseAmplitude.etaPolynomial eta)) (by linarith [h.scale_nonneg])
    nlinarith
  have hD := RadialSchedule.pulse_energy_debt_bounds
  obtain ⟨hsl, hsu⟩ := abs_le.mp hshift
  refine ⟨ha, ha', hb, ?_, ?_⟩
  · unfold constantTerm PulseAmplitude.constantTerm
    linarith [h.prefix_angular_error, h.tail_error]
  · unfold constantTerm PulseAmplitude.constantTerm
    linarith [h.prefix_angular_nonneg, h.tail_nonneg]

theorem amplitude_spec_of_bounds (d : TailData) (c : ℝ → Coeff) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : PulseAmplitude.EnergyErrorBounds d eta e)
    (hshift : |energyShift d c eta| ≤ e) (he : e ≤ 1 / 1000) :
    9 / 10 < amplitude d c eta ∧ amplitude d c eta < 6 / 5 ∧ totalEnergy d c (amplitude d c eta)
        eta = 0 := by
  obtain ⟨ha, ha', hb, hc, hc'⟩ := numerical_coefficient_bounds d c eta e heta h hshift he
  have hneg : constantTerm d c eta ≤ -(1 / 5) := by linarith
  have hr := PulseAmplitude.quadratic_root_bracket ha ha' hb hc hc' (amplitude_pos d c eta)
    (amplitude_energy_equation d c eta hneg)
  exact ⟨hr.1, hr.2, amplitude_totalEnergy_zero d c eta hneg⟩

theorem amplitude_derivative_identity (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) (eta : ℝ) (hneg : constantTerm d c eta < -(1 / 5)) :
    (2 * PulseAmplitude.quadraticCoefficient d.core * amplitude d c eta +
        PulseAmplitude.linearTerm d.core eta) * deriv (amplitude d c) eta +
      deriv (PulseAmplitude.linearTerm d.core) eta * amplitude d c eta +
        deriv (constantTerm d c) eta = 0 := by
  let F : ℝ → ℝ := fun t => energyPolynomial d c (amplitude d c t) t
  have he : F =ᶠ[𝓝 eta] (fun _ => 0) := by
    filter_upwards [(isOpen_lt (constantTerm_contDiff d hc).continuous continuous_const).mem_nhds
        hneg]
      with t ht
    exact amplitude_energy_equation d c t ht.le
  have hz : deriv F eta = 0 := by rw [he.deriv_eq]; exact deriv_const _ _
  have hA := ((amplitude_contDiff d hc).differentiable (by simp) eta).hasDerivAt
  have hb := ((PulseAmplitude.linearTerm_contDiff d.core).differentiable (by simp) eta).hasDerivAt
  have hcc := ((constantTerm_contDiff d hc).differentiable (by simp) eta).hasDerivAt
  have hd := (((hA.pow 2).const_mul (PulseAmplitude.quadraticCoefficient d.core)).add (hb.mul
      hA)).add hcc
  change HasDerivAt F _ eta at hd
  rw [hd.deriv] at hz
  convert! hz using 1
  ring

theorem coefficient_derivative_bounds (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) (eta e : ℝ) (heta : eta ^ 2 ≤ 1)
    (h : PulseAmplitude.EnergyErrorBounds d eta e)
    (hT : |deriv (PulseAmplitude.normalizedTail d) eta| ≤ e)
    (hs : |deriv (energyShift d c) eta| ≤ e) :
    |deriv (PulseAmplitude.linearTerm d.core) eta| ≤ 4 * e ∧
      |deriv (constantTerm d c) eta| ≤ 34 * e := by
  have hb := PulseAmplitude.coefficient_derivative_bounds d eta e heta h hT
  refine ⟨hb.1, ?_⟩
  have hd := (((PulseAmplitude.constantTerm_contDiff d).differentiable (by
      simp) eta).hasDerivAt).sub
    (((energyShift_contDiff d hc).differentiable (by simp) eta).hasDerivAt)
  change HasDerivAt (constantTerm d c) _ eta at hd
  rw [hd.deriv]
  have ha := abs_sub (deriv (PulseAmplitude.constantTerm d) eta) (deriv (energyShift d c) eta)
  linarith

theorem amplitude_derivative_bound (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) (eta e : ℝ) (heta : eta ^ 2 ≤ 1)
    (h : PulseAmplitude.EnergyErrorBounds d eta e) (hshift : |energyShift d c eta| ≤ e)
    (he : e ≤ 1 / 1000) (hT : |deriv (PulseAmplitude.normalizedTail d) eta| ≤ e)
    (hs : |deriv (energyShift d c) eta| ≤ e) : |deriv (amplitude d c) eta| ≤ 128 * e := by
  obtain ⟨ha, _, hb, _, hconst⟩ := numerical_coefficient_bounds d c eta e heta h hshift he
  obtain ⟨hr, hr', _⟩ := amplitude_spec_of_bounds d c eta e heta h hshift he
  obtain ⟨hdb, hdc⟩ := coefficient_derivative_bounds d hc eta e heta h hT hs
  have hden : 1 / 3 ≤ 2 * PulseAmplitude.quadraticCoefficient d.core * amplitude d c eta +
      PulseAmplitude.linearTerm d.core eta := by
    have hm := mul_le_mul_of_nonneg_right ha (amplitude_pos d c eta).le
    have hbl := (abs_le.mp hb).1
    nlinarith
  have hid := amplitude_derivative_identity d hc eta (by linarith)
  have heq : (2 * PulseAmplitude.quadraticCoefficient d.core * amplitude d c eta +
      PulseAmplitude.linearTerm d.core eta) * deriv (amplitude d c) eta =
        -(deriv (PulseAmplitude.linearTerm d.core) eta * amplitude d c eta +
          deriv (constantTerm d c) eta) := by linarith
  have hbound : (2 * PulseAmplitude.quadraticCoefficient d.core * amplitude d c eta +
      PulseAmplitude.linearTerm d.core eta) * |deriv (amplitude d c) eta| ≤
        |deriv (PulseAmplitude.linearTerm d.core) eta| * amplitude d c eta +
          |deriv (constantTerm d c) eta| := by
    calc
      _ = |(2 * PulseAmplitude.quadraticCoefficient d.core * amplitude d c eta +
          PulseAmplitude.linearTerm d.core eta) * deriv (amplitude d c) eta| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * PulseAmplitude.quadraticCoefficient d.core *
          amplitude d c eta + PulseAmplitude.linearTerm d.core eta by linarith)]
      _ = |deriv (PulseAmplitude.linearTerm d.core) eta * amplitude d c eta +
          deriv (constantTerm d c) eta| := by rw [heq, abs_neg]
      _ ≤ |deriv (PulseAmplitude.linearTerm d.core) eta * amplitude d c eta| +
          |deriv (constantTerm d c) eta| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_pos (amplitude_pos d c eta)]
  have hupper := mul_le_mul hdb hr'.le (amplitude_pos d c eta).le
    (by linarith [h.scale_nonneg] : 0 ≤ 4 * e)
  have hlower := mul_le_mul_of_nonneg_right hden (abs_nonneg (deriv (amplitude d c) eta))
  nlinarith [h.scale_nonneg]

theorem energyPolynomial_strictMonoOn (d : TailData) (c : ℝ → Coeff) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : PulseAmplitude.EnergyErrorBounds d eta e)
    (hshift : |energyShift d c eta| ≤ e) (he : e ≤ 1 / 1000) :
    StrictMonoOn (fun A => energyPolynomial d c A eta) (Ici (9 / 10 : ℝ)) := by
  obtain ⟨ha, _, hb, _, _⟩ := numerical_coefficient_bounds d c eta e heta h hshift he
  intro A hA B hB hAB
  have hsum : 0 ≤ A + B := by simp only [mem_Ici] at hA hB; linarith
  have hm := mul_le_mul_of_nonneg_right ha hsum
  have hcoef : 0 < PulseAmplitude.quadraticCoefficient d.core * (A + B) +
      PulseAmplitude.linearTerm d.core eta := by
    have hbl := (abs_le.mp hb).1
    simp only [mem_Ici] at hA hB
    nlinarith
  have hp := mul_pos (sub_pos.mpr hAB) hcoef
  change PulseAmplitude.quadraticCoefficient d.core * A ^ 2 +
      PulseAmplitude.linearTerm d.core eta * A + constantTerm d c eta <
    PulseAmplitude.quadraticCoefficient d.core * B ^ 2 +
      PulseAmplitude.linearTerm d.core eta * B + constantTerm d c eta
  nlinarith only [hp]

theorem amplitude_unique (d : TailData) (c : ℝ → Coeff) (eta e : ℝ)
    (heta : eta ^ 2 ≤ 1) (h : PulseAmplitude.EnergyErrorBounds d eta e)
    (hshift : |energyShift d c eta| ≤ e) (he : e ≤ 1 / 1000)
    (A : ℝ) (hA : A ∈ Icc (9 / 10 : ℝ) (6 / 5)) (hz : totalEnergy d c A eta = 0) :
    A = amplitude d c eta := by
  have hr := amplitude_spec_of_bounds d c eta e heta h hshift he
  have hn := totalEnergy_normalized d c A eta
  rw [hz, mul_zero, zero_div] at hn
  have hn' := totalEnergy_normalized d c (amplitude d c eta) eta
  rw [hr.2.2, mul_zero, zero_div] at hn'
  exact (energyPolynomial_strictMonoOn d c eta e heta h hshift he).injOn hA.1 hr.1.le
    (hn.symm.trans hn')

theorem realized_energy_eq (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    (∫ y, Real.exp y * (axial d.core (amplitude d c) (y, eta) ^ 2 -
      correctedAngular d c (y, eta) ^ 2 / 2)) = totalEnergy d c (amplitude d c eta) eta := by
  unfold totalEnergy energyIntegrand
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    dsimp only
    rw [PulseAmplitude.axial_eq_of_amplitude_eq d.core (amplitude d c)
      (fun _ => amplitude d c eta) eta y rfl])

/-- Radial energy integrand, given by `axial d.core amp (Real.log (X / XR), eta) ^ 2 -
correctedAngular d c (Real.log (X / XR), eta) ^ 2 / 2`. -/
def radialEnergyIntegrand (d : TailData) (c : ℝ → Coeff) (amp : ℝ → ℝ) (eta XR X : ℝ) : ℝ :=
  axial d.core amp (Real.log (X / XR), eta) ^ 2 - correctedAngular d c (Real.log (X / XR), eta) ^ 2
      / 2

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

private theorem radialCoordinate_transform (d : TailData) (c : ℝ → Coeff) (amp : ℝ → ℝ)
    (eta XR : ℝ) (hXR : 0 < XR) :
    (fun y => |XR * Real.exp y| • radialEnergyIntegrand d c amp eta XR (XR * Real.exp y)) =
      (fun y => XR * energyIntegrand d c (amp eta) eta y) := by
  funext y
  have hlog : Real.log (XR * Real.exp y / XR) = y := by
    rw [mul_comm XR, mul_div_cancel_right₀ _ hXR.ne', Real.log_exp]
  simp only [radialEnergyIntegrand, hlog, abs_of_pos (mul_pos hXR (Real.exp_pos _)), smul_eq_mul,
    energyIntegrand]
  rw [PulseAmplitude.axial_eq_of_amplitude_eq d.core amp (fun _ => amp eta) eta y rfl]
  ring

theorem radialEnergy_integrable (d : TailData) (c : ℝ → Coeff) (amp : ℝ → ℝ)
    (eta XR : ℝ) (hXR : 0 < XR) :
    IntegrableOn (radialEnergyIntegrand d c amp eta XR) (Ioi 0) := by
  have hd : ∀ y ∈ (univ : Set ℝ), HasDerivWithinAt (fun y => XR * Real.exp y)
      (XR * Real.exp y) univ y := fun y _ => ((Real.hasDerivAt_exp y).const_mul XR).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => XR * Real.exp y) univ := by
    intro x _ y _ h
    exact Real.exp_injective (mul_left_cancel₀ hXR.ne' h)
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj
    (radialEnergyIntegrand d c amp eta XR)
  rw [radialCoordinate_image XR hXR, radialCoordinate_transform d c amp eta XR hXR,
    integrableOn_univ] at h
  exact h.mpr ((energyIntegrand_integrable d c (amp eta) eta).const_mul XR)

theorem radialEnergy_integral (d : TailData) (c : ℝ → Coeff) (amp : ℝ → ℝ)
    (eta XR : ℝ) (hXR : 0 < XR) :
    (∫ X in Ioi 0, radialEnergyIntegrand d c amp eta XR X) = XR * totalEnergy d c (amp eta) eta :=
        by
  have hd : ∀ y ∈ (univ : Set ℝ), HasDerivWithinAt (fun y => XR * Real.exp y)
      (XR * Real.exp y) univ y := fun y _ => ((Real.hasDerivAt_exp y).const_mul XR).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => XR * Real.exp y) univ := by
    intro x _ y _ h
    exact Real.exp_injective (mul_left_cancel₀ hXR.ne' h)
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj
    (radialEnergyIntegrand d c amp eta XR)
  rw [radialCoordinate_image XR hXR, radialCoordinate_transform d c amp eta XR hXR,
    setIntegral_univ, integral_const_mul] at h
  exact h

/-- The actual reset coefficients and the actual energy estimates suffice;
the scalar amplitude has no assumed root or sign-change hypothesis. -/
theorem amplitude_spec {d : TailData} {K : ℝ} (w : ResetWitness d K) (hK : 0 < K)
    (hsmall : d.core.lam ≤ 1 / 120) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hscale : combinedScale d K ≤ 1 / 1000) :
    ContDiff ℝ ∞ (amplitude d w.coefficients) ∧ ∀ eta : ℝ, eta ^ 2 ≤ 1 →
      9 / 10 < amplitude d w.coefficients eta ∧ amplitude d w.coefficients eta < 6 / 5 ∧
      totalEnergy d w.coefficients (amplitude d w.coefficients eta) eta = 0 ∧
      |deriv (amplitude d w.coefficients) eta| ≤ 128 * combinedScale d K ∧
      (∀ A ∈ Icc (9 / 10 : ℝ) (6 / 5), totalEnergy d w.coefficients A eta = 0 →
        A = amplitude d w.coefficients eta) := by
  refine ⟨amplitude_contDiff d w.smooth, fun eta heta => ?_⟩
  have h := old_error_bounds d K hK hsmall hwait eta heta
  have hs := energyShift_bounds w hK eta heta
  have hr := amplitude_spec_of_bounds d w.coefficients eta (combinedScale d K) heta h hs.1 hscale
  have hT := (PulseAmplitude.normalizedTail_derivative_bound d eta heta).trans (oldScale_le d K hK)
  exact ⟨hr.1, hr.2.1, hr.2.2,
    amplitude_derivative_bound d w.smooth eta (combinedScale d K) heta h hs.1 hscale hT hs.2,
    fun A hA hz => amplitude_unique d w.coefficients eta (combinedScale d K) heta h hs.1 hscale A
        hA hz⟩

/-- The scheduled angular reset and pulse amplitude are constructed together.
The exact radial energy uses the corrected angular profile. The common
threshold is uniform over every terminal parameter `0 < h < lam/2`. -/
theorem exists_corrected_amplitude (P m : ℝ) (hP : 0 < P) :
    ∃ lam₀ K C : ℝ, 0 < lam₀ ∧ 0 < K ∧ 0 < C ∧ ∀ d : TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam₀ → ∃ w : ResetWitness d K,
        ContDiff ℝ ∞ (amplitude d w.coefficients) ∧ ∀ eta : ℝ, eta ^ 2 ≤ 1 →
          9 / 10 < amplitude d w.coefficients eta ∧ amplitude d w.coefficients eta < 6 / 5 ∧
          totalEnergy d w.coefficients (amplitude d w.coefficients eta) eta = 0 ∧
          |deriv (amplitude d w.coefficients) eta| ≤ C * d.core.lam * (1 + Real.log (1 /
              d.core.lam)) ∧
          (∀ XR : ℝ, 0 < XR →
            IntegrableOn (radialEnergyIntegrand d w.coefficients (amplitude d w.coefficients) eta
                XR) (Ioi 0) ∧
            (∫ X in Ioi 0, radialEnergyIntegrand d w.coefficients (amplitude d w.coefficients) eta
                XR X) = 0) ∧
          (∀ A ∈ Icc (9 / 10 : ℝ) (6 / 5), totalEnergy d w.coefficients A eta = 0 →
            A = amplitude d w.coefficients eta) := by
  obtain ⟨resetLam, K, hresetLam, hK, hreset⟩ := exists_scheduled_reset
  obtain ⟨delta, hd, hsmall⟩ := PulseAmplitude.exists_rate_threshold (combinedConstant P m K)
  refine ⟨min resetLam (min delta (1 / 120)), K, 128 * combinedConstant P m K,
    lt_min hresetLam (lt_min hd (by norm_num)), hK,
      mul_pos (by norm_num) (combinedConstant_pos hP m K hK), ?_⟩
  intro d hdP hdm hwait hlam
  have hr : d.core.lam < resetLam := lt_of_lt_of_le hlam (min_le_left _ _)
  have hright : d.core.lam < min delta (1 / 120) := lt_of_lt_of_le hlam (min_le_right _ _)
  have hl : d.core.lam ≤ 1 / 120 := (lt_of_lt_of_le hright (min_le_right _ _)).le
  have hscale : combinedScale d K ≤ 1 / 1000 := by
    unfold combinedScale
    rw [hdP, hdm]
    exact hsmall _ d.core.lam_pos (lt_of_lt_of_le hright (min_le_left _ _))
  obtain ⟨w⟩ := hreset d hr
  obtain ⟨hs, hspec⟩ := amplitude_spec w hK hl hwait hscale
  refine ⟨w, hs, fun eta heta => ?_⟩
  obtain ⟨ha, ha', hz, hderiv, huniq⟩ := hspec eta heta
  refine ⟨ha, ha', hz, ?_, ?_, huniq⟩
  · convert! hderiv using 1
    unfold combinedScale PulseAmplitude.logarithmicRate
    rw [hdP, hdm]
    ring
  · intro XR hXR
    refine ⟨radialEnergy_integrable d w.coefficients (amplitude d w.coefficients) eta XR hXR, ?_⟩
    rw [radialEnergy_integral d w.coefficients (amplitude d w.coefficients) eta XR hXR, hz,
        mul_zero]

end NavierStokes.CorrectedPulseAmplitude
