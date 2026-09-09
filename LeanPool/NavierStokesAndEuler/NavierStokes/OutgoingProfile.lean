/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectedPulseAmplitude
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReleaseMoments
public import LeanPool.NavierStokesAndEuler.NavierStokes.SchedulePressure
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase

@[expose] public section

/-!
# A single outgoing profile before the heat-tail edit

The profile stores one actual scheduled angular-reset witness. Its axial
amplitude is the corrected energy root associated with that same witness.
All histories and pressures below are integrals of these fields.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

namespace NavierStokes.OutgoingProfile

/-- One reset, used by both the angular profile and the energy root. -/
structure Profile where
  data : TailData
  coefficientBound : ℝ
  reset : ResetWitness data coefficientBound

namespace Profile

def amp (F : Profile) : ℝ → ℝ :=
  CorrectedPulseAmplitude.amplitude F.data F.reset.coefficients

def logE (F : Profile) : ℝ × ℝ → ℝ :=
  correctedAngular F.data F.reset.coefficients

def logU (F : Profile) : ℝ × ℝ → ℝ := axial F.data.core F.amp

def E (F : Profile) (p : ℝ × ℝ) : ℝ := F.logE (Real.log p.1, p.2)

def U (F : Profile) (p : ℝ × ℝ) : ℝ := F.logU (Real.log p.1, p.2)

def H (F : Profile) (p : ℝ × ℝ) : ℝ := Real.sqrt (2 * p.1) * F.E p

def powerE (F : Profile) (X : ℝ) : ℝ :=
  powerConstant F.data * X ^ (-(1 / 2 + F.data.h))

def powerH (F : Profile) (X : ℝ) : ℝ := Real.sqrt (2 * X) * F.powerE X

def massWeight (F : Profile) (eta y : ℝ) : ℝ := Real.exp y * F.logU (y, eta)

def angularWeight (F : Profile) (eta y : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (3 * y / 2) * F.logE (y, eta) * F.logU (y, eta)

def M (F : Profile) (eta X : ℝ) : ℝ := ∫ u in Ioc 0 X, F.U (u, eta)

def J (F : Profile) (eta X : ℝ) : ℝ := ∫ u in Ioc 0 X, F.H (u, eta) * F.U (u, eta)

def energyDensity (F : Profile) (eta X : ℝ) : ℝ :=
  F.U (X, eta) ^ 2 - F.E (X, eta) ^ 2 / 2

def totalS (F : Profile) (eta : ℝ) : ℝ := ∫ X in Ioi 0, F.energyDensity eta X

def pressureWeight (F : Profile) (eta y : ℝ) : ℝ := F.logE (y, eta) ^ 2

def logPi (F : Profile) (p : ℝ × ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ y in Ioi p.1, F.pressureWeight p.2 y

def Pi (F : Profile) (p : ℝ × ℝ) : ℝ := F.logPi (Real.log p.1, p.2)

def axisDatum (F : Profile) (eta : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ y, F.pressureWeight eta y

def pressureChange (F : Profile) (eta y : ℝ) : ℝ :=
  F.pressureWeight eta y - finalAngular F.data (y, eta) ^ 2

theorem amp_contDiff (F : Profile) : ContDiff ℝ ∞ F.amp :=
  CorrectedPulseAmplitude.amplitude_contDiff F.data F.reset.smooth

theorem logE_contDiff (F : Profile) : ContDiff ℝ ∞ F.logE :=
  correctedAngular_contDiff F.data F.reset.coefficients F.reset.smooth

theorem logU_contDiff (F : Profile) : ContDiff ℝ ∞ F.logU :=
  axial_contDiff F.data.core F.amp_contDiff

theorem E_pos (F : Profile) (p : ℝ × ℝ) : 0 < F.E p :=
  F.reset.positive _

theorem logE_before (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ F.data.core.endpoint) :
    F.logE (y, eta) = angular F.data.core.P F.data.core.dropLength F.data.core.lam (y, eta) := by
  have hout : y ∉ Ioo (F.data.releaseStart - 4) F.data.releaseStart := by
    intro h
    linarith [last_four_after_flatten F.data, flattenEnd_gt_core F.data, h.1]
  rw [logE, correctedAngular_unchanged F.data F.reset.coefficients eta hout,
    finalAngular_before F.data eta hy]

theorem logE_ideal (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    F.logE (y, eta) = F.data.core.P * shape eta * Real.exp (y / 10) := by
  rw [F.logE_before eta (hy.trans (SchedulePressure.endpoint_pos F.data).le)]
  exact angular_ideal F.data.core.dropLength_pos.le hy

theorem logU_ideal (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    F.logU (y, eta) = 4 * eta := axial_ideal F.data.core F.amp eta hy

theorem logU_after (F : Profile) (eta : ℝ) {y : ℝ} (hy : F.data.core.endpoint ≤ y) :
    F.logU (y, eta) = 0 := axial_after_pulse F.data.core F.amp eta hy

theorem angular_product_unchanged (F : Profile) (eta y : ℝ) :
    F.logE (y, eta) * F.logU (y, eta) =
      angular F.data.core.P F.data.core.dropLength F.data.core.lam (y, eta) * F.logU (y, eta) := by
  by_cases hy : y ≤ F.data.core.endpoint
  · rw [F.logE_before eta hy]
  · rw [F.logU_after eta (le_of_not_ge hy)]
    simp

theorem logE_eventual (F : Profile) (eta : ℝ) {y : ℝ} (hy : tailEnd F.data ≤ y) :
    F.logE (y, eta) = powerConstant F.data * Real.exp (-(1 / 2 + F.data.h) * y) := by
  have hr : F.data.releaseStart ≤ y := by
    have ht := tailStart_gt_release F.data
    dsimp [tailEnd] at hy
    linarith
  rw [logE, ReleaseMoments.corrected_eq_release F.data F.reset.coefficients eta hr]
  exact finalAngular_eventual_power F.data 0 hy

theorem E_ideal (F : Profile) (eta : ℝ) {X : ℝ} (hX : 0 < X) (hX' : X ≤ 1) :
    F.E (X, eta) = F.data.core.P * shape eta * X ^ (1 / 10 : ℝ) := by
  rw [E, F.logE_ideal eta (Real.log_nonpos hX.le hX'), Real.rpow_def_of_pos hX]
  congr 2
  ring

theorem U_ideal (F : Profile) (eta : ℝ) {X : ℝ} (hX : 0 < X) (hX' : X ≤ 1) :
    F.U (X, eta) = 4 * eta := F.logU_ideal eta (Real.log_nonpos hX.le hX')

theorem E_eventual (F : Profile) (eta : ℝ) {X : ℝ} (hX : 0 < X)
    (hfar : tailEnd F.data ≤ Real.log X) : F.E (X, eta) = F.powerE X := by
  rw [E, F.logE_eventual eta hfar, powerE, Real.rpow_def_of_pos hX]
  congr 2
  ring

theorem U_after (F : Profile) (eta : ℝ) {X : ℝ}
    (hfar : F.data.core.endpoint ≤ Real.log X) : F.U (X, eta) = 0 := F.logU_after eta hfar

end Profile

def domain : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

theorem logarithmic_coordinates_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (Real.log p.1, p.2)) domain := by
  exact (contDiffOn_fst.log (fun p hp => ne_of_gt hp.1)).prodMk contDiffOn_snd

namespace Profile

theorem E_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ F.E domain :=
  F.logE_contDiff.comp_contDiffOn logarithmic_coordinates_contDiffOn

theorem U_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ F.U domain :=
  F.logU_contDiff.comp_contDiffOn logarithmic_coordinates_contDiffOn

theorem H_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ F.H domain := by
  exact ((contDiffOn_const.mul contDiffOn_fst).sqrt
    (fun p hp => ne_of_gt (mul_pos (by norm_num) hp.1))).mul F.E_contDiffOn

theorem pressureChange_zero (F : Profile) (eta : ℝ) {y : ℝ}
    (hy : y ∉ Ioo (F.data.releaseStart - 4) F.data.releaseStart) :
    F.pressureChange eta y = 0 := by
  simp [pressureChange, pressureWeight, logE,
    correctedAngular_unchanged F.data F.reset.coefficients eta hy]

theorem pressureChange_integrable (F : Profile) (eta : ℝ) : Integrable (F.pressureChange eta) := by
  have hc : Continuous (F.pressureChange eta) :=
    (((F.logE_contDiff.comp (contDiff_id.prodMk contDiff_const)).pow 2).sub
      (((finalAngular_contDiff F.data).comp (contDiff_id.prodMk contDiff_const)).pow 2)).continuous
  have hs : support (F.pressureChange eta) ⊆ Icc (F.data.releaseStart - 4) F.data.releaseStart := by
    intro y hy
    by_contra hn
    apply hy
    exact F.pressureChange_zero eta (fun hm => hn ⟨hm.1.le, hm.2.le⟩)
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs)

theorem pressureWeight_integrable (F : Profile) (eta : ℝ) : Integrable (F.pressureWeight eta) := by
  have h := (F.pressureChange_integrable eta).add (SchedulePressure.angular_square_integrable
    F.data eta)
  convert! h using 1
  funext y
  simp [pressureChange]

theorem pressureWeight_integral (F : Profile) (eta : ℝ) :
    (∫ y, F.pressureWeight eta y) = ∫ y, finalAngular F.data (y, eta) ^ 2 := by
  have h := F.reset.pressure_neutral eta
  change (∫ y, F.pressureWeight eta y - finalAngular F.data (y, eta) ^ 2) = 0 at h
  rw [integral_sub (F.pressureWeight_integrable eta) (SchedulePressure.angular_square_integrable
    F.data eta)] at h
  linarith

theorem axisDatum_eq (F : Profile) : F.axisDatum = SchedulePressure.axisPressure F.data := by
  funext eta
  exact congrArg (fun a : ℝ => -(1 / 2 : ℝ) * a) (F.pressureWeight_integral eta)

theorem axisDatum_contDiff (F : Profile) : ContDiff ℝ ∞ F.axisDatum := by
  rw [F.axisDatum_eq]
  exact SchedulePressure.axisPressure_contDiff F.data

theorem axisDatum_analytic_extension (F : Profile) :
    AnalyticOnNhd ℂ (SchedulePressure.complexAxisPressure F.data) PressureDatum.strip ∧
      ∀ eta : ℝ, SchedulePressure.complexAxisPressure F.data (eta : ℂ) = (F.axisDatum eta : ℂ) := by
  refine ⟨SchedulePressure.complexAxisPressure_analytic F.data, ?_⟩
  intro eta
  rw [F.axisDatum_eq, SchedulePressure.complexAxisPressure_ofReal]

theorem natural_axis_pressureData (F : Profile) (hP : 2 ≤ F.data.core.P) :
    NaturalAxisData.PressureData F.axisDatum := by
  rw [F.axisDatum_eq]
  exact SchedulePressure.natural_axis_pressureData F.data hP

end Profile

/-- Actual incoming exponential tails, integrated through any nonnegative
clock time. No finite-prefix constant is an additional assumption. -/
theorem exponential_prefix_integral (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (hb : 0 < b) (he : ∀ y ≤ 0, f y = a * Real.exp (b * y))
    {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn f (Iic y) ∧ (∫ t in Iic y, f t) = a / b + ∫ t in (0 : ℝ)..y, f t := by
  have h0 : IntegrableOn f (Iic (0 : ℝ)) :=
    IntegrableOn.congr_fun ((integrableOn_exp_mul_Iic hb 0).const_mul a)
      (fun t ht => (he t ht).symm) measurableSet_Iic
  have hi : IntegrableOn f (Iic y) := by
    rw [← Iic_union_Ioc_eq_Iic hy]
    exact h0.union hf.integrableOn_Ioc
  have hv : (∫ t in Iic (0 : ℝ), f t) = a / b := by
    calc
      _ = ∫ t in Iic (0 : ℝ), a * Real.exp (b * t) :=
        setIntegral_congr_fun measurableSet_Iic (fun t ht => he t ht)
      _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hb]; simp [div_eq_mul_inv]
  refine ⟨hi, ?_⟩
  have h := intervalIntegral.integral_Iic_sub_Iic h0 hi
  rw [hv] at h
  linarith

/-- Compact parameter integration supplies joint smoothness of the actual
variable-endpoint primitive. -/
theorem primitive_joint_contDiff (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..p.1, f (t, p.2)) := by
  let G : (ℝ × ℝ) × ℝ → ℝ := fun z => f (z.1.1 * z.2, z.1.2)
  have hG : ContDiff ℝ ∞ G :=
    hf.comp ((contDiff_fst.fst.mul contDiff_snd).prodMk contDiff_fst.snd)
  have hi : ContDiff ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, G (p, t)) :=
    contDiffOn_univ.mp (ParametricRephase.intervalIntegral_contDiffOn_of_joint G univ
      isOpen_univ hG.contDiffOn 0 1 (by norm_num))
  have he : (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..p.1, f (t, p.2)) =
      (fun p => p.1 * ∫ t in (0 : ℝ)..1, G (p, t)) := by
    funext p
    simpa only [G, smul_eq_mul, mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left (fun t => f (t, p.2)) p.1
        (a := 0) (b := 1)).symm
  rw [he]
  exact contDiff_fst.mul hi

namespace Profile

theorem massWeight_continuous (F : Profile) (eta : ℝ) : Continuous (F.massWeight eta) :=
  Real.continuous_exp.mul ((F.logU_contDiff.comp (contDiff_id.prodMk contDiff_const)).continuous)

theorem angularWeight_continuous (F : Profile) (eta : ℝ) : Continuous (F.angularWeight eta) :=
  (((contDiff_const.mul ((contDiff_const.mul contDiff_id).div_const 2).exp).mul
    (F.logE_contDiff.comp (contDiff_id.prodMk contDiff_const))).mul
      (F.logU_contDiff.comp (contDiff_id.prodMk contDiff_const))).continuous

theorem massWeight_ideal (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    F.massWeight eta y = (4 * eta) * Real.exp (1 * y) := by
  simp only [massWeight, F.logU_ideal eta hy, one_mul]
  ring

theorem angularWeight_ideal (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    F.angularWeight eta y = (4 * Real.sqrt 2 * F.data.core.P * eta * shape eta) *
      Real.exp ((8 / 5 : ℝ) * y) := by
  have hw := ReleaseMoments.correctedWeight_ideal F.data F.reset.coefficients eta hy
  change Real.exp (3 * y / 2) * F.logE (y, eta) = _ at hw
  rw [angularWeight, F.logU_ideal eta hy, mul_assoc (Real.sqrt 2), hw]
  ring

theorem massWeight_integral_Iic (F : Profile) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (F.massWeight eta) (Iic y) ∧
      (∫ t in Iic y, F.massWeight eta t) = massMoment F.data.core F.amp eta y := by
  have h := exponential_prefix_integral (F.massWeight eta) (F.massWeight_continuous eta)
    (4 * eta) 1 (by norm_num) (fun _ ht => F.massWeight_ideal eta ht) hy
  simpa only [div_one, massMoment, massWeight, logU] using h

theorem angularWeight_integral_Iic (F : Profile) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (F.angularWeight eta) (Iic y) ∧
      (∫ t in Iic y, F.angularWeight eta t) = angularMoment F.data.core F.amp eta y := by
  have h := exponential_prefix_integral (F.angularWeight eta) (F.angularWeight_continuous eta)
    (4 * Real.sqrt 2 * F.data.core.P * eta * shape eta) (8 / 5) (by norm_num)
      (fun _ ht => F.angularWeight_ideal eta ht) hy
  refine ⟨h.1, h.2.trans ?_⟩
  have he : (∫ t in (0 : ℝ)..y, F.angularWeight eta t) =
      ∫ t in (0 : ℝ)..y, Real.sqrt 2 * Real.exp (3 * t / 2) *
        angular F.data.core.P F.data.core.dropLength F.data.core.lam (t, eta) * F.logU (t, eta) :=
          by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [angularWeight]
    simpa only [mul_assoc] using congrArg (fun z => Real.sqrt 2 * Real.exp (3 * t / 2) * z)
      (F.angular_product_unchanged eta t)
  rw [he]
  unfold angularMoment logU
  ring

theorem massWeight_integrable (F : Profile) (eta : ℝ) : Integrable (F.massWeight eta) := by
  apply (F.massWeight_integral_Iic eta (SchedulePressure.endpoint_pos
    F.data).le).1.integrable_of_forall_notMem_eq_zero
  intro y hy
  simp [massWeight, F.logU_after eta (le_of_lt (not_le.mp hy))]

theorem angularWeight_integrable (F : Profile) (eta : ℝ) : Integrable (F.angularWeight eta) := by
  apply (F.angularWeight_integral_Iic eta (SchedulePressure.endpoint_pos
    F.data).le).1.integrable_of_forall_notMem_eq_zero
  intro y hy
  simp [angularWeight, F.logU_after eta (le_of_lt (not_le.mp hy))]

theorem massWeight_integral_zero (F : Profile) (eta : ℝ) : (∫ y, F.massWeight eta y) = 0 := by
  have h : (∫ y in Iic F.data.core.endpoint, F.massWeight eta y) = ∫ y, F.massWeight eta y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp [massWeight, F.logU_after eta (le_of_lt (not_le.mp hy))]
  rw [← h, (F.massWeight_integral_Iic eta (SchedulePressure.endpoint_pos F.data).le).2]
  exact massMoment_endpoint F.data.core F.amp eta

theorem angularWeight_integral_zero (F : Profile) (eta : ℝ) : (∫ y, F.angularWeight eta y) = 0 := by
  have h : (∫ y in Iic F.data.core.endpoint, F.angularWeight eta y) = ∫ y, F.angularWeight eta y :=
    by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp [angularWeight, F.logU_after eta (le_of_lt (not_le.mp hy))]
  rw [← h, (F.angularWeight_integral_Iic eta (SchedulePressure.endpoint_pos F.data).le).2]
  exact angularMoment_endpoint F.data.core F.amp eta

theorem pressureWeight_ideal (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    F.pressureWeight eta y = (F.data.core.P ^ 2 * shape eta ^ 2) * Real.exp ((1 / 5 : ℝ) * y) := by
  simp only [pressureWeight, F.logE_ideal eta hy, mul_pow]
  rw [pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

theorem pressureWeight_integral_ideal (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    (∫ t in Iic y, F.pressureWeight eta t) =
      5 * F.data.core.P ^ 2 * shape eta ^ 2 * Real.exp (y / 5) := by
  calc
    _ = ∫ t in Iic y, (F.data.core.P ^ 2 * shape eta ^ 2) * Real.exp ((1 / 5 : ℝ) * t) :=
      setIntegral_congr_fun measurableSet_Iic (fun t ht => F.pressureWeight_ideal eta (ht.trans hy))
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 5)]
      have he : (1 / 5 : ℝ) * y = y / 5 := by ring
      rw [he]
      ring

theorem logPi_eq_primitive (F : Profile) (y eta : ℝ) :
    F.logPi (y, eta) = F.axisDatum eta + (5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2 +
      (1 / 2) * ∫ t in (0 : ℝ)..y, F.pressureWeight eta t := by
  have hi := F.pressureWeight_integrable eta
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (hi.integrableOn (s := Iic y)) (hi.integrableOn (s := Ioi y))
  have hd := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn (s := Iic (0 : ℝ))) (hi.integrableOn (s := Iic y))
  rw [F.pressureWeight_integral_ideal eta le_rfl] at hd
  norm_num only [zero_div, Real.exp_zero, mul_one] at hd
  dsimp only [logPi, axisDatum]
  linarith

theorem logPi_contDiff (F : Profile) : ContDiff ℝ ∞ F.logPi := by
  have he : F.logPi = fun p : ℝ × ℝ =>
      F.axisDatum p.2 + (5 / 2) * F.data.core.P ^ 2 * shape p.2 ^ 2 +
        (1 / 2) * ∫ t in (0 : ℝ)..p.1, F.pressureWeight p.2 t := by
    funext p
    exact F.logPi_eq_primitive p.1 p.2
  rw [he]
  exact ((F.axisDatum_contDiff.comp contDiff_snd).add
    (contDiff_const.mul ((shape_contDiff.comp contDiff_snd).pow 2))).add
      (contDiff_const.mul (primitive_joint_contDiff (fun p => F.logE p ^ 2) (F.logE_contDiff.pow
        2)))

theorem Pi_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ F.Pi domain :=
  F.logPi_contDiff.comp_contDiffOn logarithmic_coordinates_contDiffOn

theorem logPi_ideal (F : Profile) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    F.logPi (y, eta) = F.axisDatum eta +
      (5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2 * Real.exp (y / 5) := by
  have hi := F.pressureWeight_integrable eta
  have hs := intervalIntegral.integral_Iic_add_Ioi
    (hi.integrableOn (s := Iic y)) (hi.integrableOn (s := Ioi y))
  rw [F.pressureWeight_integral_ideal eta hy] at hs
  dsimp only [logPi, axisDatum]
  linarith

theorem Pi_ideal (F : Profile) (eta : ℝ) {X : ℝ} (hX : 0 < X) (hX' : X ≤ 1) :
    F.Pi (X, eta) = F.axisDatum eta +
      (5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2 * X ^ (1 / 5 : ℝ) := by
  rw [Pi, F.logPi_ideal eta (Real.log_nonpos hX.le hX'), Real.rpow_def_of_pos hX]
  congr 3
  ring

theorem mass_comp_exp (F : Profile) (eta y : ℝ) :
    |Real.exp y| • F.U (Real.exp y, eta) = F.massWeight eta y := by
  simp only [abs_of_pos (Real.exp_pos y), smul_eq_mul, U, Real.log_exp, massWeight]

theorem angular_comp_exp (F : Profile) (eta y : ℝ) :
    |Real.exp y| • (F.H (Real.exp y, eta) * F.U (Real.exp y, eta)) = F.angularWeight eta y := by
  simp only [abs_of_pos (Real.exp_pos y), smul_eq_mul, H, E, U, Real.log_exp, angularWeight]
  rw [← mul_assoc (Real.exp y), ← mul_assoc (Real.exp y), ReleaseMoments.exponential_radial_weight]

theorem mass_integrable (F : Profile) (eta : ℝ) :
    IntegrableOn (fun X => F.U (X, eta)) (Ioi 0) := by
  rw [← Real.range_exp, ← image_univ]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn _).mpr
  simp_rw [F.mass_comp_exp]
  exact (F.massWeight_integrable eta).integrableOn

theorem angular_integrable (F : Profile) (eta : ℝ) :
    IntegrableOn (fun X => F.H (X, eta) * F.U (X, eta)) (Ioi 0) := by
  rw [← Real.range_exp, ← image_univ]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn _).mpr
  simp_rw [F.angular_comp_exp]
  exact (F.angularWeight_integrable eta).integrableOn

theorem mass_integral_zero (F : Profile) (eta : ℝ) :
    (∫ X in Ioi 0, F.U (X, eta)) = 0 := by
  rw [← Real.range_exp, ← image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [F.mass_comp_exp]
  rw [setIntegral_univ, F.massWeight_integral_zero]

theorem angular_integral_zero (F : Profile) (eta : ℝ) :
    (∫ X in Ioi 0, F.H (X, eta) * F.U (X, eta)) = 0 := by
  rw [← Real.range_exp, ← image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [F.angular_comp_exp]
  rw [setIntegral_univ, F.angularWeight_integral_zero]

theorem M_at_exp (F : Profile) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    F.M eta (Real.exp y) = massMoment F.data.core F.amp eta y := by
  rw [M, ← ReleaseMoments.image_exp_Iic,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [F.mass_comp_exp]
  exact (F.massWeight_integral_Iic eta hy).2

theorem J_at_exp (F : Profile) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    F.J eta (Real.exp y) = angularMoment F.data.core F.amp eta y := by
  rw [J, ← ReleaseMoments.image_exp_Iic,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [F.angular_comp_exp]
  exact (F.angularWeight_integral_Iic eta hy).2

theorem moments_after (F : Profile) (eta : ℝ) {X : ℝ} (hX : 0 < X)
    (hfar : F.data.core.endpoint ≤ Real.log X) : F.M eta X = 0 ∧ F.J eta X = 0 := by
  have hy : 0 ≤ Real.log X := (SchedulePressure.endpoint_pos F.data).le.trans hfar
  have hM := F.M_at_exp eta hy
  have hJ := F.J_at_exp eta hy
  rw [Real.exp_log hX, massMoment_after_pulse F.data.core F.amp eta hfar] at hM
  rw [Real.exp_log hX, angularMoment_after_pulse F.data.core F.amp eta hfar] at hJ
  exact ⟨hM, hJ⟩

theorem energyDensity_eq (F : Profile) (eta : ℝ) :
    F.energyDensity eta = CorrectedPulseAmplitude.radialEnergyIntegrand F.data F.reset.coefficients
      F.amp eta 1 := by
  funext X
  simp only [energyDensity, E, U, logE, logU, CorrectedPulseAmplitude.radialEnergyIntegrand,
    div_one]

theorem energy_integrable (F : Profile) (eta : ℝ) : IntegrableOn (F.energyDensity eta) (Ioi 0) := by
  rw [F.energyDensity_eq]
  exact CorrectedPulseAmplitude.radialEnergy_integrable F.data F.reset.coefficients F.amp eta 1 (by
    norm_num)

theorem totalS_eq (F : Profile) (eta : ℝ) :
    F.totalS eta = CorrectedPulseAmplitude.totalEnergy F.data F.reset.coefficients (F.amp eta) eta
      := by
  unfold totalS
  rw [F.energyDensity_eq, CorrectedPulseAmplitude.radialEnergy_integral F.data F.reset.coefficients
    F.amp eta 1 (by norm_num), one_mul]

theorem renormalized_integrable (F : Profile) (eta : ℝ) :
    IntegrableOn (fun X => F.H (X, eta) - F.powerH X) (Ioi 0) :=
  ReleaseMoments.ResetWitness.renormalized_radial_integrable F.reset eta

theorem renormalized_angular_moment (F : Profile) (eta : ℝ) :
    (∫ X in Ioi 0, F.H (X, eta) - F.powerH X) = 0 :=
  ReleaseMoments.ResetWitness.renormalized_angular_moment F.reset eta

theorem angular_history_eventual (F : Profile) (eta : ℝ) {X : ℝ} (hX : 0 < X)
    (hfar : tailEnd F.data ≤ Real.log X) :
    (∫ u in Ioc 0 X, F.H (u, eta)) = X * F.H (X, eta) / (1 - F.data.h) :=
  ReleaseMoments.ResetWitness.radial_history_eventual F.reset eta hX hfar

theorem Pi_tendsto_axis (F : Profile) (eta : ℝ) :
    Tendsto (fun X => F.Pi (X, eta)) (𝓝[>] (0 : ℝ)) (𝓝 (F.axisDatum eta)) := by
  have hp : Tendsto (fun X : ℝ => X ^ (1 / 5 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : ContinuousAt (fun X : ℝ => X ^ (1 / 5 : ℝ)) 0 :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 5)).continuousAt
    simpa only [Real.zero_rpow (by norm_num : (1 / 5 : ℝ) ≠ 0)] using
      h.continuousWithinAt.tendsto (s := Ioi (0 : ℝ))
  have he : (fun X => F.Pi (X, eta)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun X => F.axisDatum eta + (5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2 * X ^ (1 / 5 : ℝ)) :=
        by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0
      : ℝ) < 1))] with X hX hX'
    exact F.Pi_ideal eta hX hX'.le
  have ht : Tendsto
      (fun X => F.axisDatum eta + (5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2 * X ^ (1 / 5 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (F.axisDatum eta + (5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2 * 0)) :=
    tendsto_const_nhds.add (hp.const_mul ((5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2))
  simpa only [mul_zero, add_zero] using ht.congr' he.symm

end Profile

theorem image_exp_Ioi (y : ℝ) : Real.exp '' Ioi y = Ioi (Real.exp y) := by
  ext X
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact Real.exp_lt_exp.mpr ht
  · intro hX
    have hp : 0 < X := (Real.exp_pos y).trans hX
    refine ⟨Real.log X, ?_, Real.exp_log hp⟩
    exact Real.exp_lt_exp.mp (by rw [Real.exp_log hp]; exact hX)

namespace Profile

def canonicalKernel (F : Profile) (eta X : ℝ) : ℝ := F.E (X, eta) ^ 2 / X

theorem canonicalKernel_comp_exp (F : Profile) (eta y : ℝ) :
    |Real.exp y| • F.canonicalKernel eta (Real.exp y) = F.pressureWeight eta y := by
  simp only [abs_of_pos (Real.exp_pos y), smul_eq_mul, canonicalKernel, E, Real.log_exp,
    pressureWeight]
  field_simp

theorem canonicalKernel_integrable (F : Profile) (eta : ℝ) :
    IntegrableOn (F.canonicalKernel eta) (Ioi 0) := by
  rw [← Real.range_exp, ← image_univ]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn _).mpr
  simp_rw [F.canonicalKernel_comp_exp]
  exact (F.pressureWeight_integrable eta).integrableOn

theorem Pi_canonical (F : Profile) (eta : ℝ) {X : ℝ} (hX : 0 < X) :
    F.Pi (X, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X, F.E (u, eta) ^ 2 / u := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun y (_ : y ∈ Ioi (Real.log X)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (F.canonicalKernel eta)
  rw [image_exp_Ioi, Real.exp_log hX] at h
  simp_rw [F.canonicalKernel_comp_exp] at h
  change -(1 / 2 : ℝ) * (∫ y in Ioi (Real.log X), F.pressureWeight eta y) = _
  rw [← h]
  rfl

theorem tailEnd_after_endpoint (F : Profile) : F.data.core.endpoint ≤ tailEnd F.data := by
  have hf := flattenEnd_gt_core F.data
  have hr := releaseStart_gt_flattenEnd F.data
  have ht := tailStart_gt_release F.data
  dsimp only [tailEnd]
  linarith

end Profile

/-- All fields in this specification refer to one `Profile`, hence one reset
and its associated corrected energy root. -/
structure Specification (F : Profile) (C : ℝ) : Prop where
  amplitude_smooth : ContDiff ℝ ∞ F.amp
  angular_smooth : ContDiffOn ℝ ∞ F.E domain
  axial_smooth : ContDiffOn ℝ ∞ F.U domain
  momentum_smooth : ContDiffOn ℝ ∞ F.H domain
  pressure_smooth : ContDiffOn ℝ ∞ F.Pi domain
  angular_positive : ∀ p ∈ domain, 0 < F.E p
  amplitude_bounds : ∀ eta : ℝ, eta ^ 2 ≤ 1 →
    9 / 10 < F.amp eta ∧ F.amp eta < 6 / 5 ∧
      |deriv F.amp eta| ≤ C * F.data.core.lam * (1 + Real.log (1 / F.data.core.lam))
  mass_integrable : ∀ eta : ℝ, IntegrableOn (fun X => F.U (X, eta)) (Ioi 0)
  angular_integrable : ∀ eta : ℝ, IntegrableOn (fun X => F.H (X, eta) * F.U (X, eta)) (Ioi 0)
  mass_total_zero : ∀ eta : ℝ, (∫ X in Ioi 0, F.U (X, eta)) = 0
  angular_total_zero : ∀ eta : ℝ, (∫ X in Ioi 0, F.H (X, eta) * F.U (X, eta)) = 0
  after_pulse : ∀ eta X : ℝ, 0 < X → F.data.core.endpoint ≤ Real.log X →
    F.U (X, eta) = 0 ∧ F.M eta X = 0 ∧ F.J eta X = 0
  energy_integrable : ∀ eta : ℝ, IntegrableOn (F.energyDensity eta) (Ioi 0)
  energy_zero : ∀ eta : ℝ, eta ^ 2 ≤ 1 → F.totalS eta = 0
  renormalized_integrable : ∀ eta : ℝ, IntegrableOn (fun X => F.H (X, eta) - F.powerH X) (Ioi 0)
  renormalized_zero : ∀ eta : ℝ, (∫ X in Ioi 0, F.H (X, eta) - F.powerH X) = 0
  eventual_power : ∀ eta X : ℝ, 0 < X → tailEnd F.data ≤ Real.log X →
    F.U (X, eta) = 0 ∧ F.E (X, eta) = F.powerE X ∧
      (∫ u in Ioc 0 X, F.H (u, eta)) = X * F.H (X, eta) / (1 - F.data.h)
  ideal_prefix : ∀ eta X : ℝ, 0 < X → X ≤ 1 →
    F.E (X, eta) = F.data.core.P * shape eta * X ^ (1 / 10 : ℝ) ∧
    F.U (X, eta) = 4 * eta ∧
    F.Pi (X, eta) = F.axisDatum eta + (5 / 2) * F.data.core.P ^ 2 * shape eta ^ 2 * X ^ (1 / 5 : ℝ)
  pressure_integrable : ∀ eta : ℝ, IntegrableOn (F.canonicalKernel eta) (Ioi 0)
  pressure_canonical : ∀ eta X : ℝ, 0 < X →
    F.Pi (X, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X, F.E (u, eta) ^ 2 / u
  same_axis_datum : F.axisDatum = SchedulePressure.axisPressure F.data
  axis_limit : ∀ eta : ℝ, Tendsto (fun X => F.Pi (X, eta)) (𝓝[>] (0 : ℝ)) (𝓝 (F.axisDatum eta))
  analytic_axis_datum : AnalyticOnNhd ℂ (SchedulePressure.complexAxisPressure F.data)
    PressureDatum.strip ∧
    ∀ eta : ℝ, SchedulePressure.complexAxisPressure F.data (eta : ℂ) = (F.axisDatum eta : ℂ)

/-- Assemble the actual fields from the same witness returned by the corrected
amplitude construction. The smallness threshold is uniform in the tail `h`. -/
theorem exists_profile_for_data (P m : ℝ) (hP : 0 < P) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ d : TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam₀ → ∃ F : Profile, F.data = d ∧ Specification F C := by
  obtain ⟨lam₀, K, C, hlam₀, _hK, hC, hc⟩ :=
    CorrectedPulseAmplitude.exists_corrected_amplitude P m hP
  refine ⟨lam₀, C, hlam₀, hC, ?_⟩
  intro d hdP hdm hwait hlam
  obtain ⟨w, hs, hspec⟩ := hc d hdP hdm hwait hlam
  let F : Profile := ⟨d, K, w⟩
  refine ⟨F, rfl, {
    amplitude_smooth := F.amp_contDiff
    angular_smooth := F.E_contDiffOn
    axial_smooth := F.U_contDiffOn
    momentum_smooth := F.H_contDiffOn
    pressure_smooth := F.Pi_contDiffOn
    angular_positive := fun p _ => F.E_pos p
    amplitude_bounds := ?_
    mass_integrable := F.mass_integrable
    angular_integrable := F.angular_integrable
    mass_total_zero := F.mass_integral_zero
    angular_total_zero := F.angular_integral_zero
    after_pulse := fun eta X hX hfar => ⟨F.U_after eta hfar, F.moments_after eta hX hfar⟩
    energy_integrable := F.energy_integrable
    energy_zero := ?_
    renormalized_integrable := F.renormalized_integrable
    renormalized_zero := F.renormalized_angular_moment
    eventual_power := fun eta X hX hfar =>
      ⟨F.U_after eta (F.tailEnd_after_endpoint.trans hfar), F.E_eventual eta hX hfar,
        F.angular_history_eventual eta hX hfar⟩
    ideal_prefix := fun eta X hX hX' =>
      ⟨F.E_ideal eta hX hX', F.U_ideal eta hX hX', F.Pi_ideal eta hX hX'⟩
    pressure_integrable := F.canonicalKernel_integrable
    pressure_canonical := fun eta X hX => F.Pi_canonical eta hX
    same_axis_datum := F.axisDatum_eq
    axis_limit := F.Pi_tendsto_axis
    analytic_axis_datum := F.axisDatum_analytic_extension }⟩
  · intro eta heta
    obtain ⟨ha, ha', _, hd, _⟩ := hspec eta heta
    exact ⟨ha, ha', hd⟩
  · intro eta heta
    rw [F.totalS_eq]
    exact (hspec eta heta).2.2.1

/-- Choose `lam` after the fixed prefix parameters, and then any permitted
`h`. The actual outgoing profile has every exact pre-heat moment constraint. -/
theorem exists_outgoing_profile (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ lam : ℝ,
      0 < lam → lam < lam₀ → ∀ h : ℝ, 0 < h → 2 * h < lam →
      ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧
        F.data.core.lam = lam ∧ F.data.h = h ∧
        F.data.core.wait = 60 * Real.log (1 / lam) ∧ Specification F C := by
  obtain ⟨lam₀, C, hlam₀, hC, hc⟩ := exists_profile_for_data P m hP
  refine ⟨min lam₀ (1 / 10), C, lt_min hlam₀ (by norm_num), hC, ?_⟩
  intro lam hlam hlam' h hh hsmall
  have hl : lam < 1 / 10 := lt_of_lt_of_le hlam' (min_le_right _ _)
  let d : TailData := ⟨paperParameters P m lam hP hm hlam hl, h, hh, hsmall⟩
  obtain ⟨F, hF, hs⟩ := hc d rfl rfl rfl (lt_of_lt_of_le hlam' (min_le_left _ _))
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, hs⟩ <;> rw [hF] <;> rfl

/-- A single positive schedule parameter works before the terminal parameter
is selected. -/
theorem exists_fixed_lambda (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ lam C : ℝ, 0 < lam ∧ 0 < C ∧ ∀ h : ℝ, 0 < h → 2 * h < lam →
      ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧
        F.data.core.lam = lam ∧ F.data.h = h ∧ Specification F C := by
  obtain ⟨lam₀, C, hlam₀, hC, hc⟩ := exists_outgoing_profile P m hP hm
  refine ⟨lam₀ / 2, C, half_pos hlam₀, hC, ?_⟩
  intro h hh hsmall
  obtain ⟨F, hP', hm', hl', hh', _, hs⟩ :=
    hc (lam₀ / 2) (half_pos hlam₀) (by linarith) h hh hsmall
  exact ⟨F, hP', hm', hl', hh', hs⟩

end NavierStokes.OutgoingProfile
