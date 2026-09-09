/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingTail
public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalProfile
import LeanPool.NavierStokesAndEuler.NavierStokes.TailEnergyBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The pressure datum of the constructed outgoing angular schedule

This module instantiates the abstract pressure integral with `finalAngular`.
The pressure-neutral angular-moment correction remains a separate operation.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SchedulePressure

open Set Filter MeasureTheory
open OutgoingSchedule OutgoingTail
open scoped Topology ContDiff

/-- Squared clock amplitude, taken from the actual angular schedule at `η=0`. -/
noncomputable def clockWeight (d : TailData) (y : ℝ) : ℝ := finalAngular d (y, 0) ^ 2

/-- The shape exponent decreases from one to zero during flattening. -/
noncomputable def shapeExponent (d : TailData) (y : ℝ) : ℝ :=
  1 - sigma ((y - d.core.endpoint) / flattenLength)

/-- The datum computed directly from the complete constructed angular field. -/
noncomputable def axisPressure (d : TailData) (η : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ y, finalAngular d (y, η) ^ 2

theorem endpoint_pos (d : TailData) : 0 < d.core.endpoint := by
  dsimp [OutgoingSchedule.Parameters.endpoint]
  linarith [d.core.pulseStart_pos, d.core.pulseLength_pos]

theorem clockWeight_contDiff (d : TailData) : ContDiff ℝ ∞ (clockWeight d) :=
  ((finalAngular_contDiff d).comp (contDiff_id.prodMk contDiff_const)).pow 2

theorem clockWeight_pos (d : TailData) (y : ℝ) : 0 < clockWeight d y :=
  sq_pos_of_pos (finalAngular_pos d (y, 0))

theorem shapeExponent_contDiff (d : TailData) : ContDiff ℝ ∞ (shapeExponent d) :=
  contDiff_const.sub (sigma_contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const flattenLength))

theorem shapeExponent_bounds (d : TailData) (y : ℝ) :
    0 ≤ shapeExponent d y ∧ shapeExponent d y ≤ 1 := by
  dsimp [shapeExponent]
  constructor <;> linarith [sigma_nonneg ((y - d.core.endpoint) / flattenLength),
    sigma_le_one ((y - d.core.endpoint) / flattenLength)]

theorem shapeExponent_before (d : TailData) {y : ℝ} (hy : y ≤ d.core.endpoint) :
    shapeExponent d y = 1 := by
  have hs : (y - d.core.endpoint) / flattenLength ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) flattenLength_pos.le
  simp [shapeExponent, sigma_zero hs]

theorem shapeExponent_after (d : TailData) {y : ℝ} (hy : d.flattenEnd ≤ y) :
    shapeExponent d y = 0 := by
  have hs : 1 ≤ (y - d.core.endpoint) / flattenLength := by
    apply (le_div_iff₀ flattenLength_pos).mpr
    dsimp [TailData.flattenEnd] at hy
    linarith
  simp [shapeExponent, sigma_one hs]

theorem clockWeight_ideal (d : TailData) {y : ℝ} (hy : y ≤ 0) :
    clockWeight d y = d.core.P ^ 2 * Real.exp ((1 / 5 : ℝ) * y) := by
  have hE : finalAngular d (y, 0) = d.core.P * Real.exp (y / 10) := by
    rw [finalAngular_before d 0 (hy.trans (endpoint_pos d).le)]
    simpa [shape] using (angular_ideal (P := d.core.P) (eta := 0)
      (lam := d.core.lam) d.core.dropLength_pos.le hy)
  have he : Real.exp (y / 10) ^ 2 = Real.exp ((1 / 5 : ℝ) * y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [clockWeight, hE, mul_pow, he]

theorem shape_eq_exp (η : ℝ) :
    shape η = Real.exp (-Real.log (1 + η ^ 2)) := by
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 + η ^ 2)]
  rfl

/-- Exact shape separation of the complete angular schedule. -/
theorem angular_factorization (d : TailData) (y η : ℝ) :
    finalAngular d (y, η) = finalAngular d (y, 0) *
      Real.exp (-shapeExponent d y * Real.log (1 + η ^ 2)) := by
  let s := sigma ((y - d.core.endpoint) / flattenLength)
  have he : -Real.log (1 + η ^ 2) + s * (Real.log (1 + η ^ 2) - Real.log 2) =
      s * (-Real.log 2) + -(1 - s) * Real.log (1 + η ^ 2) := by ring
  have hfac : shape η * Real.exp (s * (Real.log (1 + η ^ 2) - Real.log 2)) =
      Real.exp (s * (-Real.log 2)) * Real.exp (-(1 - s) * Real.log (1 + η ^ 2)) := by
    rw [shape_eq_exp, ← Real.exp_add, he, Real.exp_add]
  unfold finalAngular flattened angular flattenFactor
  dsimp only
  change _ = _
  have h0 : shape (0 : ℝ) = 1 := by norm_num [shape]
  have hl0 : logShape (0 : ℝ) = 0 := by norm_num [logShape]
  rw [h0, hl0]
  simp only [mul_one, zero_sub]
  unfold logShape
  change _ = _
  dsimp only [shapeExponent]
  calc
    _ = (radialAmplitude d.core.P d.core.dropLength d.core.lam y *
      (shape η * Real.exp (s * (Real.log (1 + η ^ 2) - Real.log 2)))) *
        Real.exp (releaseAdjustment d (y - d.releaseStart)) *
          (tailShape d (y - tailStart d) / (1 - d.rho)) := by dsimp [s]; ring
    _ = _ := by rw [hfac]; ring

theorem angular_square_factorization (d : TailData) (y η : ℝ) :
    finalAngular d (y, η) ^ 2 =
      clockWeight d y * PressureDatum.kernel (shapeExponent d y) η := by
  rw [angular_factorization d y η, mul_pow]
  change clockWeight d y * _ = clockWeight d y * _
  congr 1
  rw [← Real.exp_nat_mul]
  unfold PressureDatum.kernel
  congr 1
  norm_num
  ring

theorem clockWeight_integrable_left (d : TailData) :
    IntegrableOn (clockWeight d) (Iic (0 : ℝ)) := by
  apply ((integrableOn_exp_mul_Iic (by norm_num : 0 < (1 / 5 : ℝ)) 0).const_mul
    (d.core.P ^ 2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
  exact (clockWeight_ideal d hy).symm

theorem clockWeight_integrable_right (d : TailData) :
    IntegrableOn (clockWeight d) (Ioi d.core.endpoint) := by
  apply (TailEnergyBounds.energyDensity_integrable_postPulse d 0).mono'
    (clockWeight_contDiff d).continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (clockWeight_pos d y)]
  have he : 1 ≤ Real.exp y := Real.one_le_exp_iff.mpr ((endpoint_pos d).le.trans hy.le)
  exact le_mul_of_one_le_left (clockWeight_pos d y).le he

theorem clockWeight_integrable (d : TailData) : Integrable (clockWeight d) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := d.core.endpoint), integrableOn_union]
  refine ⟨?_, clockWeight_integrable_right d⟩
  rw [← Iic_union_Ioc_eq_Iic (endpoint_pos d).le, integrableOn_union]
  exact ⟨clockWeight_integrable_left d, (clockWeight_contDiff d).continuous.integrableOn_Ioc⟩

/-- The actual schedule discharges all abstract weight/exponent hypotheses. -/
theorem admissible (d : TailData) :
    PressureDatum.Admissible (clockWeight d) (shapeExponent d) 1 where
  cap_nonneg := by norm_num
  integrable := clockWeight_integrable d
  nonneg := fun y => (clockWeight_pos d y).le
  measurable := (shapeExponent_contDiff d).continuous.measurable
  exponent_nonneg := fun y => (shapeExponent_bounds d y).1
  exponent_le := fun y => (shapeExponent_bounds d y).2

theorem axisPressure_eq (d : TailData) :
    axisPressure d = PressureDatum.pressure (clockWeight d) (shapeExponent d) := by
  funext η
  unfold axisPressure PressureDatum.pressure
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => angular_square_factorization d y η

theorem shapeExponent_ideal (d : TailData) {y : ℝ} (hy : y ≤ 0) :
    shapeExponent d y = 1 := shapeExponent_before d (hy.trans (endpoint_pos d).le)

theorem angular_square_integrable (d : TailData) (η : ℝ) :
    Integrable (fun y => finalAngular d (y, η) ^ 2) := by
  apply (PressureDatum.integrable_kernel (admissible d) η).congr
  exact Filter.Eventually.of_forall fun y => (angular_square_factorization d y η).symm

theorem axisPressure_contDiff (d : TailData) : ContDiff ℝ ∞ (axisPressure d) := by
  rw [axisPressure_eq]
  exact PressureDatum.pressure_contDiff (admissible d)

@[simp] theorem axisPressure_even (d : TailData) (η : ℝ) :
    axisPressure d (-η) = axisPressure d η := by
  rw [axisPressure_eq]
  exact PressureDatum.pressure_neg _ _ _

theorem axisPressure_lower_bound (d : TailData) (η : ℝ) :
    axisPressure d η ≤ -(5 / 2 : ℝ) * d.core.P ^ 2 * shape η ^ 2 := by
  rw [axisPressure_eq]
  exact PressureDatum.pressure_le_of_ideal_prefix (admissible d)
    (fun _ hy => clockWeight_ideal d hy) (fun _ hy => shapeExponent_ideal d hy) η

theorem positive_exponent_mass (d : TailData) :
    0 < ∫ y, clockWeight d y * shapeExponent d y :=
  PressureDatum.exponent_mass_pos_of_ideal_prefix (admissible d) d.core.P_pos
    (fun _ hy => clockWeight_ideal d hy) (fun _ hy => shapeExponent_ideal d hy)

theorem axisPressure_hasDerivAt (d : TailData) (η : ℝ) :
    HasDerivAt (axisPressure d)
      ((2 * η / (1 + η ^ 2)) *
        ∫ y, shapeExponent d y * finalAngular d (y, η) ^ 2) η := by
  rw [axisPressure_eq]
  have heq : (∫ y, shapeExponent d y * finalAngular d (y, η) ^ 2) =
      ∫ y, clockWeight d y * shapeExponent d y * PressureDatum.kernel (shapeExponent d y) η := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [angular_square_factorization]
      ring
  rw [heq]
  exact PressureDatum.hasDerivAt_pressure (admissible d) η

theorem axisPressure_deriv_pos (d : TailData) {η : ℝ} (hη : 0 < η) :
    0 < deriv (axisPressure d) η := by
  rw [axisPressure_eq]
  exact PressureDatum.deriv_pressure_pos (admissible d) (positive_exponent_mass d) hη

theorem axisPressure_deriv_neg (d : TailData) {η : ℝ} (hη : η < 0) :
    deriv (axisPressure d) η < 0 := by
  rw [axisPressure_eq]
  exact PressureDatum.deriv_pressure_neg (admissible d) (positive_exponent_mass d) hη

@[simp] theorem axisPressure_deriv_zero (d : TailData) : deriv (axisPressure d) 0 = 0 := by
  rw [axisPressure_eq]
  exact PressureDatum.deriv_pressure_zero (admissible d)

theorem axisPressure_neg (d : TailData) (η : ℝ) : axisPressure d η < 0 := by
  rw [axisPressure_eq]
  exact PressureDatum.pressure_neg_of_ideal_prefix (admissible d) d.core.P_pos
    (fun _ hy => clockWeight_ideal d hy) (fun _ hy => shapeExponent_ideal d hy) η

/-- Moving `X_R` translates the logarithmic clock and leaves the actual datum fixed. -/
theorem axisPressure_radius_independent (d : TailData) (X_R η : ℝ) :
    (-(1 / 2 : ℝ) * ∫ y, finalAngular d (y - Real.log X_R, η) ^ 2) = axisPressure d η := by
  unfold axisPressure
  simp only [sub_eq_add_neg]
  rw [integral_add_right_eq_self (fun y => finalAngular d (y, η) ^ 2) (-Real.log X_R)]

/-- Complex axis pressure, given by `PressureDatum.complexPressure (clockWeight d)
(shapeExponent d)`. -/
noncomputable def complexAxisPressure (d : TailData) : ℂ → ℂ :=
  PressureDatum.complexPressure (clockWeight d) (shapeExponent d)

theorem complexAxisPressure_analytic (d : TailData) :
    AnalyticOnNhd ℂ (complexAxisPressure d) PressureDatum.strip :=
  PressureDatum.complexPressure_analytic (admissible d)

@[simp] theorem complexAxisPressure_ofReal (d : TailData) (η : ℝ) :
    complexAxisPressure d (η : ℂ) = (axisPressure d η : ℂ) := by
  rw [axisPressure_eq]
  exact PressureDatum.complexPressure_ofReal _ _ _

theorem natural_axis_pressureData (d : TailData) (hP : 2 ≤ d.core.P) :
    NaturalAxisData.PressureData (axisPressure d) := by
  rw [axisPressure_eq]
  exact NaturalAxisData.pressureData_of_ideal_prefix (admissible d) hP
    (fun _ hy => clockWeight_ideal d hy) (fun _ hy => shapeExponent_ideal d hy)

/-- The analytic input is fixed first, followed by every sufficiently large
`Λ` and every normalization `C` above its constructed threshold. -/
theorem natural_profileFamily (d : TailData) {j : ℝ}
    (hsmall : NaturalAxisData.SmallParameters d.h j) (hP : 2 ≤ d.core.P) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1,
        |NaturalAxisData.Z d.h j (axisPressure d) η| ≤ δ →
          99 / 100 < NaturalAxisData.chi d.h j σ η) ∧
      ∃ data : NaturalAxisCoefficients.AnalyticInputs d.h j σ (axisPressure d),
        ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
          ∀ C : ℝ, data.normalizationThreshold Λ ≤ C →
            Nonempty (NaturalProfile.ProfileFamily data Λ C) := by
  rw [axisPressure_eq]
  exact NaturalProfile.ideal_prefix_profileFamily hsmall (admissible d) hP
    (fun _ hy => clockWeight_ideal d hy) (fun _ hy => shapeExponent_ideal d hy)

/-- The pressure of the actual outgoing schedule supplies the natural-axis theorem. -/
theorem exists_natural_profiles (d : TailData) {j : ℝ}
    (hsmall : NaturalAxisData.SmallParameters d.h j) (hP : 2 ≤ d.core.P) :
    ∃ δ σ Λ C : ℝ, 0 < δ ∧ 0 < σ ∧ 0 < Λ ∧ 0 < C ∧
      ∃ f U V Pr : ℝ × ℝ → ℝ,
        NaturalProfile.IsNaturalSolution d.h j Λ (axisPressure d)
          (NaturalAxisCoefficients.realAmplitude d.h j σ Λ C) f U V Pr ∧
        (∀ p ∈ NaturalProfile.domain Λ, 0 ≤ Λ * p.1 → Λ * p.1 ≤ 41 / 10 → 0 < f p) ∧
        (∀ η ∈ Icc (-1 : ℝ) 1,
          |NaturalAxisData.Z d.h j (axisPressure d) η| ≤ δ →
            23 / 10 < -2 * (4 / Λ) * NaturalAxisBridge.partialY f (4 / Λ, η) / f (4 / Λ, η)) := by
  rw [axisPressure_eq]
  exact NaturalProfile.exists_natural_profiles hsmall (admissible d) hP
    (fun _ hy => clockWeight_ideal d hy) (fun _ hy => shapeExponent_ideal d hy)

end NavierStokes.SchedulePressure
