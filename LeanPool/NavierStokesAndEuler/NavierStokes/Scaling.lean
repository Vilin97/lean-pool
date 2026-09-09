/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Exact core and carrier scaling

Real-power identities and the integer-frequency estimate in Appendix A,
Proposition A.2 and Remark 8.6 of the candidate manuscript. These are scalar
scaling facts; they do not supply a Navier--Stokes solution or analytic estimates
for its profiles. The arbitrary envelope is kept in the carrier Reynolds product.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.Scaling

/-- The core velocity scale, with the fixed profile coefficient omitted. -/
def coreVelocity (q h : ℝ) : ℝ := q ^ (-(1 / 2 + h))

/-- The radial length scale. -/
def radialLength (q : ℝ) : ℝ := q ^ (1 / 2 : ℝ)

/-- The axial length scale. -/
def axialLength (q h : ℝ) : ℝ := q ^ (1 / 2 - h)

/-- Reynolds number at physical viscosity one. -/
def reynolds (velocity length : ℝ) : ℝ := velocity * length

theorem core_radial_reynolds {q : ℝ} (hq : 0 < q) (h : ℝ) :
    reynolds (coreVelocity q h) (radialLength q) = q ^ (-h) := by
  unfold reynolds coreVelocity radialLength
  rw [← Real.rpow_add hq]
  congr 1
  ring

theorem core_axial_reynolds {q : ℝ} (hq : 0 < q) (h : ℝ) :
    reynolds (coreVelocity q h) (axialLength q h) = q ^ (-2 * h) := by
  unfold reynolds coreVelocity axialLength
  rw [← Real.rpow_add hq]
  congr 1
  ring

/-- Dividing the diffusion scale by the inertial scale yields `Q ^ h`. -/
theorem normalized_viscosity {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    Q ^ (-(1 / 2 + h) - 1) / Q ^ (-2 * (1 / 2 + h) - 1 / 2) =
      Q ^ h := by
  rw [← Real.rpow_sub hQ]
  congr 1
  ring

theorem sqrt_viscosity {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    Real.sqrt (Q ^ h) = Q ^ (h / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQ.le]
  congr 1
  ring

/-- The physical amplitude prefactor of the primary wave. -/
theorem wave_amplitude_power {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    coreVelocity Q h * Real.sqrt (Q ^ h) = Q ^ (-1 / 2 - h / 2) := by
  rw [sqrt_viscosity hQ]
  unfold coreVelocity
  rw [← Real.rpow_add hQ]
  congr 1
  ring

/-- The continuum wavelength scale, before rounding the frequency. -/
theorem wave_length_power {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    radialLength Q * Real.sqrt (Q ^ h) = Q ^ (1 / 2 + h / 2) := by
  rw [sqrt_viscosity hQ]
  unfold radialLength
  rw [← Real.rpow_add hQ]

theorem wave_power_cancellation {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    Q ^ (-1 / 2 - h / 2) * Q ^ (1 / 2 + h / 2) = 1 := by
  rw [← Real.rpow_add hQ]
  have he : (-1 / 2 - h / 2) + (1 / 2 + h / 2) = (0 : ℝ) := by ring
  rw [he, Real.rpow_zero]

/-- The integer carrier frequency is the natural ceiling of `ε ^ (-1/2)`. -/
def carrierFrequency (ε : ℝ) : ℕ := ⌈ε ^ (-(1 / 2 : ℝ))⌉₊

theorem inverse_sqrt_power {ε : ℝ} (hε : 0 < ε) :
    ε ^ (-(1 / 2 : ℝ)) = (Real.sqrt ε)⁻¹ := by
  rw [Real.rpow_neg hε.le, Real.sqrt_eq_rpow]

/-- Integer rounding changes `k √ε` by at most `√ε`. -/
theorem carrier_frequency_sqrt_bounds {ε : ℝ} (hε : 0 < ε) :
    1 ≤ (carrierFrequency ε : ℝ) * Real.sqrt ε ∧
      (carrierFrequency ε : ℝ) * Real.sqrt ε ≤ 1 + Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hp : 0 ≤ ε ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hε _).le
  have hc : ε ^ (-(1 / 2 : ℝ)) * Real.sqrt ε = 1 := by
    rw [inverse_sqrt_power hε, inv_mul_cancel₀ hs.ne']
  constructor
  · have hl := mul_le_mul_of_nonneg_right
      (Nat.le_ceil (ε ^ (-(1 / 2 : ℝ)))) hs.le
    simpa only [carrierFrequency, hc] using hl
  · have hu := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hp).le hs.le
    calc
      (carrierFrequency ε : ℝ) * Real.sqrt ε ≤
          (ε ^ (-(1 / 2 : ℝ)) + 1) * Real.sqrt ε := hu
      _ = 1 + Real.sqrt ε := by rw [add_mul, hc, one_mul]

theorem carrier_frequency_pos {ε : ℝ} (hε : 0 < ε) :
    0 < (carrierFrequency ε : ℝ) := by
  have h := (carrier_frequency_sqrt_bounds hε).1
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  nlinarith

/-- The lower and upper viscosity bounds include the integer ceiling error. -/
theorem carrier_viscosity_bounds {ε : ℝ} (hε : 0 < ε) :
    1 ≤ ε * (carrierFrequency ε : ℝ) ^ 2 ∧
      ε * (carrierFrequency ε : ℝ) ^ 2 ≤ (1 + Real.sqrt ε) ^ 2 := by
  obtain ⟨hl, hu⟩ := carrier_frequency_sqrt_bounds hε
  have hk : 0 ≤ (carrierFrequency ε : ℝ) * Real.sqrt ε := by positivity
  have heq : ((carrierFrequency ε : ℝ) * Real.sqrt ε) ^ 2 =
      ε * (carrierFrequency ε : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hε.le]
    ring
  constructor
  · have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hk).mpr hl
    simpa only [one_pow, heq] using hsq
  · have hsq := (sq_le_sq₀ hk (by positivity : 0 ≤ 1 + Real.sqrt ε)).mpr hu
    simpa only [heq] using hsq

theorem one_add_sqrt_sq_le_four {ε : ℝ} (hε₁ : ε ≤ 1) :
    (1 + Real.sqrt ε) ^ 2 ≤ 4 := by
  have hs : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε₁
  have hs₀ := Real.sqrt_nonneg ε
  nlinarith

/-- The manuscript's complete inequality, for `0 < ε ≤ 1`. -/
theorem order_one_viscosity {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    1 ≤ ε * (carrierFrequency ε : ℝ) ^ 2 ∧
      ε * (carrierFrequency ε : ℝ) ^ 2 ≤ (1 + Real.sqrt ε) ^ 2 ∧
      (1 + Real.sqrt ε) ^ 2 ≤ 4 := by
  exact ⟨(carrier_viscosity_bounds hε).1, (carrier_viscosity_bounds hε).2,
    one_add_sqrt_sq_le_four hε₁⟩

theorem reciprocal_frequency_bounds {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    Real.sqrt ε / 2 ≤ 1 / (carrierFrequency ε : ℝ) ∧
      1 / (carrierFrequency ε : ℝ) ≤ Real.sqrt ε := by
  obtain ⟨hl, hu⟩ := carrier_frequency_sqrt_bounds hε
  have hk := carrier_frequency_pos hε
  have hs : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε₁
  constructor
  · apply (le_div_iff₀ hk).mpr
    nlinarith
  · apply (div_le_iff₀ hk).mpr
    nlinarith

/-- The physical wavelength with the actual integer carrier frequency. -/
def waveLength (Q h : ℝ) : ℝ :=
  radialLength Q / (carrierFrequency (Q ^ h) : ℝ)

/-- Integer rounding changes the nominal wavelength by a factor in `[1/2,1]`. -/
theorem wave_length_bounds {Q h : ℝ} (hQ : 0 < Q) (hε : Q ^ h ≤ 1) :
    Q ^ (1 / 2 + h / 2) / 2 ≤ waveLength Q h ∧
      waveLength Q h ≤ Q ^ (1 / 2 + h / 2) := by
  have hp : 0 < Q ^ h := Real.rpow_pos_of_pos hQ h
  obtain ⟨hl, hu⟩ := reciprocal_frequency_bounds hp hε
  have hr : 0 ≤ radialLength Q := (Real.rpow_pos_of_pos hQ _).le
  constructor
  · calc
      Q ^ (1 / 2 + h / 2) / 2 =
          radialLength Q * (Real.sqrt (Q ^ h) / 2) := by
        rw [← wave_length_power hQ h]
        ring
      _ ≤ radialLength Q * (1 / (carrierFrequency (Q ^ h) : ℝ)) :=
        mul_le_mul_of_nonneg_left hl hr
      _ = waveLength Q h := by simp [waveLength, div_eq_mul_inv]
  · calc
      waveLength Q h = radialLength Q * (1 / (carrierFrequency (Q ^ h) : ℝ)) := by
        simp [waveLength, div_eq_mul_inv]
      _ ≤ radialLength Q * Real.sqrt (Q ^ h) := mul_le_mul_of_nonneg_left hu hr
      _ = Q ^ (1 / 2 + h / 2) := wave_length_power hQ h

/-- The primary velocity includes an arbitrary real envelope coefficient. -/
def waveVelocity (Q h envelope : ℝ) : ℝ :=
  coreVelocity Q h * Real.sqrt (Q ^ h) * envelope

/-- Exact cancellation leaves the envelope and a bounded rounding factor. -/
theorem wave_reynolds_exact {Q : ℝ} (hQ : 0 < Q) (h envelope : ℝ) :
    reynolds (waveVelocity Q h envelope) (waveLength Q h) =
      envelope / ((carrierFrequency (Q ^ h) : ℝ) * Real.sqrt (Q ^ h)) := by
  have hp : 0 < Q ^ h := Real.rpow_pos_of_pos hQ h
  have hk := carrier_frequency_pos hp
  have hs : 0 < Real.sqrt (Q ^ h) := Real.sqrt_pos.mpr hp
  have hc : (coreVelocity Q h * Real.sqrt (Q ^ h)) *
      (radialLength Q * Real.sqrt (Q ^ h)) = 1 := by
    rw [wave_amplitude_power hQ h, wave_length_power hQ h,
      wave_power_cancellation hQ h]
  apply (eq_div_iff (mul_ne_zero hk.ne' hs.ne')).mpr
  unfold reynolds waveVelocity waveLength
  calc
    (coreVelocity Q h * Real.sqrt (Q ^ h) * envelope *
        (radialLength Q / (carrierFrequency (Q ^ h) : ℝ))) *
        ((carrierFrequency (Q ^ h) : ℝ) * Real.sqrt (Q ^ h)) =
        envelope * ((coreVelocity Q h * Real.sqrt (Q ^ h)) *
          (radialLength Q * Real.sqrt (Q ^ h))) := by
      field_simp
    _ = envelope := by rw [hc, mul_one]

/-- A positive envelope gives quantitative bounds with no extra power of `Q`. -/
theorem wave_reynolds_bounds {Q h envelope : ℝ} (hQ : 0 < Q)
    (hε : Q ^ h ≤ 1) (he : 0 ≤ envelope) :
    envelope / 2 ≤ reynolds (waveVelocity Q h envelope) (waveLength Q h) ∧
      reynolds (waveVelocity Q h envelope) (waveLength Q h) ≤ envelope := by
  rw [wave_reynolds_exact hQ]
  have hp : 0 < Q ^ h := Real.rpow_pos_of_pos hQ h
  obtain ⟨hl, hu⟩ := carrier_frequency_sqrt_bounds hp
  have hs : Real.sqrt (Q ^ h) ≤ 1 := Real.sqrt_le_one.mpr hε
  have hd : 0 < (carrierFrequency (Q ^ h) : ℝ) * Real.sqrt (Q ^ h) := by
    linarith
  have hd₂ : (carrierFrequency (Q ^ h) : ℝ) * Real.sqrt (Q ^ h) ≤ 2 := by
    linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg he (sub_nonneg.mpr hd₂)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg he (sub_nonneg.mpr hl)]

/-- The scaling computation does not imply a lower bound at envelope zeros. -/
theorem wave_reynolds_zero_envelope (Q h : ℝ) :
    reynolds (waveVelocity Q h 0) (waveLength Q h) = 0 := by
  simp [reynolds, waveVelocity]

end NavierStokes.Scaling
