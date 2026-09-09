/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scalar identities for the outgoing radial schedule

This file verifies the ideal-prefix source and its lower bound, the exponential
weights of the axial moment rows, their two-column algebraic reset, the negative
energy term in equation (13), and the constant-coefficient lag equation.

These finite-dimensional calculations do not establish existence of the full
smooth schedule, estimates on the correction bumps, or the stress-cone bounds.
-/

@[expose] public section


noncomputable section

open MeasureTheory

namespace NavierStokes.RadialSchedule

/-- Axial exponent, given by `1 / 2 - h`. -/
def axialExponent (h : ℝ) : ℝ := 1 / 2 - h

/-- Axial shape, given by `1 - η ^ 2`. -/
def axialShape (η : ℝ) : ℝ := 1 - η ^ 2

/-- Coordinate factor, given by `1 - 2 * h * η ^ 2`. -/
def coordinateFactor (h η : ℝ) : ℝ := 1 - 2 * h * η ^ 2

/-- Ideal axial velocity, given by `4 * η`. -/
def idealAxialVelocity (η : ℝ) : ℝ := 4 * η

/-- Ideal transport, given by `1 - 2 * axialExponent h * η * idealAxialVelocity η - axialShape η
* 4`. -/
def idealTransport (h η : ℝ) : ℝ :=
  1 - 2 * axialExponent h * η * idealAxialVelocity η - axialShape η * 4

/-- The logarithmic shape derivative of `(1 + η²)⁻¹`. -/
def logShapeDerivative (η : ℝ) : ℝ := -(2 * η / (1 + η ^ 2))

theorem log_shape_hasDerivAt (η : ℝ) :
    HasDerivAt (fun x : ℝ => -Real.log (1 + x ^ 2)) (logShapeDerivative η) η := by
  have hp : 1 + η ^ 2 ≠ 0 := by positivity
  have hd := (((hasDerivAt_id η).pow 2).const_add 1).log hp
  convert! hd.neg using 1
  simp [logShapeDerivative]

/-- Ideal source as an element of `ℝ`. -/
def idealSource (h η : ℝ) : ℝ :=
  -(3 / 5) * idealTransport h η - h * (1 - 2 * η * idealAxialVelocity η) -
    (axialExponent h * η + axialShape η * idealAxialVelocity η) *
      logShapeDerivative η

/-- The constant particular solution with `l = 3/5`. -/
def idealLag (h η : ℝ) : ℝ := idealSource h η / (8 / 5)

theorem ideal_transport_eq (h η : ℝ) :
    idealTransport h η = 1 - 4 * coordinateFactor h η := by
  unfold idealTransport axialExponent axialShape idealAxialVelocity coordinateFactor
  ring

theorem ideal_source_displayed (h η : ℝ) :
    idealSource h η =
      (3 / 5) * (4 * coordinateFactor h η - 1) - h * (1 - 8 * η ^ 2) +
        (axialExponent h + 4 * axialShape η) * η * (2 * η / (1 + η ^ 2)) := by
  unfold idealSource logShapeDerivative idealAxialVelocity
  rw [ideal_transport_eq]
  ring

theorem ideal_source_positive_decomposition (h η : ℝ) :
    idealSource h η = 9 / 5 - h + (16 / 5) * h * η ^ 2 +
      2 * (axialExponent h + 4 * axialShape η) * η ^ 2 / (1 + η ^ 2) := by
  rw [ideal_source_displayed]
  unfold coordinateFactor
  ring

/-- A quantitative version of the ideal-prefix positivity in Section 4.4. -/
theorem ideal_lag_ge_one {h η : ℝ}
    (hh : 0 ≤ h) (hsmall : h ≤ 1 / 5) (hη : η ^ 2 ≤ 1) :
    1 ≤ idealLag h η := by
  have hD : 0 ≤ axialExponent h := by unfold axialExponent; linarith
  have hd : 0 ≤ axialShape η := by unfold axialShape; linarith
  have hquad : 0 ≤ (16 / 5 : ℝ) * h * η ^ 2 := by positivity
  have hshape : 0 ≤ 2 * (axialExponent h + 4 * axialShape η) * η ^ 2 /
      (1 + η ^ 2) := by positivity
  unfold idealLag
  rw [ideal_source_positive_decomposition]
  linarith

/-- The profile equation is satisfied by the constant particular solution. -/
theorem ideal_lag_equation (h η : ℝ) :
    (1 + (3 / 5 : ℝ)) * idealLag h η = idealSource h η := by
  unfold idealLag
  ring

/-- Radius profile, given by `X₀ * Real.exp y`. -/
def radiusProfile (X₀ y : ℝ) : ℝ := X₀ * Real.exp y

/-- Angular velocity profile, given by `e₀ * Real.exp (-(1 / 2 + lam) * y)`. -/
def angularVelocityProfile (e₀ lam y : ℝ) : ℝ :=
  e₀ * Real.exp (-(1 / 2 + lam) * y)

/-- Angular momentum profile, given by `H₀ * Real.exp (-lam * y)`. -/
def angularMomentumProfile (H₀ lam y : ℝ) : ℝ :=
  H₀ * Real.exp (-lam * y)

/-- Weight of `R` in `dM/dy = X E R`. -/
theorem first_axial_moment_weight (X₀ e₀ lam y : ℝ) :
    radiusProfile X₀ y * angularVelocityProfile e₀ lam y =
      (X₀ * e₀) * Real.exp ((1 / 2 - lam) * y) := by
  unfold radiusProfile angularVelocityProfile
  calc
    _ = (X₀ * e₀) * Real.exp (y + -(1 / 2 + lam) * y) := by
      rw [Real.exp_add]
      ring
    _ = _ := by congr 2; ring

/-- Weight of `R` in `dJ/dy = X E H R`. -/
theorem second_axial_moment_weight (X₀ e₀ H₀ lam y : ℝ) :
    radiusProfile X₀ y * angularVelocityProfile e₀ lam y *
        angularMomentumProfile H₀ lam y =
      (X₀ * e₀ * H₀) * Real.exp ((1 / 2 - 2 * lam) * y) := by
  rw [first_axial_moment_weight]
  unfold angularMomentumProfile
  calc
    _ = (X₀ * e₀ * H₀) * Real.exp ((1 / 2 - lam) * y + -lam * y) := by
      rw [Real.exp_add]
      ring
    _ = _ := by congr 2; ring

/-- The common energy weight used to rescale the pulse in equation (13). -/
theorem energy_moment_weight (X₀ e₀ lam y : ℝ) :
    radiusProfile X₀ y * angularVelocityProfile e₀ lam y ^ 2 =
      (X₀ * e₀ ^ 2) * Real.exp (-2 * lam * y) := by
  unfold radiusProfile angularVelocityProfile
  calc
    _ = (X₀ * e₀ ^ 2) *
        Real.exp (y + (-(1 / 2 + lam) * y + -(1 / 2 + lam) * y)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = _ := by congr 2; ring

/-- The two axial slopes differ whenever `lam > 0`, as do their translated weights. -/
theorem axial_weight_gap_neg {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    Real.exp ((1 / 2 - 2 * lam) * δ) -
      Real.exp ((1 / 2 - lam) * δ) < 0 := by
  have hgap : (1 / 2 - 2 * lam) * δ < (1 / 2 - lam) * δ := by
    nlinarith [mul_pos hlam hδ]
  exact sub_neg.mpr (Real.exp_lt_exp.mpr hgap)

/-- Determinant of the moment matrix for two equal bumps separated by `δ`. -/
theorem axial_moment_determinant_neg {lam δ c₁ c₂ : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    c₁ * (c₂ * Real.exp ((1 / 2 - 2 * lam) * δ)) -
      (c₁ * Real.exp ((1 / 2 - lam) * δ)) * c₂ < 0 := by
  have h := mul_neg_of_pos_of_neg (mul_pos hc₁ hc₂) (axial_weight_gap_neg hlam hδ)
  nlinarith

/-- Explicit algebraic reset for arbitrary debts in the two normalized moment rows.
The theorem does not assert bounds on these coefficients or construct smooth bumps. -/
theorem two_moment_reset {r₁ r₂ : ℝ} (hgap : r₂ ≠ r₁) (debt₁ debt₂ : ℝ) :
    let b := (debt₁ - debt₂) / (r₂ - r₁)
    let a := -debt₁ - r₁ * b
    debt₁ + a + r₁ * b = 0 ∧ debt₂ + a + r₂ * b = 0 := by
  dsimp
  constructor
  · ring
  · field_simp [sub_ne_zero.mpr hgap]
    ring

/-- The exact negative part of the scaled pulse energy in equation (13). -/
theorem pulse_negative_energy_integral :
    (∫ z in (0 : ℝ)..13, (1 / 2 : ℝ) * Real.exp (-2 * z)) =
      (1 - Real.exp (-26)) / 4 := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (-2 : ℝ) ≠ 0),
    integral_exp]
  norm_num
  ring

/-- Pulse energy debt, given by `(1 - Real.exp (-26)) / 4`. -/
def pulseEnergyDebt : ℝ := (1 - Real.exp (-26)) / 4

theorem pulse_energy_debt_bounds :
    (6 / 25 : ℝ) ≤ pulseEnergyDebt ∧ pulseEnergyDebt ≤ 1 / 4 := by
  have hexp : (27 : ℝ) ≤ Real.exp 26 := by
    linarith [Real.add_one_le_exp (26 : ℝ)]
  have hinv : Real.exp (-26) ≤ 1 / 27 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 27) hexp
  have hpos := (Real.exp_pos (-26 : ℝ)).le
  unfold pulseEnergyDebt
  constructor <;> linarith

/-- Equation (13) has opposite endpoint signs if its error is at most `1/100`.
The asymptotic estimate needed to establish that bound is not formalized here. -/
theorem pulse_amplitude_endpoint_signs {K error₀ error₁ : ℝ}
    (hKlo : 1 / 5 ≤ K) (hKhi : K ≤ 1 / 4)
    (herror₀ : |error₀| ≤ 1 / 100) (herror₁ : |error₁| ≤ 1 / 100) :
    K * (9 / 10 : ℝ) ^ 2 - pulseEnergyDebt + error₀ < 0 ∧
      0 < K * (6 / 5 : ℝ) ^ 2 - pulseEnergyDebt + error₁ := by
  rcases pulse_energy_debt_bounds with ⟨hlo, hhi⟩
  rcases abs_le.mp herror₀ with ⟨he₀lo, he₀hi⟩
  rcases abs_le.mp herror₁ with ⟨he₁lo, he₁hi⟩
  constructor <;> nlinarith

/-- A continuous error bounded by `1/100` gives an amplitude in the manuscript's
bracket. No monotonicity, uniqueness, smooth dependence, or asymptotic error
estimate is inferred from this theorem. -/
theorem pulse_amplitude_root {K : ℝ} (error : ℝ → ℝ)
    (hKlo : 1 / 5 ≤ K) (hKhi : K ≤ 1 / 4)
    (hcontinuous : ContinuousOn error (Set.Icc (9 / 10 : ℝ) (6 / 5)))
    (herror : ∀ A ∈ Set.Icc (9 / 10 : ℝ) (6 / 5), |error A| ≤ 1 / 100) :
    ∃ A ∈ Set.Icc (9 / 10 : ℝ) (6 / 5),
      K * A ^ 2 - pulseEnergyDebt + error A = 0 := by
  let F : ℝ → ℝ := fun A => K * A ^ 2 - pulseEnergyDebt + error A
  have hF : ContinuousOn F (Set.Icc (9 / 10 : ℝ) (6 / 5)) := by
    apply ContinuousOn.add _ hcontinuous
    exact ((continuous_const.mul (continuous_id.pow 2)).sub continuous_const).continuousOn
  have hlo := herror (9 / 10) (by constructor <;> norm_num)
  have hhi := herror (6 / 5) (by constructor <;> norm_num)
  have hsign := pulse_amplitude_endpoint_signs hKlo hKhi hlo hhi
  have hzero : 0 ∈ F '' Set.Icc (9 / 10 : ℝ) (6 / 5) :=
    intermediate_value_Icc (by norm_num) hF ⟨hsign.1.le, hsign.2.le⟩
  exact hzero

/-- Constant-source lag solution, written in a form that also specifies its initial value. -/
def lagSolution (a c q₀ y : ℝ) : ℝ :=
  c / a + (q₀ - c / a) * Real.exp (-a * y)

theorem lag_solution_initial (a c q₀ : ℝ) : lagSolution a c q₀ 0 = q₀ := by
  simp [lagSolution]

theorem lag_solution_hasDerivAt (a c q₀ y : ℝ) :
    HasDerivAt (lagSolution a c q₀)
      (-(a * (q₀ - c / a) * Real.exp (-a * y))) y := by
  have he := ((hasDerivAt_id y).const_mul (-a)).exp
  convert! (he.const_mul (q₀ - c / a)).const_add (c / a) using 1
  simp only [mul_one, id_eq]
  ring

theorem lag_solution_equation {a : ℝ} (ha : a ≠ 0) (c q₀ y : ℝ) :
    deriv (lagSolution a c q₀) y + a * lagSolution a c q₀ y = c := by
  rw [(lag_solution_hasDerivAt a c q₀ y).deriv]
  unfold lagSolution
  field_simp [ha]; ring

/-- The release initial lag follows algebraically from the angular moment reset. -/
theorem release_initial_lag {lam : ℝ} (hlam : lam ≠ 1) (h : ℝ) :
    -1 + (1 - h) / (1 - lam) = (lam - h) / (1 - lam) := by
  field_simp [sub_ne_zero.mpr (Ne.symm hlam)]; ring

theorem release_initial_lag_positive {lam h : ℝ} (hhlam : h < lam) (hlam : lam < 1) :
    0 < (lam - h) / (1 - lam) :=
  div_pos (sub_pos.mpr hhlam) (sub_pos.mpr hlam)

end NavierStokes.RadialSchedule
