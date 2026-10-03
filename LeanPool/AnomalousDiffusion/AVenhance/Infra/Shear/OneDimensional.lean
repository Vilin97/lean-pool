/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Explicit one-dimensional calculations for a sinusoidal shear.  The variable `x`
is the unit-period fast coordinate `x₁ / ε`; spatial derivatives below are
rescaled by `ε⁻¹`, so the formula keeps the source parameters `a`, `ε`, and `κ`.
-/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Shear

open Real
open intervalIntegral

/-- Stream function profile `a ε² sin (2π x)` in the unit-period fast variable. -/
def streamProfile (a ε x : ℝ) : ℝ := a * ε ^ 2 * Real.sin (2 * Real.pi * x)

/-- The physical shear speed `∂ₓ₁ ψ = 2π a ε cos (2π x₁ / ε)`. -/
def velocityProfile (a ε x : ℝ) : ℝ := 2 * Real.pi * a * ε * Real.cos (2 * Real.pi * x)

/-- The stationary corrector for the second coordinate, with the sign solving
`-κ Δχ + u₂ = 0`. -/
def stationaryCorrector (a ε κ x : ℝ) : ℝ :=
  -(a * ε ^ 3 / (2 * Real.pi * κ)) * Real.cos (2 * Real.pi * x)

/-- The spatial average over one period of the fast coordinate. -/
def cellAverage (f : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, f x

@[simp]
theorem streamProfile_add_one (a ε x : ℝ) :
    streamProfile a ε (x + 1) = streamProfile a ε x := by
  unfold streamProfile
  rw [show 2 * Real.pi * (x + 1) = (2 * Real.pi * x) + 2 * Real.pi by ring,
    Real.sin_add_two_pi]

@[simp]
theorem velocityProfile_add_one (a ε x : ℝ) :
    velocityProfile a ε (x + 1) = velocityProfile a ε x := by
  unfold velocityProfile
  rw [show 2 * Real.pi * (x + 1) = (2 * Real.pi * x) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

@[simp]
theorem stationaryCorrector_add_one (a ε κ x : ℝ) :
    stationaryCorrector a ε κ (x + 1) = stationaryCorrector a ε κ x := by
  unfold stationaryCorrector
  rw [show 2 * Real.pi * (x + 1) = (2 * Real.pi * x) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem average_sin_sq : cellAverage (fun x => Real.sin (2 * Real.pi * x) ^ 2) = 1 / 2 := by
  unfold cellAverage
  have hchange :
      (∫ x in (0 : ℝ)..1, Real.sin ((2 * Real.pi) * x) ^ 2 * (2 * Real.pi)) =
        ∫ y in (0 : ℝ)..(2 * Real.pi), Real.sin y ^ 2 := by
    simpa only [Function.comp_apply, mul_zero, mul_one] using
      (intervalIntegral.integral_comp_mul_deriv
        (f := fun x : ℝ => (2 * Real.pi) * x)
        (f' := fun _ : ℝ => 2 * Real.pi)
        (g := fun y : ℝ => Real.sin y ^ 2)
        (a := (0 : ℝ)) (b := 1)
        (by
          intro x hx
          simpa using (hasDerivAt_const_mul (2 * Real.pi)))
        (by fun_prop)
        (by fun_prop))
  have hperiod : (∫ y in (0 : ℝ)..(2 * Real.pi), Real.sin y ^ 2) = Real.pi := by
    rw [integral_sin_sq]
    simp
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have hchange' :
      (2 * Real.pi) * (∫ x in (0 : ℝ)..1, Real.sin ((2 * Real.pi) * x) ^ 2) = Real.pi := by
    calc
      (2 * Real.pi) * (∫ x in (0 : ℝ)..1, Real.sin ((2 * Real.pi) * x) ^ 2) =
          ∫ x in (0 : ℝ)..1, Real.sin ((2 * Real.pi) * x) ^ 2 * (2 * Real.pi) := by
            rw [integral_mul_const]
            ring
      _ = Real.pi := hchange.trans hperiod
  rw [show (fun x : ℝ => Real.sin (2 * Real.pi * x) ^ 2) =
      (fun x => Real.sin ((2 * Real.pi) * x) ^ 2) by rfl]
  apply (mul_left_cancel₀ hpi)
  calc
    (2 * Real.pi) * (∫ x in (0 : ℝ)..1, Real.sin ((2 * Real.pi) * x) ^ 2) =
        Real.pi := hchange'
    _ = (2 * Real.pi) * (1 / 2) := by ring

end AVenhance.Infra.Shear
