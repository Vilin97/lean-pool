/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Shared Trigonometric Identities

Euler-formula expansion of `exp(θ * I)` and exact values at `2π/3`,
used by both `WindingWeights/Common.lean` and `RectHomotopy/HomotopyDef.lean`.
-/

open Complex

theorem exp_real_angle_I (θ : ℝ) :
    Complex.exp (↑θ * I) = ↑(Real.cos θ) + ↑(Real.sin θ) * I := by
  rw [Complex.exp_mul_I]; simp [Complex.ofReal_cos, Complex.ofReal_sin]

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]; ring

theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.sin_pi_sub]; exact Real.sin_pi_div_three
