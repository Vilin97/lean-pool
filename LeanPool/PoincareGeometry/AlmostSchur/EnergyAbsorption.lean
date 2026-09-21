/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # Scalar absorption for coercive energy estimates -/

@[expose] public section
namespace AlmostSchur

/-- Completing a square absorbs a linear error in a coercive quadratic estimate. -/
theorem quadratic_energy_absorption {a X b c : ℝ} (ha : 0 < a)
    (h : a * X ^ 2 ≤ b * X + c) :
    a ^ 2 * X ^ 2 ≤ b ^ 2 + 2 * a * c := by
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * a by positivity)
  nlinarith [sq_nonneg (a * X - b)]

/-- The absorbed energy estimate supplies an explicit uniform norm bound. -/
theorem norm_bound_of_quadratic_energy {a X b c : ℝ} (ha : 0 < a)
    (h : a * X ^ 2 ≤ b * X + c) :
    X ≤ Real.sqrt (b ^ 2 + 2 * a * c) / a := by
  have hs := quadratic_energy_absorption ha h
  have hn : 0 ≤ b ^ 2 + 2 * a * c :=
    (mul_nonneg (sq_nonneg a) (sq_nonneg X)).trans hs
  have hroot := Real.sq_sqrt hn
  apply (le_div_iff₀ ha).mpr
  nlinarith [Real.sqrt_nonneg (b ^ 2 + 2 * a * c)]

end AlmostSchur
