/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.Sensitivity.Defs
import LeanPool.Sensitivity.Basic
import LeanPool.Sensitivity.Multilinear
import LeanPool.Sensitivity.Main

/-!
# Consequences of the Sensitivity Theorem

A direct numerical corollary of `sensitivity_ge_sqrt_degree`: the
multilinear degree of any Boolean function is bounded above by the square
of its sensitivity.

## Main results

* `LeanPoolSensitivity.degree_le_sensitivity_sq` — `f.degree ≤ f.sensitivity^2`.
-/

namespace LeanPoolSensitivity

/-- The multilinear degree is at most the square of the sensitivity, an
immediate corollary of the sensitivity theorem `√d ≤ s(f)`: squaring both
sides yields `d ≤ s(f)^2`. -/
theorem degree_le_sensitivity_sq {n : ℕ} (f : BoolFun n) :
    f.degree ≤ f.sensitivity ^ 2 := by
  by_cases hd : f.degree = 0
  · simp [hd]
  · have hsqrt := sensitivity_ge_sqrt_degree f (by omega)
    have hsq : (f.degree : ℝ) ≤ (f.sensitivity : ℝ) ^ 2 := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) f.degree),
                 Real.sqrt_nonneg (↑f.degree : ℝ)]
    exact_mod_cast hsq

end LeanPoolSensitivity
