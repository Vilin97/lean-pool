/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
/-!
# From an integral discriminant bound to a root discriminant bound
-/

namespace AlgebraicNumberTheory.DiscriminantBounds

/-- A degree-power bound on the absolute discriminant gives a uniform
bound on the usual real root discriminant. -/
theorem rootDiscr_le_of_natAbs_discr_le_pow
    (F : Type*) [Field F] [NumberField F] (C : ℕ)
    (h : (NumberField.discr F).natAbs ≤ C ^ Module.finrank ℚ F) :
    NumberField.rootDiscr F ≤ (C : ℝ) := by
  have hn : Module.finrank ℚ F ≠ 0 := ne_of_gt Module.finrank_pos
  have hc : ((NumberField.discr F).natAbs : ℝ) ≤
      (C : ℝ) ^ Module.finrank ℚ F := by exact_mod_cast h
  have hd : |(NumberField.discr F : ℝ)| ≤
      (C : ℝ) ^ Module.finrank ℚ F := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  rw [NumberField.rootDiscr_def, Int.cast_abs]
  calc
    |(NumberField.discr F : ℝ)| ^ (Module.finrank ℚ F : ℝ)⁻¹ ≤
        ((C : ℝ) ^ Module.finrank ℚ F) ^ (Module.finrank ℚ F : ℝ)⁻¹ :=
      Real.rpow_le_rpow (abs_nonneg _) hd (by positivity)
    _ = (C : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hn

end AlgebraicNumberTheory.DiscriminantBounds
