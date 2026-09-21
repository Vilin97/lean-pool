/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunction
/-! # Herbrand values at natural lower indices -/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- At a natural lower index, the real piecewise Herbrand function equals
the rational finite-sum value after casting to reals. -/
theorem herbrandFunction_nat
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    ClassFieldTheory.herbrandFunction K A (n : ℝ) =
      (herbrandFunctionAtLowerIndex K A n : ℝ) := by
  unfold ClassFieldTheory.herbrandFunction
  rw [ite_eq_left (Nat.cast_nonneg n)]
  dsimp only
  rw [Nat.floor_natCast, sub_self, zero_mul, add_zero]

end ClassFieldTheory
