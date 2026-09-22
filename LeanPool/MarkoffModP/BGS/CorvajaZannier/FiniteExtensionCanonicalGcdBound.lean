/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionOneSubGcdHeight
import LeanPool.MarkoffModP.BGS.CorvajaZannier.GlobalWronskianSummation
import Mathlib.Tactic

/-!
# A gcd bound from the canonical Wronskian inequality

Deduce the finite-extension gcd estimate from the residue-weighted canonical Wronskian bound.
-/

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The exact integer-valued canonical Wronskian inequality, together with
the one-minus divisor comparison, implies the numerical bound of Proposition
2 for the exhaustive gcd divisor. -/
theorem finiteExtensionGcdBound_of_canonicalWronskianInequality
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1)
    (h k : ℕ) (hn : 0 < h * k + h + k) (chi : ℕ)
    (hWronskian :
      Int.ofNat (h * k) *
          Int.ofNat (finiteExtensionPositiveDegree K L v) -
        Int.ofNat k *
          (Int.ofNat (finiteExtensionPositiveDegree K L v) +
            Int.ofNat (finiteExtensionPositiveDegree K L u)) -
        Int.ofNat ((h * k + h + k).choose 2) * Int.ofNat chi ≤
      Int.ofNat (h * k + h + k) *
        Int.ofNat (finiteExtensionOutsideHeight K L ((1 - u) / (1 - v))
          (propositionTwoExceptionalPlaces K L u v))) :
    (finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) : ℝ) ≤
      (((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ)) *
          (finiteExtensionPositiveDegree K L v : ℝ) +
      ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) *
          (finiteExtensionPositiveDegree K L u : ℝ) +
      (((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ)) := by
  let H : ℕ := finiteExtensionOutsideHeight K L ((1 - u) / (1 - v))
    (propositionTwoExceptionalPlaces K L u v)
  have hsum :=
    finiteExtensionOneSubGcd_add_outsideHeight_le_positiveDegree_coordinate
      K L u v hu hv huone hvone
  have hsumReal :
      (finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) : ℝ) +
          (H : ℝ) ≤ (finiteExtensionPositiveDegree K L v : ℝ) := by
    dsimp only [H]
    exact_mod_cast hsum
  have hGHeight :
      (finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) : ℝ) ≤
        (finiteExtensionPositiveDegree K L v : ℝ) - (H : ℝ) := by
    linarith
  have hWronskianCast :
      ((Int.ofNat (h * k) *
          Int.ofNat (finiteExtensionPositiveDegree K L v) -
        Int.ofNat k *
          (Int.ofNat (finiteExtensionPositiveDegree K L v) +
            Int.ofNat (finiteExtensionPositiveDegree K L u)) -
        Int.ofNat ((h * k + h + k).choose 2) * Int.ofNat chi : ℤ) : ℝ) ≤
      ((Int.ofNat (h * k + h + k) * Int.ofNat H : ℤ) : ℝ) :=
    Int.cast_le.mpr hWronskian
  push_cast at hWronskianCast
  have hWronskianReal :
      (((h * k : ℕ) : ℝ) *
          (finiteExtensionPositiveDegree K L v : ℝ) -
        (k : ℝ) *
          ((finiteExtensionPositiveDegree K L v : ℝ) +
            (finiteExtensionPositiveDegree K L u : ℝ)) -
        (((h * k + h + k).choose 2 : ℕ) : ℝ) * (chi : ℝ) ≤
      ((h * k + h + k : ℕ) : ℝ) * (H : ℝ)) := by
    simpa only [Int.ofNat_eq_natCast, Int.cast_mul, Int.cast_natCast,
      Nat.cast_mul] using hWronskianCast
  apply gcdBound_of_globalWronskianInequality
    (finiteExtensionPositiveDegree K L v : ℝ)
    (finiteExtensionPositiveDegree K L u : ℝ)
    (chi : ℝ)
    (finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) : ℝ)
    (H : ℝ) h k hn hGHeight
  simpa only [Nat.cast_choose_two] using hWronskianReal

end

end BGS.CorvajaZannier
