/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.PuncturedSmallOrderCount

/-!
# The elementary asymptotic in the giant-orbit assembly

The concrete small-order count is `2 * (2 + 2 * B^2)^2`.  This file proves that choosing
`B ≤ p^(ε/5)` makes that count at most `p^ε` for all sufficiently large `p`.  No dynamical
claim about the cage complement is used here.
-/

namespace BGS.Markoff

open Filter
open scoped Topology

/-- Once `p^(ε/5)` absorbs the fixed constant, the explicit polynomial bound is at most
`p^ε`. -/
theorem smallOrderPointBound_le_rpow
    {p bound : ℕ} {ε : ℝ}
    (hThirtyTwo : (32 : ℝ) ≤ (p : ℝ) ^ (ε / 5))
    (hbound : (bound : ℝ) ≤ (p : ℝ) ^ (ε / 5)) :
    ((2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) : ℝ) ≤ (p : ℝ) ^ ε := by
  let x : ℝ := (p : ℝ) ^ (ε / 5)
  have hxNonneg : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hxOne : 1 ≤ x := by
    dsimp [x]
    linarith [hThirtyTwo]
  have hboundNonneg : 0 ≤ (bound : ℝ) := Nat.cast_nonneg bound
  have hboundSq : (bound : ℝ) ^ 2 ≤ x ^ 2 := by
    exact pow_le_pow_left₀ hboundNonneg hbound 2
  have hxSqOne : 1 ≤ x ^ 2 := by nlinarith
  have hInside : 1 + (bound : ℝ) ^ 2 ≤ 2 * x ^ 2 := by linarith
  have hPolynomial :
      ((2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) : ℝ) ≤ 32 * x ^ 4 := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
    calc
      2 * (2 + 2 * (bound : ℝ) ^ 2) ^ 2 = 8 * (1 + (bound : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ 8 * (2 * x ^ 2) ^ 2 := by gcongr
      _ = 32 * x ^ 4 := by ring
  have hAbsorbConstant : 32 * x ^ 4 ≤ x ^ 5 := by
    nlinarith [sq_nonneg (x ^ 2), mul_nonneg hxNonneg (sq_nonneg x)]
  calc
    ((2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) : ℝ) ≤ 32 * x ^ 4 := hPolynomial
    _ ≤ x ^ 5 := hAbsorbConstant
    _ = (p : ℝ) ^ ε := by
      dsimp [x]
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p) (ε / 5) 5]
      congr 1
      ring

/-- The explicit polynomial small-order bound is eventually absorbed by the target real power. -/
theorem eventually_smallOrderPointBound_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, ∀ bound : ℕ,
      (bound : ℝ) ≤ (p : ℝ) ^ (ε / 5) →
        ((2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) : ℝ) ≤ (p : ℝ) ^ ε := by
  have hExponent : 0 < ε / 5 := div_pos hε (by norm_num)
  have hEventuallyThirtyTwo :
      ∀ᶠ p : ℕ in atTop, (32 : ℝ) ≤ (p : ℝ) ^ (ε / 5) :=
    ((tendsto_rpow_atTop hExponent).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 32)
  filter_upwards [hEventuallyThirtyTwo] with p hp
  exact fun bound hbound ↦ smallOrderPointBound_le_rpow hp hbound

/-- The counted punctured small-order set satisfies the target bound as soon as its order cutoff
is at most `p^(ε/5)` and the harmless constant has been absorbed. -/
theorem puncturedSmallOrderSet_card_le_rpow_of_bound
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) {ε : ℝ} (bound : ℕ)
    (hThirtyTwo : (32 : ℝ) ≤ (p : ℝ) ^ (ε / 5))
    (hbound : (bound : ℝ) ≤ (p : ℝ) ^ (ε / 5)) :
    ((puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card : ℝ) ≤
      (p : ℝ) ^ ε := by
  calc
    ((puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card : ℝ) ≤
        (2 * (2 + 2 * bound ^ 2) ^ 2 : ℕ) := by
      exact_mod_cast puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le hpTwo bound
    _ ≤ (p : ℝ) ^ ε := smallOrderPointBound_le_rpow hThirtyTwo hbound

end BGS.Markoff
