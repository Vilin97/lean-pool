/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.CarryArithmetic
import LeanPool.GKPCarry.FiniteRange

/-!
# Central-binomial consequence of the bounded C3 certificate

The bounded prefix computation supplies a secondary application of the general
Kummer carry theorem: divisibility by nine for a finite family of central
binomial coefficients indexed by powers of four.
-/

namespace GKPCarry

/-- The bounded C3 certificate implies divisibility by nine for
`Nat.centralBinom (4 ^ m)` throughout `27 ≤ m ≤ 6560`. -/
theorem nine_dvd_centralBinom_four_pow_in_finite_range
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    9 ∣ Nat.centralBinom (4 ^ m) := by
  apply nine_dvd_centralBinom_of_two_le_ternaryDoubleCarryCount
  exact le_trans
    (four_pow_prefix_carry_count_ge_two_in_finite_range hlower hupper)
    (prefixTernaryDoubleCarryCount_le
      (6 * ternaryLength m) (4 ^ m))

/-- Equivalent power-of-two form of the bounded central-binomial theorem. -/
theorem nine_dvd_centralBinom_two_pow_even_in_finite_range
    {m : ℕ} (hlower : 27 ≤ m) (hupper : m ≤ 6560) :
    9 ∣ Nat.centralBinom (2 ^ (2 * m)) := by
  have hpower : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  rw [← hpower]
  exact nine_dvd_centralBinom_four_pow_in_finite_range hlower hupper

end GKPCarry
