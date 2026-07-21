/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Kummer's digit formula for central binomial coefficients

This module specializes Kummer's theorem to `Nat.centralBinom`, providing the
arithmetic bridge used by the odd-prime carry enumerator.
-/

namespace OddPrimeValuationDistribution

open Nat

/-- Kummer's digit-sum formula specialized to central binomial
coefficients. -/
theorem sub_one_mul_padicValNat_centralBinom
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (Nat.centralBinom n) =
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hn : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by decide)
  have hkummer :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits
      (p := p) (k := n) (n := 2 * n) hn
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hkummer
  rw [hkummer]
  ring_nf

end OddPrimeValuationDistribution
