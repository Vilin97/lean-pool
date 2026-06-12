/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
Kummer bridge for the Concrete Mathematics GKP conjecture.

This file owns the central-binomial digit-excess lemmas used by the active
GKP attack. Earlier versions imported these lemmas from the retired
Erdos117 squarefree-central-binomial scaffold. Keeping them here makes the
ConcreteMath module self-contained around its actual open target.
-/

namespace Egrs75.ConcreteMath

open Nat

/-! ## Kummer digit-excess form for central binomial coefficients -/

/-- **General `p`-adic formula for central binomial coefficients.**

For any prime `p`,
`(p - 1) * ν_p(C(2n,n)) = 2 * S_p(n) - S_p(2n)`, where `S_p`
is the sum of base-`p` digits. This is Kummer's theorem specialized to
`Nat.centralBinom`. -/
theorem sub_one_mul_padicValNat_centralBinom (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (Nat.centralBinom n) =
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hk : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by decide)
  have hkummer :
      (p - 1) * padicValNat p ((2 * n).choose n) =
        (Nat.digits p n).sum + (Nat.digits p (2 * n - n)).sum -
          (Nat.digits p (2 * n)).sum :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) (k := n)
      (n := 2 * n) hk
  have h2n : 2 * n - n = n := by omega
  rw [h2n] at hkummer
  rw [hkummer]
  ring_nf

/-- **`p^m` divides `Nat.centralBinom n` from a Kummer digit bound.**

If `2 * S_p(n) - S_p(2n) ≥ (p - 1) * m`, then `p^m ∣ C(2n,n)`.
This is the reusable bridge from digit/carry certificates to
central-binomial divisibility. -/
theorem pow_dvd_centralBinom_of_digit_excess
    {p n m : ℕ} [hp : Fact p.Prime]
    (h : (p - 1) * m ≤
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum) :
    p ^ m ∣ Nat.centralBinom n := by
  have hform := sub_one_mul_padicValNat_centralBinom p n
  rw [← hform] at h
  have hp1 : 1 ≤ p - 1 := by
    have := hp.out.one_lt
    omega
  have hpos : 0 < p - 1 := hp1
  have hval : m ≤ padicValNat p (Nat.centralBinom n) :=
    Nat.le_of_mul_le_mul_left h hpos
  exact dvd_trans (pow_dvd_pow p hval) pow_padicValNat_dvd

/-- The ternary specialization of the central-binomial digit-excess formula. -/
theorem two_mul_padicValNat_three_centralBinom (n : ℕ) :
    2 * padicValNat 3 (Nat.centralBinom n) =
      2 * (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n)).sum := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have := sub_one_mul_padicValNat_centralBinom 3 n
  simpa using this

end Egrs75.ConcreteMath
