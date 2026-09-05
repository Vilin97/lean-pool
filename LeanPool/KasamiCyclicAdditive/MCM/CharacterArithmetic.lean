/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Arithmetic for the exceptional MCM character case

For coprime `k,n`, every common divisor of `2^k+1` and `2^n-1` divides `3`.
Thus a multiplicative character on `GF(2^n)` killed by `2^k+1` is automatically
cubic. This is the exceptional branch complementary to the generic Dickson
permutation argument.
-/

namespace KasamiCyclicAdditive

/-- If `gcd(k,n)=1`, then `gcd(2k,n)` divides `2`. -/
theorem gcd_two_mul_dvd_two {k n : ℕ} (hkn : Nat.Coprime k n) :
    Nat.gcd (2 * k) n ∣ 2 := by
  by_cases h2n : 2 ∣ n
  · have hg : Nat.gcd (k * 2) n = 2 :=
      Nat.gcd_mul_of_coprime_of_dvd hkn h2n
    rw [mul_comm] at hg
    rw [hg]
  · have h2cop : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr h2n
    have hprod : Nat.Coprime (2 * k) n :=
      Nat.coprime_mul_iff_left.mpr ⟨h2cop, hkn⟩
    rw [Nat.Coprime] at hprod
    rw [hprod]
    norm_num

/-- A common divisor of `2^k+1` and `2^n-1`, with `gcd(k,n)=1`, divides `3`. -/
theorem dvd_three_of_dvd_two_pow_add_one_two_pow_sub_one
    {d k n : ℕ} (hkn : Nat.Coprime k n)
    (hplus : d ∣ 2 ^ k + 1) (hminus : d ∣ 2 ^ n - 1) :
    d ∣ 3 := by
  have hsq : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by
    rw [pow_mul']
  have hplus' : (2 ^ k + 1) ∣ (2 ^ (2 * k) - 1) := by
    refine ⟨2 ^ k - 1, ?_⟩
    rw [hsq, ← Nat.sq_sub_sq (2 ^ k) 1]
  have hd2k : d ∣ 2 ^ (2 * k) - 1 := hplus.trans hplus'
  have hdg : d ∣ Nat.gcd (2 ^ (2 * k) - 1) (2 ^ n - 1) :=
    Nat.dvd_gcd hd2k hminus
  have hp := Nat.pow_sub_one_gcd_pow_sub_one 2 (2 * k) n
  rw [hp] at hdg
  have hgdiv : Nat.gcd (2 * k) n ∣ 2 := gcd_two_mul_dvd_two hkn
  rcases (Nat.dvd_prime Nat.prime_two).mp hgdiv with hg | hg
  · rw [hg] at hdg
    norm_num at hdg
    norm_num [hdg]
  · rw [hg] at hdg
    norm_num at hdg ⊢
    exact hdg

variable {K : Type*} [Field K] [Fintype K]

/-- On a field of order `2^n`, a character satisfying `χ^(2^k+1)=1` is cubic
whenever `gcd(k,n)=1`. -/
theorem mulChar_cube_eq_one_of_kasami_exceptional
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) (hkn : Nat.Coprime k n)
    (χ : MulChar K ℂ) (he : χ ^ (2 ^ k + 1) = 1) :
    χ ^ 3 = 1 := by
  have hplus : orderOf χ ∣ 2 ^ k + 1 := orderOf_dvd_of_pow_eq_one he
  have hminus : orderOf χ ∣ 2 ^ n - 1 := by
    have h := MulChar.orderOf_dvd_card_sub_one K χ
    rwa [hcard] at h
  have h3 : orderOf χ ∣ 3 :=
    dvd_three_of_dvd_two_pow_add_one_two_pow_sub_one hkn hplus hminus
  exact orderOf_dvd_iff_pow_eq_one.mp h3

end KasamiCyclicAdditive
