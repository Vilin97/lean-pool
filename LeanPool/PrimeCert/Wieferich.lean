/-
Copyright (c) 2026 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases
import LeanPool.PrimeCert.Interval
import LeanPool.PrimeCert.PowMod

/-! # Wieferich and Mirimanoff primes

A Wieferich prime satisfies `2^(p-1) ≡ 1 [MOD p²]`; a Mirimanoff prime satisfies
`3^(p-1) ≡ 1 [MOD p²]`. As of 2025, the only known Wieferich primes are 1093 and 3511;
the only known Mirimanoff primes are 11 and 1006003.

The main result `wieferich_mirimanoff` shows that no prime below 6000 is simultaneously
Wieferich and Mirimanoff. This is used in `miller_rabin_squarefree` to rule out
squarefree pseudoprimes below 36 million (to bases 2 and 3).
-/

/-- `p` is a Wieferich prime: `2 ^ (p - 1) ≡ 1 [MOD p²]`. -/
def Wieferich (p : ℕ) : Prop :=
  2 ^ (p - 1) ≡ 1 [MOD p^2]

/-- `p` is a Mirimanoff prime: `3 ^ (p - 1) ≡ 1 [MOD p²]`. -/
def Mirimanoff (p : ℕ) : Prop :=
  3 ^ (p - 1) ≡ 1 [MOD p^2]

/-- Kernel-reducible Boolean test for `p` being a Wieferich prime. -/
noncomputable def wieferichKR (p : ℕ) : Bool :=
  powModTR 2 p.pred (p.pow 2) |>.beq 1

/-- Kernel-reducible Boolean test for `p` being a Mirimanoff prime. -/
noncomputable def mirimanoffKR (p : ℕ) : Bool :=
  powModTR 3 p.pred (p.pow 2) |>.beq 1

@[simp] theorem wieferichKR_eq_true_iff (p : ℕ) (hp : p ≠ 1) : wieferichKR p ↔ Wieferich p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Wieferich, wieferichKR, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModTR_eq, powMod, Nat.pow_eq, Nat.pred_eq_sub_one]

@[simp] theorem wieferichKR_eq_false_iff (p : ℕ) (hp : p ≠ 1) :
    wieferichKR p = false ↔ ¬Wieferich p := by
  rw [← Bool.not_eq_true, wieferichKR_eq_true_iff p hp]

@[simp] theorem mirimanoffKR_eq_true_iff (p : ℕ) (hp : p ≠ 1) : mirimanoffKR p ↔ Mirimanoff p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Mirimanoff, mirimanoffKR, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModTR_eq, powMod, Nat.pow_eq, Nat.pred_eq_sub_one]

@[simp] theorem mirimanoffKR_eq_false_iff (p : ℕ) (hp : p ≠ 1) :
    mirimanoffKR p = false ↔ ¬Mirimanoff p := by
  rw [← Bool.not_eq_true, mirimanoffKR_eq_true_iff p hp]

/-! # We check odd numbers up to 6000 in the classes 1%6 and 5%6 -/


-- elab: 37 ms
-- kernel: 470 ms
-- 6n+1 to 6000
theorem wieferich_mirimanoff₁ : ∀ n < 6000, n % 6 = 1 →
    (wieferichKR n).not'.or' (mirimanoffKR n).not' := by
  checkInterval

-- elab: 57 ms
-- kernel: 561 ms
-- 6n+5 to 6000
theorem wieferich₅ : ∀ n < 6000, n % 6 = 5 → !wieferichKR n := by
  checkInterval

theorem Nat.Prime.mod_6 {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hp₃ : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h₁ := div_add_mod p 6
  have h₂ := mod_lt p (by decide +kernel : 0 < 6)
  generalize p / 6 = k at *
  generalize p % 6 = r at *
  subst p
  interval_cases r
  · rw [add_zero, prime_mul_iff, eq_false (p := Prime 6) (by decide)] at hp; simp at hp
  · left; lia
  · rw [show 6 * k + 2 = 2 * (3 * k + 1) by ring, prime_mul_iff] at hp
    rcases hp with ⟨-, h⟩ | ⟨-, h⟩ <;> lia
  · rw [show 6 * k + 3 = 3 * (2 * k + 1) by ring, prime_mul_iff] at hp
    rcases hp with ⟨-, h⟩ | ⟨-, h⟩ <;> lia
  · rw [show 6 * k + 4 = 2 * (3 * k + 2) by ring, prime_mul_iff] at hp
    rcases hp with ⟨-, h⟩ | ⟨-, h⟩ <;> lia
  · right; lia

theorem wieferich_mirimanoff {p : ℕ} (hp : p.Prime) (p_bound : p < 6000) :
    ¬(2 ^ (p - 1) ≡ 1 [MOD p^2]) ∨ ¬(3 ^ (p - 1) ≡ 1 [MOD p^2]) := by
  obtain hp₄ | hp₄ := lt_or_ge p 4
  · clear p_bound
    revert hp
    decide +revert +kernel
  have hp₁ : p ≠ 1 := hp.ne_one
  obtain h₁ | h₅ := hp.mod_6 (by lia) (by lia)
  · simpa [hp₁] using! wieferich_mirimanoff₁ p p_bound h₁
  · simpa [hp₁] using! Or.inl <| wieferich₅ p p_bound h₅

theorem _root_.pow_eq_one_of_dvd {M : Type*} [Monoid M] {x : M} {m n : ℕ}
    (h₁ : x ^ m = 1) (h₂ : m ∣ n) : x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := h₂
  rw [pow_mul, h₁, one_pow]

theorem miller_rabin_squarefree {n : ℕ} (hn₀ : n ≠ 0) (hn : n < 36000000)
    (h₂ : 2 ^ (n - 1) ≡ 1 [MOD n]) (h₃ : 3 ^ (n - 1) ≡ 1 [MOD n])
    {p : ℕ} (hp : p.Prime) (hpn : p ^ 2 ∣ n) : False := by
  have hn₁ : n ≠ 1 := by
    rintro rfl
    rw [Nat.dvd_one, sq, mul_eq_one, and_self] at hpn
    subst hpn
    exact absurd hp (by decide)
  have h₁ : _ < 6000 ^ 2 := (Nat.le_of_dvd (pos_of_ne_zero hn₀) hpn).trans_lt hn
  rw [Nat.pow_lt_pow_iff_left (by decide)] at h₁
  have hn₁' : n - 1 ≠ 0 := by lia
  have hp₁ : p ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
  have := NeZero.mk hp₁
  have h₅ : (n - 1).gcd p = 1 := by
    rw [Nat.gcd_sub_left_left_of_dvd _ (by lia)
      (dvd_trans (dvd_pow_self _ (by lia)) hpn), Nat.gcd_one_left]
  have h₄ (a) (ha : a ^ (n - 1) ≡ 1 [MOD n]) : a ^ (p - 1) ≡ 1 [MOD p^2] := by
    replace ha := ha.of_dvd hpn
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one] at ha ⊢
    let a' := Units.ofPowEqOne _ _ ha hn₁'
    have ha₁ : a' ^ (n - 1) = 1 := Units.pow_ofPowEqOne _ _
    have ha₂ := pow_card_eq_one (x := a')
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp, pow_one] at ha₂
    replace ha₂ := pow_gcd_eq_one.2 ⟨ha₁, ha₂⟩
    rw [Nat.gcd_mul_right_right_of_gcd_eq_one h₅] at ha₂
    replace ha₂ := pow_eq_one_of_dvd ha₂ (Nat.gcd_dvd_right _ _)
    simpa [a'] using congr(($ha₂ : ZMod (p ^ 2)))
  have := wieferich_mirimanoff hp h₁
  tauto
