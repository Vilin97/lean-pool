/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# Shared Frobenius and power-of-two arithmetic

Facts used by the Fermat-cubic, MCM and normalization layers alike.  This module
depends on nothing but Mathlib, and is kept separate from
`Statement/Definitions.lean` so that a file may depend on the arithmetic
without depending on the Kasami definitions, or
vice versa.

* `pow_two_pow_mul_self`, `pow_two_pow_gcd`, `pow_card_two_pow`: fixedness under
  iterated Frobenius and finite-field cardinality.
* `two_pow_mod_three`, `two_pow_mod_three_of_odd`, `two_pow_mod_nine`,
  `two_pow_two_mul_sub_one`: elementary arithmetic of `2 ^ k`.
-/

namespace KasamiCyclicAdditive

/-! ### Fixedness under iterated Frobenius -/

variable {K : Type*} [Field K]

/-- Iterating the `2^m`-power map: `x^(2^(m*q)) = x` whenever `x^(2^m) = x`. -/
theorem pow_two_pow_mul_self {x : K} {m : ℕ} (hm : x ^ 2 ^ m = x) :
    ∀ q : ℕ, x ^ 2 ^ (m * q) = x := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      have h : m * (q + 1) = m * q + m := by ring
      rw [h, pow_add, pow_mul, ih, hm]

/-- **Fixed field / Bézout step.**  If `x` is fixed by `π^a` and by `π^b`, then it is
fixed by `π^(gcd a b)`. -/
theorem pow_two_pow_gcd {x : K} {a b : ℕ} (ha : x ^ 2 ^ a = x) (hb : x ^ 2 ^ b = x) :
    x ^ 2 ^ Nat.gcd a b = x := by
  revert ha hb
  induction a, b using Nat.gcd.induction with
  | H0 b => intro _ hb; simpa using hb
  | H1 a b _ ih =>
      intro ha hb
      rw [Nat.gcd_rec]
      refine ih ?_ ha
      have hsplit : a * (b / a) + b % a = b := Nat.div_add_mod b a
      have h : x ^ 2 ^ (a * (b / a) + b % a) = x := by rw [hsplit]; exact hb
      rwa [pow_add, pow_mul, pow_two_pow_mul_self ha] at h

/-- On a finite field of order `2 ^ n`, `a ^ (2 ^ n) = a`. -/
theorem pow_card_two_pow [Fintype K] {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (a : K) : a ^ (2 ^ n) = a := by
  rw [← hcard]
  exact FiniteField.pow_card a

/-! ### Elementary arithmetic of `2 ^ k` -/

/-- `2` has multiplicative order dividing `2` modulo `3`. -/
theorem two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = 2 ^ (k % 2) % 3 := by
  conv_lhs => rw [← Nat.div_add_mod k 2]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- For odd `k`, `2 ^ k ≡ 2 (mod 3)`. -/
theorem two_pow_mod_three_of_odd {k : ℕ} (hk : Odd k) : 2 ^ k % 3 = 2 := by
  have h := two_pow_mod_three k
  rw [Nat.odd_iff.mp hk] at h
  simpa using h

/-- `2` has multiplicative order dividing `6` modulo `9`. -/
theorem two_pow_mod_nine (k : ℕ) : 2 ^ k % 9 = 2 ^ (k % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod k 6]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- `2 ^ (2k) - 1` factors as `(2 ^ k + 1) (2 ^ k - 1)`. -/
theorem two_pow_two_mul_sub_one (k : ℕ) :
    2 ^ (2 * k) - 1 = (2 ^ k + 1) * (2 ^ k - 1) := by
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  have h2 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  zify [h1, h2]
  ring

end KasamiCyclicAdditive
