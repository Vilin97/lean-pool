/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.Arithmetic

/-!
# Elementary Frobenius-sum infrastructure

This module packages the elementary facts about the partial Frobenius sum
`T_k(s) = ∑ i < k, s^(2^i)` used by both the Fourier and permutation proofs.

The logical hierarchy is:

* `frobSum_succ` gives the recurrence used by `frobSum_sq_add_self`;
* if `frobSum k s = 0`, the Artin--Schreier identity gives `s^(2^k) = s`;
* the shared arithmetic lemmas `pow_card_two_pow` and `pow_two_pow_gcd` from
  `Preliminaries/Arithmetic.lean` then give `s^(2^gcd(k,n)) = s`;
* coprimality together with `s ≠ 0` forces `s = 1`, while oddness gives
  `frobSum k 1 = 1`, contradicting the assumed zero. The resulting
  `frobSum_ne_zero_of_odd` theorem is the public payoff.

```text
frobSum_succ
      |
      v
frobSum_sq_add_self
      |
      |  if frobSum k s = 0
      v
s^(2^k) = s -----------\
                         \
pow_card_two_pow --------> pow_two_pow_gcd
                           |
                           v
                 s^(2^gcd(k,n)) = s
                           |
                    gcd(k,n) = 1
                           |
                           v
                        s^2 = s
                           |
                    s ≠ 0 => s = 1
                           |
frobSum_one --------------+
                           |
                           v
                     contradiction
```
-/

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- `T_k(s)=s+s^2+...+s^(2^(k-1))`. -/
def frobSum (k : ℕ) (s : K) : K :=
  ∑ i ∈ Finset.range k, s ^ (2 ^ i)

omit [Fintype K] [DecidableEq K] [CharP K 2] in
/-- One further term of the Frobenius sum. -/
theorem frobSum_succ (k : ℕ) (s : K) :
    frobSum (k + 1) s = frobSum k s + s ^ (2 ^ k) := by
  simp [frobSum, Finset.sum_range_succ]

omit [Fintype K] [DecidableEq K] in
/-- For odd `k`, `frobSum k 1 = 1`. -/
theorem frobSum_one {k : ℕ} (hk : Odd k) : frobSum k (1 : K) = 1 := by
  simp only [frobSum, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  obtain ⟨m, rfl⟩ := hk
  push_cast
  rw [CharTwo.two_eq_zero]
  ring

omit [Fintype K] [DecidableEq K] in
/-- `frobSum k` satisfies the Artin--Schreier identity. -/
theorem frobSum_sq_add_self (k : ℕ) (s : K) :
    frobSum k s ^ 2 + frobSum k s = s ^ (2 ^ k) + s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  induction k with
  | zero => simp [frobSum]; linear_combination -s * h2
  | succ k ih =>
    rw [frobSum_succ]
    have h3 : (frobSum k s + s ^ (2 ^ k)) ^ 2 =
        frobSum k s ^ 2 + (s ^ (2 ^ k)) ^ 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact add_pow_char _ _ _
    rw [h3, ← pow_mul, pow_succ 2 k]
    linear_combination ih + s ^ (2 ^ k) * h2

omit [DecidableEq K] in
/-- Under the odd Kasami hypotheses, `frobSum k s` is nonzero for `s ≠ 0`. -/
theorem frobSum_ne_zero_of_odd
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) (hk : Odd k)
    (hkn : Nat.Coprime k n) {s : K} (hs : s ≠ 0) : frobSum k s ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hfix : s ^ (2 ^ k) = s := by
    have h' := frobSum_sq_add_self k s
    rw [h] at h'
    simp at h'
    linear_combination -h' - s * h2
  have hn : s ^ (2 ^ n) = s := pow_card_two_pow hcard s
  have hg : s ^ (2 ^ Nat.gcd k n) = s := pow_two_pow_gcd hfix hn
  rw [hkn] at hg
  have hs1 : s = 1 := by
    have hz : s * (s - 1) = 0 := by
      have hs2 : s ^ 2 = s := by simpa using hg
      linear_combination hs2
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd h' hs
    · exact sub_eq_zero.1 h'
  rw [hs1, frobSum_one hk] at h
  exact one_ne_zero h

end KasamiCyclicAdditive
