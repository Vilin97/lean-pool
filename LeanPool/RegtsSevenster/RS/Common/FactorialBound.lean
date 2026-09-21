/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# `n ^ n ≤ 3 ^ n · n !`

The crude exponential comparison behind the Schur package's
square-dimension growth, proved over ℕ so that the package's
arithmetic stays integral.

The route is elementary: expand `(n + 1) ^ n` binomially, observe
that from the second term on each term is at most half the one
before it (the identity `C(n,k+1)·(k+1) = C(n,k)·(n−k)`), and sum a
halving sequence to at most twice its first term.  That gives
`(n + 1) ^ n ≤ 3 · n ^ n`, and induction turns it into the stated
bound.

The constant `3` is deliberate slack: this bound only has to beat
*some* exponential.  The sharp comparison `n ^ n ≤ e ^ n · n !`,
which the `⌊2eR⌋` threshold does need, is
`pow_le_exp_mul_factorial` in
`RS/Classical/SchurTheory/SquareGrowthSharp.lean`.
-/

namespace RS

open Finset Nat

/-! ## Geometric-sum bound

If a sequence halves at each step, the partial sum is at most twice the
first term. -/

/-- If `2 * f(i+1) ≤ f(i)` for all `i`, then
`∑ i in range (m+1), f i ≤ 2 * f 0`. -/
theorem sum_le_two_mul_first (m : ℕ) :
    ∀ (f : ℕ → ℕ), (∀ i, 2 * f (i + 1) ≤ f i) →
    ∑ i ∈ Finset.range (m + 1), f i ≤ 2 * f 0 := by
  induction m with
  | zero => intro f _; simp; omega
  | succ m ih =>
    intro f hf
    rw [Finset.sum_range_succ' f (m + 1)]
    have ih_shifted := ih (fun j => f (j + 1)) (fun i => hf (i + 1))
    change ∑ i ∈ Finset.range (m + 1), f (i + 1) ≤ 2 * f 1 at ih_shifted
    have h2 : 2 * f 1 ≤ f 0 := hf 0
    omega

/-! ## Ratio bound for binomial-expansion terms

Each successive term in the expansion of `(N+1)^N` is at most half the previous,
starting from the second term.  The proof pivots on the identity
`choose N (k+1) * (k+1) = choose N k * (N - k)`. -/

/-- For `k ≥ 1` and `k + 1 ≤ N`, consecutive binomial-expansion terms satisfy
`2 * (C(N,k+1) * N^(N-k-1)) ≤ C(N,k) * N^(N-k)`. -/
theorem binom_term_ratio (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    2 * (N.choose (k + 1) * N ^ (N - (k + 1))) ≤ N.choose k * N ^ (N - k) := by
  have h_pow : N - k = N - (k + 1) + 1 := by omega
  rw [h_pow, pow_succ]
  have h1 : 2 * N.choose (k + 1) ≤ N * N.choose k := by
    have h := Nat.choose_succ_right_eq N k
    calc 2 * N.choose (k + 1)
        ≤ (k + 1) * N.choose (k + 1) := by apply Nat.mul_le_mul_right; omega
      _ = N.choose k * (N - k) := by linarith
      _ ≤ N.choose k * N := Nat.mul_le_mul_left _ (Nat.sub_le N k)
      _ = N * N.choose k := Nat.mul_comm _ _
  calc 2 * (N.choose (k + 1) * N ^ (N - (k + 1)))
      = (2 * N.choose (k + 1)) * N ^ (N - (k + 1)) := by ring
    _ ≤ (N * N.choose k) * N ^ (N - (k + 1)) := Nat.mul_le_mul_right _ h1
    _ = N.choose k * (N ^ (N - (k + 1)) * N) := by ring

/-! ## Sub-lemma: `(n+1)^n ≤ 3 * n^n`

Expand `(n+1)^n` via the binomial theorem; the `m = 0` and `m = 1` terms each
contribute `n^n`, and the remaining terms form a geometrically decaying sum
bounded by `n^n`, for a total of at most `3 * n^n`. -/

/-- `(n + 1) ^ n ≤ 3 * n ^ n` for all natural numbers `n`. -/
theorem succ_pow_le_three_mul_pow (n : ℕ) : (n + 1) ^ n ≤ 3 * n ^ n := by
  rcases n with _ | n
  · simp
  set N := n + 1 with hN_def
  -- Binomial expansion: (1 + N)^N = ∑ m in range (N+1), N^(N-m) * C(N,m)
  have binom : (N + 1) ^ N =
      ∑ m ∈ range (N + 1), N ^ (N - m) * (N.choose m) := by
    have := add_pow (1 : ℕ) N N
    simp only [one_pow, one_mul, add_comm 1 N] at this
    exact this
  rw [binom]
  -- Peel off the m = 0 term (= N^N)
  rw [Finset.sum_range_succ' (fun m => N ^ (N - m) * N.choose m) N]
  simp only [Nat.sub_zero, choose_zero_right, Nat.mul_one]
  -- Goal: ∑ k in range N, N^(N-(k+1)) * C(N,k+1) + N^N ≤ 3 * N^N
  suffices h : ∑ k ∈ range N, N ^ (N - (k + 1)) * N.choose (k + 1) ≤ 2 * N ^ N
    by omega
  -- The terms halve: 2 * term(i+1) ≤ term(i)
  have hf_ratio : ∀ i, 2 * (N ^ (N - (i + 1 + 1)) * N.choose (i + 1 + 1)) ≤
      N ^ (N - (i + 1)) * N.choose (i + 1) := by
    intro i
    by_cases h : i + 2 ≤ N
    · have := binom_term_ratio N (i + 1) (by omega) h
      calc 2 * (N ^ (N - (i + 1 + 1)) * N.choose (i + 1 + 1))
          = 2 * (N.choose (i + 1 + 1) * N ^ (N - (i + 1 + 1))) := by ring
        _ ≤ N.choose (i + 1) * N ^ (N - (i + 1)) := this
        _ = N ^ (N - (i + 1)) * N.choose (i + 1) := by ring
    · have : N.choose (i + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [show i + 1 + 1 = i + 2 from by ring, this]
  -- Apply the geometric-sum bound
  have key := sum_le_two_mul_first n
    (fun i => N ^ (N - (i + 1)) * N.choose (i + 1)) hf_ratio
  -- The first term f(0) = N^(N-1) * C(N,1) = N^(N-1) * N = N^N
  have hf0 : N ^ (N - (0 + 1)) * N.choose (0 + 1) = N ^ N := by
    rw [Nat.choose_one_right, show N - (0 + 1) = n from by omega]
    exact (pow_succ _ _).symm
  rw [show n + 1 = N from rfl, hf0] at key
  exact key

/-! ## Main theorem -/

/-- `n ^ n ≤ 3 ^ n * n!` for all natural numbers `n`. -/
theorem three_pow_mul_factorial_ge (n : ℕ) : n ^ n ≤ 3 ^ n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.factorial_succ, pow_succ]
    -- Goal: (n+1)^n * (n+1) ≤ 3^n * 3 * ((n+1) * n!)
    calc (n + 1) ^ n * (n + 1)
        ≤ 3 * n ^ n * (n + 1) := Nat.mul_le_mul_right _
          (succ_pow_le_three_mul_pow n)
      _ = (n + 1) * (3 * n ^ n) := by ring
      _ ≤ (n + 1) * (3 * (3 ^ n * n !)) := by
          apply Nat.mul_le_mul_left; exact Nat.mul_le_mul_left _ ih
      _ = 3 ^ n * 3 * ((n + 1) * n !) := by ring

end RS
