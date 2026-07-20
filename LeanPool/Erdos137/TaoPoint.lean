/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Finiteness
import LeanPool.Erdos137.JointFiniteness

/-!
# Erdős Problem #137: the elementary structure of a "very bad interval"

`Erdos137/Finiteness.lean` and `Erdos137/JointFiniteness.lean` formalize the conditional
finiteness of powerful products `F k n = n(n+1)⋯(n+k-1)` under radical lower bounds. This
file isolates the **elementary, deterministic** structural facts attached to a *very bad
interval* — Terence Tao's name (erdosproblems.com/137) for a block `[n, n+k-1]` whose product
`F k n` is powerful.

The point is entirely valuation-theoretic and uses no radical/abc input:

* Among `k` consecutive integers a prime `p ≥ k` divides **at most one** factor, because two
  factors differ by `< k ≤ p` (`prime_dvd_two_terms_eq`).
* Hence in a very bad block, all of `v_p(F k n)` comes from that single factor `n + i`, and
  powerfulness forces `v_p ≥ 2`, so `p ^ 2 ∣ n + i` (`veryBad_large_prime_sq`).
* In particular a prime `p` that *equals* one of the factors and *exceeds* the block length
  cannot occur in a very bad block: it would have to be a square, which a prime is not
  (`prime_term_gt_length_not_powerful`, `prime_in_block_not_powerful`).

The last statement is exactly the elementary mechanism that pairs with a Baker–Harman–Pintz
type input (a prime in every short interval `[n, n+k-1]`) to rule out very bad blocks: a single
prime that is itself a term of the block and is larger than the block length kills powerfulness.

Tao's analytic density theorem (very bad intervals have density `O(x^{2/5+o(1)})`) is **not**
formalized here; only the deterministic uniqueness/valuation facts above. The two-term linear
relation extraction that is Tao's next step is likewise not formalized.

## Main results (all unconditional — Mathlib's three axioms only)

* `prime_dvd_two_terms_eq` : a prime `p ≥ k` divides at most one of the `k` block factors.
* `veryBad_large_prime_sq` : in a very bad block, a prime `p ≥ k` dividing a factor squares it.
* `prime_term_gt_length_not_powerful` / `prime_in_block_not_powerful` : a prime that is a block
  factor and exceeds the block length prevents powerfulness.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-- A **very bad interval** (Tao, erdosproblems.com/137): the block `[n, n+k-1]` whose product
`F k n = ∏_{i<k}(n+i)` is *powerful*. For `k ≥ 2` this is exactly a powerful product of `≥ 2`
consecutive integers; the difference of two factors being `< k`, together with the resulting
coprimality of factors away from primes `< k`, is what feeds the Erdős #137 obstruction. -/
def VeryBad (k n : ℕ) : Prop := Powerful (F k n)

/-- **Prime uniqueness in a block.** If a prime `p` is at least the block length `k`, it divides
at most one of the `k` consecutive factors `n, n+1, …, n+k-1`: two distinct factors `n+i`, `n+j`
with `i, j < k` differ by `|i-j| < k ≤ p`, so a common prime divisor would divide a nonzero
number smaller than `p`, which is impossible. -/
theorem prime_dvd_two_terms_eq {p n k i j : ℕ} (_hp : p.Prime) (hk : k ≤ p)
    (hi : i < k) (hj : j < k) (hpi : p ∣ n + i) (hpj : p ∣ n + j) : i = j := by
  -- p divides the difference of the two factors, an integer of absolute value < k ≤ p.
  have hdvd : (p : ℤ) ∣ ((n : ℤ) + i) - ((n : ℤ) + j) := by
    exact dvd_sub (by exact_mod_cast hpi) (by exact_mod_cast hpj)
  have hsimp : ((n : ℤ) + i) - ((n : ℤ) + j) = (i : ℤ) - (j : ℤ) := by ring
  rw [hsimp] at hdvd
  -- |i - j| < k ≤ p, and p ∣ (i - j), forcing i - j = 0.
  have hlt : |(i : ℤ) - (j : ℤ)| < (p : ℤ) := by
    have hik : (i : ℤ) < (k : ℤ) := by exact_mod_cast hi
    have hjk : (j : ℤ) < (k : ℤ) := by exact_mod_cast hj
    have hkp : (k : ℤ) ≤ (p : ℤ) := by exact_mod_cast hk
    rw [abs_lt]; constructor <;> nlinarith [Int.natCast_nonneg i, Int.natCast_nonneg j]
  have hzero : (i : ℤ) - (j : ℤ) = 0 := by
    rcases eq_or_ne ((i : ℤ) - (j : ℤ)) 0 with h | h
    · exact h
    · exact absurd (Int.le_of_dvd (abs_pos.mpr h) ((dvd_abs _ _).mpr hdvd)) (by
        simp only [not_le]; exact hlt)
  have : (i : ℤ) = (j : ℤ) := by linarith
  exact_mod_cast this

/-- **Very bad block + large prime ⟹ the prime squares the unique factor it touches.**
If `F k n` is powerful, `p ≥ k` is prime, and `p ∣ n + i` for some `i < k`, then `p ^ 2 ∣ n + i`.

By `prime_dvd_two_terms_eq` the prime `p` divides *only* the factor `n + i` among the `k` block
factors, so `v_p(F k n) = ∑_{j<k} v_p(n+j) = v_p(n+i)`. Powerfulness gives `p ^ 2 ∣ F k n`, hence
`v_p(F k n) ≥ 2`, so `v_p(n+i) ≥ 2`, i.e. `p ^ 2 ∣ n + i`. -/
theorem veryBad_large_prime_sq {p n k i : ℕ} (hp : p.Prime) (hk : k ≤ p) (hi : i < k)
    (hn : 1 ≤ n) (hbad : VeryBad k n) (hpi : p ∣ n + i) : p ^ 2 ∣ (n + i) := by
  have hni : n + i ≠ 0 := by omega
  have hFne : F k n ≠ 0 := F_ne_zero hn
  -- v_p(F k n) = ∑_{j<k} v_p(n+j) (reuse the factorization-sum identity).
  have hfac : (F k n).factorization p = ∑ j ∈ Finset.range k, (n + j).factorization p := by
    unfold F
    rw [Nat.factorization_prod (by intro j _; omega)]
    rw [Finset.sum_apply']
  -- Every summand with j ≠ i vanishes: p ∤ (n+j) by uniqueness.
  have hsingle : (∑ j ∈ Finset.range k, (n + j).factorization p)
      = (n + i).factorization p := by
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      have hjk : j < k := Finset.mem_range.mp hj
      -- if p ∣ n+j then j = i (contradiction), so p ∤ n+j and v_p = 0.
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpj
      exact hji (prime_dvd_two_terms_eq hp hk hjk hi hpj hpi)
    · intro hcon; exact absurd (Finset.mem_range.mpr hi) hcon
  have hvF : (F k n).factorization p = (n + i).factorization p := by rw [hfac, hsingle]
  -- powerful + p ∣ F (via the i-th factor) ⟹ p² ∣ F ⟹ v_p(F) ≥ 2.
  have hpF : p ∣ F k n := by
    have hmem : i ∈ Finset.range k := Finset.mem_range.mpr hi
    have : (n + i) ∣ F k n := by unfold F; exact Finset.dvd_prod_of_mem _ hmem
    exact dvd_trans hpi this
  have hp2F : p ^ 2 ∣ F k n := hbad p hp hpF
  have hge2 : 2 ≤ (F k n).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hFne).mp hp2F
  -- transport to v_p(n+i) ≥ 2 and conclude.
  have hge2' : 2 ≤ (n + i).factorization p := by rw [hvF] at hge2; exact hge2
  exact (Nat.Prime.pow_dvd_iff_le_factorization hp hni).mpr hge2'

/-- **A prime factor exceeding the block length kills powerfulness.**
If `p` is prime, `p > k` (so `p ≥ k`), `i < k`, and the factor `n + i` *equals* `p`, then the
block `[n, n+k-1]` is not very bad: powerfulness would force `p ^ 2 ∣ n + i = p` by
`veryBad_large_prime_sq`, impossible for a prime `p ≥ 2`.

This is the elementary lemma that combines with a Baker–Harman–Pintz prime-in-short-interval
input: a prime `p > k` lying inside `[n, n+k-1]` cannot occur in a very bad interval. -/
theorem prime_term_gt_length_not_powerful {p n k i : ℕ} (hp : p.Prime) (hpk : k < p)
    (hi : i < k) (hn : 1 ≤ n) (hterm : n + i = p) : ¬ VeryBad k n := by
  intro hbad
  have hk : k ≤ p := le_of_lt hpk
  have hpi : p ∣ n + i := by rw [hterm]
  have hsq : p ^ 2 ∣ (n + i) := veryBad_large_prime_sq hp hk hi hn hbad hpi
  rw [hterm] at hsq
  -- p² ∣ p forces p ≤ 1, contradicting primality.
  have hple : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hsq
  nlinarith [hp.two_le]

/-- **Restatement.** If some factor of the block equals a prime `p` larger than the block
length `k`, then `F k n` is not powerful. (Directly: `prime_term_gt_length_not_powerful`
unfolding `VeryBad`.) -/
theorem prime_in_block_not_powerful {p n k : ℕ} (hp : p.Prime) (hpk : k < p) (hn : 1 ≤ n)
    (hmem : ∃ i < k, n + i = p) : ¬ Powerful (F k n) := by
  obtain ⟨i, hi, hterm⟩ := hmem
  exact prime_term_gt_length_not_powerful hp hpk hi hn hterm

end  -- noncomputable section

end Erdos137
