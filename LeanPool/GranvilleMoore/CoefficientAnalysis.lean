/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.Defs.TheIteratedFermatQuotients
public import Mathlib.Tactic.LinearCombination

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The coefficient analysis

The combinatorial core of the elementary route to the congruences for the iterated Fermat
quotients. Nothing here mentions the Moore determinant: these are facts about the
coefficients of `cPoly` and about products of differences of powers of `p`.

## Main results

* `GranvilleMoore.cCoeff_succ`: the recursion `c_{j+1,i+1} = c_{j,i} + p^j c_{j,i+1}`.
* `GranvilleMoore.signedCCoeff_sum_eq_prod`: the signed coefficient identity
  `∑_{i ≤ j} (-1)^{j-i} c_{j,i} z^i = ∏_{r<j} (z - p^r)`.
* `GranvilleMoore.prod_pow_sub_pow_eq_zero`: that product vanishes when `n < j`.
* `GranvilleMoore.prod_pow_sub_pow_eq_pow_mul`: for `j ≤ n` it factors as
  `p^{∑_{r<j} r}` times a product of units.
* `GranvilleMoore.sum_range_choose_two`: the hockey stick `∑_{c ≤ d} C(c,2) = C(d+1,3)`.

## Implementation notes

The signed identity is stated *evaluated* at an integer `z` rather than as an identity of
polynomials. That is the only form the consumer needs — the collapsed coefficient is
`∑_i (-1)^{j-i} c_{j,i} (e_i choose m)` and the analysis evaluates it at `z = p^n` — and it
avoids composing `cPoly` with `-X` to get there.

`prod_pow_sub_pow_eq_pow_mul` leaves the exponent as `∑ r ∈ range j, r` rather than
`C(j,2)`; keeping the sum makes the proof one `Finset.prod_congr`. To convert, use
`Finset.sum_range_id` together with `Nat.choose_two_right` — there is no single Mathlib lemma
for it, and in particular no `Finset.sum_range_id_eq_choose_two`, which does not exist.
-/

public section

open Finset Polynomial

namespace GranvilleMoore

/-! ### The recursion for the coefficients -/

/-- **Recursion for the coefficients**: `c_{j+1,i+1} = c_{j,i} + p^j c_{j,i+1}`.

Stated at `i + 1` so that the paper's `c_{j,i-1}` is subtraction-free. -/
theorem cCoeff_succ (p j i : ℕ) :
    cCoeff p (j + 1) (i + 1) = cCoeff p j i + (p : ℤ) ^ j * cCoeff p j (i + 1) := by
  simp only [cCoeff, cPoly_succ]
  rw [mul_add, coeff_add, mul_comm (cPoly p j) X, coeff_X_mul, coeff_mul_C]
  ring

/-! ### The signed coefficient identity -/

/-- A sign bookkeeping step: for `i ≤ j`, `(-1)^{j-i} * (-1)^i = (-1)^j`. -/
private theorem neg_one_pow_sub_mul {j i : ℕ} (h : i ≤ j) :
    ((-1 : ℤ)) ^ (j - i) * (-1) ^ i = (-1) ^ j := by
  rw [← pow_add]
  congr 1
  omega

/-- **The signed coefficient identity**, evaluated:
`∑_{i ≤ j} (-1)^{j-i} c_{j,i}(p) z^i = ∏_{r<j} (z - p^r)`.

Substituting `-z` into the defining product of `cPoly` and pulling out `(-1)^j`. Evaluated
at `z = p^n` this is what turns the collapsed coefficient into a product of differences of
powers of `p`. -/
theorem signedCCoeff_sum_eq_prod (p j : ℕ) (z : ℤ) :
    ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i * z ^ i
      = ∏ r ∈ range j, (z - (p : ℤ) ^ r) := by
  have hsgn : ∏ r ∈ range j, (z - (p : ℤ) ^ r)
      = (-1) ^ j * ∏ r ∈ range j, ((-z) + (p : ℤ) ^ r) := by
    induction j with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
      ring
  have hev : ∏ r ∈ range j, ((-z) + (p : ℤ) ^ r) = (cPoly p j).eval (-z) := by
    simp [cPoly, eval_prod]
  rw [hsgn, hev, cPoly_eq_sum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hkey := neg_one_pow_sub_mul (j := j) (i := i) hij
  have hsq : ((-1 : ℤ)) ^ (i * 2) = 1 := by
    rw [mul_comm, pow_mul]
    norm_num
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [neg_pow]
  linear_combination (cCoeff p j i * z ^ i * (-1 : ℤ) ^ i) * hkey
    - (cCoeff p j i * z ^ i * (-1 : ℤ) ^ (j - i)) * hsq

/-! ### Products of differences of powers of `p` -/

/-- **The `p`-power difference product vanishes** for `n < j`: the factor at `r = n` is
`p^n - p^n = 0`. -/
theorem prod_pow_sub_pow_eq_zero {p n j : ℕ} (h : n < j) :
    ∏ r ∈ range j, ((p : ℤ) ^ n - (p : ℤ) ^ r) = 0 :=
  Finset.prod_eq_zero (mem_range.mpr h) (by ring)

/-- For `j ≤ n` the product factors as `p^{∑_{r<j} r}` times a product of terms
`p^{n-r} - 1`, each of which is `≡ -1` mod `p` and so a unit.

This is the paper's `∏_{r<j}(p^{m-r} - 1)` with its power of `p` made explicit; the
exponent `∑ r ∈ range j, r` equals `C(j,2)` by `Finset.sum_range_id` and
`Nat.choose_two_right`. -/
theorem prod_pow_sub_pow_eq_pow_mul {p n j : ℕ} (h : j ≤ n) :
    ∏ r ∈ range j, ((p : ℤ) ^ n - (p : ℤ) ^ r)
      = (p : ℤ) ^ (∑ r ∈ range j, r) * ∏ r ∈ range j, ((p : ℤ) ^ (n - r) - 1) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hrn : r ≤ n := le_trans (le_of_lt (mem_range.mp hr)) h
  rw [mul_sub, mul_one, ← pow_add]
  congr 2
  omega

/-! ### The ladder exponent -/

/-- **The ladder exponent**: `∑_{c ≤ d} C(c,2) = C(d+1,3)`, the hockey stick.

The `i`-th rung of the reduction ladder contributes `C(d-i,2)`; re-indexing by `c = d - i` turns
the ladder's total into this sum, which is how `GranvilleMoore.sum_range_sub_choose_two` — that
total in the ladder's own indexing — is proved. -/
theorem sum_range_choose_two (d : ℕ) :
    ∑ c ∈ range (d + 1), Nat.choose c 2 = Nat.choose (d + 1) 3 := by
  induction d with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (n + 1) 2]
    exact Nat.add_comm _ _

end GranvilleMoore
