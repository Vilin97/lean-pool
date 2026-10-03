/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.CoefficientAnalysis
public import Mathlib.Tactic.FieldSimp

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The explicit form of the iterated Fermat quotients

The divided-difference recursion defining `iteratedFermatQuot` is unrolled once and for all:
`F^{(j)}_k(x)` is a single fraction whose numerator is the signed combination of the powers
`x^{p^{k+i}}` weighted by the coefficients `c_{j,i}(p)` of the falling `p`-power product, and
whose denominator is `p^{jk + C(j+1,2)}`.

## Main results

* `GranvilleMoore.iteratedFermatQuot_eq_sum_div`: the explicit form
  `F^{(j)}_k(x) = (∑_{i ≤ j} (-1)^{j-i} c_{j,i}(p) x^{p^{k+i}}) / p^{jk + C(j+1,2)}`.

## Implementation notes

The induction is on `j` uniformly in `k`, since the divided difference needs the formula at
both `k` and `k+1`; `generalizing k` supplies the quantified inductive hypothesis.

The combinatorial half of the step — that the numerator at level `j+1` is the numerator at
level `j` shifted in `k` minus `p^j` times the unshifted one — is isolated in
`numerator_recursion`, so that the main proof is only the bookkeeping of a common
denominator. That isolation matters: the shift is an index reindexing whose boundary term at
`i = 0` is supplied by `cCoeff_succ_zero`, while the interior is `cCoeff_succ`, and mixing
that with the division would make one indivisible mess.

The exponent identity behind the common denominator is
`(j+1)(k+1) + C(j+1,2) = (j+1)k + C(j+2,2)`, which is `C(j+2,2) = C(j+1,2) + (j+1)`; it is
proved from `Nat.choose_succ_succ` rather than `Nat.choose_two_right`, whose division by two
is gratuitous here.
-/

public section

open Finset

namespace GranvilleMoore

/-! ### The constant coefficient of the falling `p`-power product -/

/-- The constant term of `∏_{r<j+1}(X + p^r)`: the new factor contributes its constant `p^j`.

This is the `i = 0` boundary case of `cCoeff_succ`, which cannot state it because the index
`c_{j,i-1}` is meaningless there. -/
private theorem cCoeff_succ_zero (p j : ℕ) :
    cCoeff p (j + 1) 0 = (p : ℤ) ^ j * cCoeff p j 0 := by
  simp only [cCoeff, cPoly_succ, Polynomial.mul_coeff_zero, Polynomial.coeff_add,
    Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_add]
  ring

/-! ### The numerator recursion -/

/-- Reindexing the signed sum by `i ↦ i + 1`: shifting the coefficient index up by one and
the exponent index up by one flips the overall sign, up to the boundary term at `i = 0`
which is left behind.

The coefficient `c_{j,j+1}` at the top of the shifted range vanishes by
`cCoeff_eq_zero_of_lt`, which is what makes the two ranges match. -/
private theorem shifted_cCoeff_sum (p : ℕ) (x : ℤ) (j k : ℕ) :
    ∑ i ∈ range (j + 1),
        (-1 : ℚ) ^ (j - i) * (cCoeff p j (i + 1) : ℚ) * (x : ℚ) ^ p ^ (k + 1 + i)
      = -∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * (x : ℚ) ^ p ^ (k + i)
        + (-1 : ℚ) ^ j * (cCoeff p j 0 : ℚ) * (x : ℚ) ^ p ^ k := by
  rw [Finset.sum_range_succ, cCoeff_eq_zero_of_lt (p := p) (j := j) (i := j + 1) (by omega),
    Finset.sum_range_succ'
      (fun i => (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * (x : ℚ) ^ p ^ (k + i)) j]
  have hterm : ∀ i ∈ range j,
      (-1 : ℚ) ^ (j - i) * (cCoeff p j (i + 1) : ℚ) * (x : ℚ) ^ p ^ (k + 1 + i)
        = -((-1 : ℚ) ^ (j - (i + 1)) * (cCoeff p j (i + 1) : ℚ) * (x : ℚ) ^ p ^ (k + (i + 1))) := by
    intro i hi
    have hij : i < j := mem_range.mp hi
    have h1 : j - i = j - (i + 1) + 1 := by omega
    have h2 : k + 1 + i = k + (i + 1) := by omega
    rw [h1, h2, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  simp only [Nat.sub_zero, Int.cast_zero, mul_zero, zero_mul, add_zero]
  ring

/-- **The numerator recursion.** Writing `N_j(k)` for the signed sum
`∑_{i ≤ j} (-1)^{j-i} c_{j,i}(p) x^{p^{k+i}}`, the level-`j+1` numerator is
`N_{j+1}(k) = N_j(k+1) - p^j N_j(k)`.

This is the whole combinatorial content of `iteratedFermatQuot_eq_sum_div`: the interior
coefficients combine by `cCoeff_succ` and the boundary one by `cCoeff_succ_zero`. -/
private theorem numerator_recursion (p : ℕ) (x : ℤ) (j k : ℕ) :
    (∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * (x : ℚ) ^ p ^ (k + 1 + i))
        - (p : ℚ) ^ j *
          ∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * (x : ℚ) ^ p ^ (k + i)
      = ∑ i ∈ range (j + 1 + 1),
          (-1 : ℚ) ^ (j + 1 - i) * (cCoeff p (j + 1) i : ℚ) * (x : ℚ) ^ p ^ (k + i) := by
  rw [Finset.sum_range_succ'
    (fun i => (-1 : ℚ) ^ (j + 1 - i) * (cCoeff p (j + 1) i : ℚ) * (x : ℚ) ^ p ^ (k + i)) (j + 1)]
  have hstep : ∀ i ∈ range (j + 1),
      (-1 : ℚ) ^ (j + 1 - (i + 1)) * (cCoeff p (j + 1) (i + 1) : ℚ) * (x : ℚ) ^ p ^ (k + (i + 1))
        = (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * (x : ℚ) ^ p ^ (k + 1 + i)
          + (p : ℚ) ^ j *
            ((-1 : ℚ) ^ (j - i) * (cCoeff p j (i + 1) : ℚ) * (x : ℚ) ^ p ^ (k + 1 + i)) := by
    intro i _
    have h1 : j + 1 - (i + 1) = j - i := by omega
    have h2 : k + (i + 1) = k + 1 + i := by omega
    rw [h1, h2, cCoeff_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
    shifted_cCoeff_sum, cCoeff_succ_zero]
  simp only [Nat.sub_zero, Nat.add_zero]
  push_cast
  ring

/-! ### The explicit form -/

/-- **`prop_fermatexplicit`**: the explicit form of the iterated Fermat quotient,
```
F^{(j)}_k(x) = (1 / p^{jk + C(j+1,2)}) * ∑_{i=0}^{j} (-1)^{j-i} c_{j,i}(p) x^{p^{k+i}} .
```

Induction on `j`, uniformly in `k`. The base case is the empty product `c_{0,0}(p) = 1` over
the empty denominator; the step puts the two halves of the divided difference over the
common denominator `p^{(j+1)(k+1) + C(j+1,2)} = p^{(j+1)k + C(j+2,2)}` and appeals to
`numerator_recursion`. -/
theorem iteratedFermatQuot_eq_sum_div {p : ℕ} (hp : p ≠ 0) (j k : ℕ) (x : ℤ) :
    iteratedFermatQuot p j k x
      = (∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * (x : ℚ) ^ p ^ (k + i))
        / (p : ℚ) ^ (j * k + Nat.choose (j + 1) 2) := by
  have hne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  induction j generalizing k with
  | zero => simp [cCoeff]
  | succ j ih =>
    have hc : Nat.choose (j + 1 + 1) 2 = j + 1 + Nat.choose (j + 1) 2 := by
      rw [Nat.choose_succ_succ (j + 1) 1, Nat.choose_one_right]
    have e1 : (p : ℚ) ^ (j * (k + 1) + Nat.choose (j + 1) 2)
        = (p : ℚ) ^ (j * k + Nat.choose (j + 1) 2) * (p : ℚ) ^ j := by
      rw [← pow_add]
      congr 1
      ring
    have e2 : (p : ℚ) ^ ((j + 1) * k + Nat.choose (j + 1 + 1) 2)
        = (p : ℚ) ^ (j * k + Nat.choose (j + 1) 2) * (p : ℚ) ^ j * (p : ℚ) ^ (k + 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      rw [hc]
      ring
    have hQ : (p : ℚ) ^ (j * k + Nat.choose (j + 1) 2) ≠ 0 := pow_ne_zero _ hne
    rw [iteratedFermatQuot_succ, ih (k + 1), ih k, ← numerator_recursion, e1, e2]
    field_simp

end GranvilleMoore
