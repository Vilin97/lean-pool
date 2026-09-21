/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.ComputeDegree

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The iterated Fermat quotients

The objects of §3 of Granville's paper: the iterated Fermat quotients `F^{(j)}_k(x)`, the
coefficients `c_{j,i}(p)` of the falling `p`-power product, the unit quotient `g_k(x)`,
the rescaled binomial polynomial `B_m` with its coefficients `β_{m,n}`, and the collapsed
coefficient `A_j(m)`.

Everything here is a definition together with the API a consumer needs in order to use it
without unfolding it. None of the definitions needs `p` to be prime, so none of them
carries a primality hypothesis; the arithmetic lemmas that do are stated elsewhere.

All the divisions are taken in `ℚ`, so the definitions are total and unconditional; integrality is
a theorem about them (`GranvilleMoore.exists_intCast_iteratedFermatQuot` and
`GranvilleMoore.unitQuot_eq_intCast`), not part of their statement.

## Main definitions

* `GranvilleMoore.iteratedFermatQuot` — `F^{(j)}_k(x)`, the `j`-fold Fermat quotient.
* `GranvilleMoore.cPoly`, `GranvilleMoore.cCoeff` — `∏_{r<j}(X + p^r)` and its
  coefficients `c_{j,i}(p)`.
* `GranvilleMoore.unitQuot` — `g_k(x) = (t_x^{p^k} - 1)/p^{k+1}`, where `t_x = x^{p-1}`.
* `GranvilleMoore.binomPoly`, `GranvilleMoore.binomPolyCoeff` — `B_m` and `β_{m,n}`.
* `GranvilleMoore.collapsedCoeff` — `A_j(m)`.
-/

@[expose] public section

namespace GranvilleMoore

open Polynomial

/-! ### The iterated Fermat quotient -/

/-- The iterated Fermat quotient `F^{(j)}_k(x)` of Granville's paper: `F^{(0)}_k(x)` is
`x^(p^k)`, and `F^{(j+1)}_k(x)` is the divided difference
`(F^{(j)}_{k+1}(x) - F^{(j)}_k(x)) / p^(k+1)`.

The value is a rational number; that it is in fact an integer for prime `p` is
`GranvilleMoore.exists_intCast_iteratedFermatQuot`. The recursion is on `j`, uniformly in `k`. -/
def iteratedFermatQuot (p : ℕ) : ℕ → ℕ → ℤ → ℚ
  | 0, k, x => (x : ℚ) ^ p ^ k
  | j + 1, k, x =>
      (iteratedFermatQuot p j (k + 1) x - iteratedFermatQuot p j k x) / (p : ℚ) ^ (k + 1)

/-- The bottom of the tower: `F^{(0)}_k(x) = x^(p^k)`. -/
@[simp]
theorem iteratedFermatQuot_zero (p k : ℕ) (x : ℤ) :
    iteratedFermatQuot p 0 k x = (x : ℚ) ^ p ^ k := rfl

/-- The divided-difference recursion: `F^{(j+1)}_k(x)` is
`(F^{(j)}_{k+1}(x) - F^{(j)}_k(x)) / p^(k+1)`. -/
@[simp]
theorem iteratedFermatQuot_succ (p j k : ℕ) (x : ℤ) :
    iteratedFermatQuot p (j + 1) k x =
      (iteratedFermatQuot p j (k + 1) x - iteratedFermatQuot p j k x) / (p : ℚ) ^ (k + 1) :=
  rfl

/-! ### The coefficients of the falling `p`-power product -/

/-- The falling `p`-power product `∏_{r<j}(X + p^r)`, whose coefficients are the
`c_{j,i}(p)` of Granville's paper. The empty product for `j = 0` is `1`. -/
noncomputable def cPoly (p j : ℕ) : ℤ[X] := ∏ r ∈ Finset.range j, (X + C ((p : ℤ) ^ r))

/-- The coefficient `c_{j,i}(p)` of `X^i` in `∏_{r<j}(X + p^r)`. -/
noncomputable def cCoeff (p j i : ℕ) : ℤ := (cPoly p j).coeff i

/-- The empty falling `p`-power product is `1`. -/
@[simp] theorem cPoly_zero (p : ℕ) : cPoly p 0 = 1 := by simp [cPoly]

/-- The falling `p`-power product gains the factor `X + p^j` at step `j`. -/
theorem cPoly_succ (p j : ℕ) : cPoly p (j + 1) = cPoly p j * (X + C ((p : ℤ) ^ j)) := by
  simp [cPoly, Finset.prod_range_succ]

/-- The falling `p`-power product is monic, being a product of monic linear factors. -/
theorem monic_cPoly (p j : ℕ) : (cPoly p j).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/-- The falling `p`-power product `∏_{r<j}(X + p^r)` has degree `j`. -/
@[simp] theorem natDegree_cPoly (p j : ℕ) : (cPoly p j).natDegree = j := by
  rw [cPoly, natDegree_prod_of_monic _ _ fun r _ => monic_X_add_C ((p : ℤ) ^ r)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The coefficients `c_{j,i}(p)` vanish above the degree: `c_{j,i}(p) = 0` for `i > j`. -/
theorem cCoeff_eq_zero_of_lt {p j i : ℕ} (h : j < i) : cCoeff p j i = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_cPoly])

/-- The top coefficient of the falling `p`-power product is `1`: the product is monic of
degree `j`. -/
@[simp] theorem cCoeff_self (p j : ℕ) : cCoeff p j j = 1 := by
  have := (monic_cPoly p j).coeff_natDegree
  rwa [natDegree_cPoly] at this

/-- The defining identity of the coefficients `c_{j,i}(p)`, in the form
`∏_{r<j}(X + p^r) = ∑_{i ≤ j} c_{j,i}(p) X^i`. -/
theorem cPoly_eq_sum (p j : ℕ) :
    cPoly p j = ∑ i ∈ Finset.range (j + 1), C (cCoeff p j i) * X ^ i := by
  rw [(cPoly p j).as_sum_range' (j + 1) (by simp)]
  exact Finset.sum_congr rfl fun i _ => C_mul_X_pow_eq_monomial.symm

/-! ### The unit quotient -/

/-- The unit quotient `g_k(x) = (t_x^{p^k} - 1) / p^{k+1}` of Granville's paper, where
`t_x = x^{p-1}`; equivalently `(x^{(p-1)p^k} - 1)/p^{k+1}`.

The value is a rational number; that it is in fact an integer for an odd prime `p` not
dividing `x` is `GranvilleMoore.unitQuot_eq_intCast`. -/
def unitQuot (p : ℕ) (x : ℤ) (k : ℕ) : ℚ :=
  ((x ^ ((p - 1) * p ^ k) - 1 : ℤ) : ℚ) / (p : ℚ) ^ (k + 1)

/-- `g_k(x)` written with the unit `t_x = x^{p-1}` visible. -/
theorem unitQuot_eq (p : ℕ) (x : ℤ) (k : ℕ) :
    unitQuot p x k = (((x ^ (p - 1)) ^ p ^ k - 1 : ℤ) : ℚ) / (p : ℚ) ^ (k + 1) := by
  rw [unitQuot, pow_mul]

/-- The bottom unit quotient is the Fermat quotient: `g_0(x) = (x^{p-1} - 1)/p`. -/
@[simp] theorem unitQuot_zero (p : ℕ) (x : ℤ) :
    unitQuot p x 0 = ((x ^ (p - 1) - 1 : ℤ) : ℚ) / (p : ℚ) := by
  simp [unitQuot]

/-- The characterising property of `g_k(x)`: `t_x^{p^k} = 1 + p^{k+1} g_k(x)`, as an
identity in `ℚ`. This is the form consumers rewrite with, so that `unitQuot` never has to
be unfolded. -/
theorem pow_eq_one_add_pow_mul_unitQuot {p : ℕ} (hp : p ≠ 0) (x : ℤ) (k : ℕ) :
    ((x : ℚ) ^ (p - 1)) ^ p ^ k = 1 + (p : ℚ) ^ (k + 1) * unitQuot p x k := by
  have hp' : (p : ℚ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  rw [unitQuot, mul_div_cancel₀ _ hp']
  push_cast [pow_mul]
  ring

/-! ### The binomial polynomial and its coefficients -/

/-- The rescaled binomial polynomial `B_m(z) = (1/m!) ∏_{s<m} ((z-1)/(p-1) - s)` of
Granville's paper, the empty product for `m = 0` being `1`. It is built from
`descPochhammer ℚ m = ∏_{s<m}(X - s)` by substituting `(z-1)/(p-1)`; `eval_binomPoly`
recovers the product formula. -/
noncomputable def binomPoly (p m : ℕ) : ℚ[X] :=
  (m.factorial : ℚ)⁻¹ • (descPochhammer ℚ m).comp (((p : ℚ) - 1)⁻¹ • (X - 1))

/-- The coefficient `β_{m,n}` of `z^n` in `B_m`. It vanishes for `n > m`
(`binomPolyCoeff_eq_zero_of_lt`), so no bound on `n` is built into the definition. -/
noncomputable def binomPolyCoeff (p m n : ℕ) : ℚ := (binomPoly p m).coeff n

/-- The empty rescaled binomial polynomial is `1`. -/
@[simp] theorem binomPoly_zero (p : ℕ) : binomPoly p 0 = 1 := by simp [binomPoly]

/-- The product formula for `B_m`: `B_m(z) = (1/m!) ∏_{s<m} ((z-1)/(p-1) - s)`. -/
theorem eval_binomPoly (p m : ℕ) (z : ℚ) :
    (binomPoly p m).eval z =
      (m.factorial : ℚ)⁻¹ * ∏ s ∈ Finset.range m, ((z - 1) / ((p : ℚ) - 1) - s) := by
  simp only [binomPoly, eval_smul, eval_comp, eval_sub, eval_X, eval_one,
    descPochhammer_eval_eq_prod_range, smul_eq_mul, div_eq_inv_mul]

/-- The rescaled binomial polynomial `B_m` has degree at most `m`, being a rescaled
composition of a degree-`m` polynomial with a linear one. -/
theorem natDegree_binomPoly_le (p m : ℕ) : (binomPoly p m).natDegree ≤ m := by
  refine (natDegree_smul_le _ _).trans (natDegree_comp_le.trans ?_)
  rw [descPochhammer_natDegree]
  have h1 : (((p : ℚ) - 1)⁻¹ • (X - 1 : ℚ[X])).natDegree ≤ 1 :=
    (natDegree_smul_le _ _).trans (by compute_degree)
  simpa using Nat.mul_le_mul_left m h1

/-- The coefficients of `B_m` vanish above the degree: `β_{m,n} = 0` for `n > m`. -/
theorem binomPolyCoeff_eq_zero_of_lt {p m n : ℕ} (h : m < n) : binomPolyCoeff p m n = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_binomPoly_le p m).trans_lt h)

/-- `B_m` is the polynomial with coefficients `β_{m,n}` for `n ≤ m`. -/
theorem binomPoly_eq_sum (p m : ℕ) :
    binomPoly p m = ∑ n ∈ Finset.range (m + 1), C (binomPolyCoeff p m n) * X ^ n := by
  rw [(binomPoly p m).as_sum_range' (m + 1)
    ((natDegree_binomPoly_le p m).trans_lt (Nat.lt_succ_self m))]
  exact Finset.sum_congr rfl fun n _ => C_mul_X_pow_eq_monomial.symm

/-! ### The collapsed coefficient -/

/-- The collapsed coefficient `A_j(m) = ∑_{i ≤ j} (-1)^{j-i} c_{j,i}(p) * (e_i choose m)`
of Granville's paper, where `e_i = ∑_{r<i} p^r` is the Frobenius exponent
`GranvilleMoore.frobeniusExponent p i`, written out here and definitionally equal to it.

It is rational because it is compared with `p`-adic valuations and combined with rational
quantities in the master expansion `GranvilleMoore.iteratedFermatQuot_eq_mul_sum`, even
though the summands are integers. Its content is in `GranvilleMoore.collapsedCoeff_eq_sum`,
`GranvilleMoore.collapsedCoeff_eq_zero`, `GranvilleMoore.le_padicValRat_collapsedCoeff` and
`GranvilleMoore.collapsedCoeff_self_eq`. -/
noncomputable def collapsedCoeff (p j m : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (j + 1),
    (-1) ^ (j - i) * (cCoeff p j i : ℚ) * ((∑ r ∈ Finset.range i, p ^ r).choose m : ℚ)

/-- The collapsed coefficient at `j = 0` is the indicator of `m = 0`: `A_0(m)` is `1` for
`m = 0` and `0` otherwise. -/
@[simp] theorem collapsedCoeff_zero_left (p m : ℕ) :
    collapsedCoeff p 0 m = if m = 0 then 1 else 0 := by
  rcases m with _ | m <;> simp [collapsedCoeff]

end GranvilleMoore
