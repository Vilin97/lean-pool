/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.BinomPoly
public import LeanPool.GranvilleMoore.CoefficientAnalysis
public import Mathlib.Data.ZMod.Basic

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The collapsed coefficient

The four facts about `A_j(m)` that the master expansion needs. The definition
`GranvilleMoore.collapsedCoeff` is a sum over `i ≤ j` of signed `c`-coefficients against
binomial coefficients `C(e_i, m)`; expanding each `C(e_i, m)` as a polynomial in `p^i` and
exchanging the two sums replaces it by a sum over `n ≤ m` of `β_{m,n}` against a product of
differences of powers of `p`. Everything else here is read off that closed form.

## Main results

* `GranvilleMoore.collapsedCoeff_eq_sum`: `A_j(m) = ∑_{n ≤ m} β_{m,n} ∏_{r<j}(p^n - p^r)`.
* `GranvilleMoore.collapsedCoeff_eq_zero`: `A_j(m) = 0` for `m < j`.
* `GranvilleMoore.exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff` and
  `GranvilleMoore.le_padicValRat_collapsedCoeff`: `m! (p-1)^m A_j(m) / p^{C(j,2)}` is an
  integer, and hence `v_p(A_j(m)) ≥ C(j,2) - v_p(m!)`.
* `GranvilleMoore.collapsedCoeff_self_eq`,
  `GranvilleMoore.factorial_mul_pow_mul_collapsedCoeff_self` and
  `GranvilleMoore.exists_int_factorial_mul_pow_mul_collapsedCoeff_self`: the leading value
  `A_j(j) = β_{j,j} p^{C(j,2)} ∏_{s<j}(p^{s+1} - 1)`, its division-free form, and the
  resulting congruence `j! A_j(j) / p^{C(j,2)} ≡ 1 (mod p)`.

## Implementation notes

The coefficient analysis of `GranvilleMoore.CoefficientAnalysis` is stated over `ℤ`,
because that is where the `c_{j,i}(p)` live, while `collapsedCoeff` is rational. The three
private `*_rat` lemmas at the top of this file are those statements pushed through
`Int.cast`, and they are the only place a cast appears; `prod_pow_sub_pow_rat_eq_pow_mul`
also converts the exponent `∑_{r<j} r` into `C(j,2)`.

The valuation is usually stated as the inequality `v_p(A_j(m)) ≥ C(j,2) - v_p(m!)`, and that is
`le_padicValRat_collapsedCoeff`. It carries the side condition `A_j(m) ≠ 0`, which is not
avoidable: `padicValRat p 0 = 0` by convention, so the unconditional inequality would assert
`C(j,2) ≤ v_p(m!)` at every pair `(j, m)` where `A_j(m)` happens to vanish, and that is false
already for `j = m = 2` and `p` odd. The inequality is therefore derived from a sharper, purely
algebraic and unconditional form, `exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff`, which
says that

  `m! (p-1)^m A_j(m) / p^{C(j,2)}`

is an integer. That is the form a consumer wanting integrality should use — it holds for all
`j` and `m` with no nonvanishing hypothesis and no primality beyond `p ≠ 1` in spirit — and
the valuation bound follows from it because `p ∤ p - 1`. Neither statement needs `j ≤ m`:
for `j > m` the collapsed coefficient vanishes and both are trivially true.

For the leading coefficient the paper asserts the congruence `A_j(j)/p^{C(j,2)} ≡ 1/j! (mod p)` for
`j ≤ p - 1`. A congruence between rational numbers is not a Mathlib notion, so what is proved here
is the exact factorisation that the paper's proof actually establishes, in three increasingly
explicit forms:

* `collapsedCoeff_self_eq`: `A_j(j) = β_{j,j} p^{C(j,2)} ∏_{s<j}(p^{s+1} - 1)`;
* `factorial_mul_pow_mul_collapsedCoeff_self`: the same with `β_{j,j}` eliminated using
  `factorial_mul_pow_mul_binomPolyCoeff_self`, giving the division-free identity
  `j! (p-1)^j A_j(j) = p^{C(j,2)} ∏_{s<j}(p^{s+1} - 1)`;
* `exists_int_factorial_mul_pow_mul_collapsedCoeff_self`: the congruence itself, in the shape
  `j! (p-1)^j A_j(j) = p^{C(j,2)} ((p-1)^j + p a)` for an integer `a`, which says exactly that
  `j! A_j(j)/p^{C(j,2)}` differs from `1` by `p a/(p-1)^j`, a rational of positive valuation.

None of the three needs `j ≤ p - 1`: that hypothesis exists only to make `1/j!` `p`-integral, i.e.
to give the congruence's right-hand side a meaning, and the forms above clear `j!` instead of
inverting it. They need only `2 ≤ p`.
-/

@[expose] public section

open Finset Polynomial

namespace GranvilleMoore

/-! ### Rational forms of the coefficient analysis -/

/-- The Gauss sum `∑_{r<j} r = C(j,2)`, the exponent of `p` produced by
`GranvilleMoore.prod_pow_sub_pow_eq_pow_mul`. -/
private theorem sum_range_id_eq_choose_two (j : ℕ) : ∑ r ∈ range j, r = j.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]

/-- The signed coefficient identity `GranvilleMoore.signedCCoeff_sum_eq_prod`, cast into `ℚ`
and evaluated at `z = p^n`. -/
private theorem signedCCoeff_sum_eq_prod_rat (p j n : ℕ) :
    ∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * ((p : ℚ) ^ n) ^ i
      = ∏ r ∈ range j, ((p : ℚ) ^ n - (p : ℚ) ^ r) := by
  have h := congrArg (fun a : ℤ => (a : ℚ)) (signedCCoeff_sum_eq_prod p j ((p : ℤ) ^ n))
  push_cast at h
  exact h

/-- `GranvilleMoore.prod_pow_sub_pow_eq_zero` over `ℚ`. -/
theorem prod_pow_sub_pow_rat_eq_zero {p n j : ℕ} (h : n < j) :
    ∏ r ∈ range j, ((p : ℚ) ^ n - (p : ℚ) ^ r) = 0 := by
  have h' := congrArg (fun a : ℤ => (a : ℚ)) (prod_pow_sub_pow_eq_zero (p := p) h)
  push_cast at h'
  exact h'

/-- `GranvilleMoore.prod_pow_sub_pow_eq_pow_mul` over `ℚ`, with the exponent written as
`C(j,2)`. -/
theorem prod_pow_sub_pow_rat_eq_pow_mul {p n j : ℕ} (h : j ≤ n) :
    ∏ r ∈ range j, ((p : ℚ) ^ n - (p : ℚ) ^ r)
      = (p : ℚ) ^ j.choose 2 * ∏ r ∈ range j, ((p : ℚ) ^ (n - r) - 1) := by
  have h' := congrArg (fun a : ℤ => (a : ℚ)) (prod_pow_sub_pow_eq_pow_mul (p := p) h)
  push_cast at h'
  rw [h', sum_range_id_eq_choose_two]

/-! ### The closed form -/

/-- **`lem_A_formula`**: the collapsed coefficient in closed form,
`A_j(m) = ∑_{n ≤ m} β_{m,n} ∏_{r<j}(p^n - p^r)`.

Substituting the expansion `C(e_i, m) = ∑_{n ≤ m} β_{m,n} (p^n)^i` of
`GranvilleMoore.natCast_choose_frobeniusExponent_eq_sum` into the definition and exchanging
the two finite sums leaves, for each `n`, the signed sum `∑_i (-1)^{j-i} c_{j,i} (p^n)^i`,
which is `∏_{r<j}(p^n - p^r)` by `GranvilleMoore.signedCCoeff_sum_eq_prod`. -/
theorem collapsedCoeff_eq_sum {p : ℕ} (hp : 2 ≤ p) (j m : ℕ) :
    collapsedCoeff p j m
      = ∑ n ∈ range (m + 1),
          binomPolyCoeff p m n * ∏ r ∈ range j, ((p : ℚ) ^ n - (p : ℚ) ^ r) := by
  have hdef : collapsedCoeff p j m
      = ∑ i ∈ range (j + 1),
          (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) *
            ((frobeniusExponent p i).choose m : ℚ) := rfl
  have step : ∀ i ∈ range (j + 1),
      (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * ((frobeniusExponent p i).choose m : ℚ)
        = ∑ n ∈ range (m + 1),
            (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) *
              (binomPolyCoeff p m n * ((p : ℚ) ^ n) ^ i) := fun i _ => by
    rw [natCast_choose_frobeniusExponent_eq_sum hp m i, Finset.mul_sum]
  rw [hdef, Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← signedCCoeff_sum_eq_prod_rat p j n, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **`lem_A_vanishes`**: the collapsed coefficient vanishes in low degree,
`A_j(m) = 0` for `m < j`.

Every index `n` of the closed form satisfies `n ≤ m < j`, so every product vanishes by
`GranvilleMoore.prod_pow_sub_pow_eq_zero`. -/
theorem collapsedCoeff_eq_zero {p : ℕ} (hp : 2 ≤ p) {j m : ℕ} (h : m < j) :
    collapsedCoeff p j m = 0 := by
  rw [collapsedCoeff_eq_sum hp]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [prod_pow_sub_pow_rat_eq_zero (lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hn)) h),
    mul_zero]

/-! ### The valuation -/

/-- A finite sum all of whose terms are `c` times an integer is `c` times an integer. -/
private theorem exists_intCast_sum {c : ℚ} {f : ℕ → ℚ} (s : Finset ℕ)
    (h : ∀ n ∈ s, ∃ a : ℤ, f n = c * (a : ℚ)) : ∃ a : ℤ, ∑ n ∈ s, f n = c * (a : ℚ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert n s hn ih =>
    obtain ⟨a, ha⟩ := h n (Finset.mem_insert_self n s)
    obtain ⟨b, hb⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    refine ⟨a + b, ?_⟩
    rw [Finset.sum_insert hn, ha, hb]
    push_cast
    ring

/-- One term of the closed form, cleared of denominators: for every `n`,
`m! (p-1)^m β_{m,n} ∏_{r<j}(p^n - p^r)` is `p^{C(j,2)}` times an integer.

For `n < j` the product vanishes; for `j ≤ n` it is `p^{C(j,2)}` times the integer
`∏_{r<j}(p^{n-r} - 1)`, and `m! (p-1)^m β_{m,n}` is an integer by
`GranvilleMoore.exists_intCast_eq_factorial_mul_pow_mul_binomPolyCoeff`. -/
private theorem exists_intCast_term {p : ℕ} (hp : p ≠ 1) (j m n : ℕ) :
    ∃ a : ℤ, (m.factorial : ℚ) * ((p : ℚ) - 1) ^ m *
        (binomPolyCoeff p m n * ∏ r ∈ range j, ((p : ℚ) ^ n - (p : ℚ) ^ r))
      = (p : ℚ) ^ j.choose 2 * (a : ℚ) := by
  rcases lt_or_ge n j with h | h
  · exact ⟨0, by rw [prod_pow_sub_pow_rat_eq_zero h]; push_cast; ring⟩
  obtain ⟨a, ha⟩ := exists_intCast_eq_factorial_mul_pow_mul_binomPolyCoeff hp m n
  refine ⟨a * ∏ r ∈ range j, ((p : ℤ) ^ (n - r) - 1), ?_⟩
  rw [prod_pow_sub_pow_rat_eq_pow_mul h]
  push_cast
  linear_combination ((p : ℚ) ^ j.choose 2 * ∏ r ∈ range j, ((p : ℚ) ^ (n - r) - 1)) * ha

/-- **`lem_A_valuation`, algebraic form**: `m! (p-1)^m A_j(m) / p^{C(j,2)}` is an integer.

This is the unconditional content behind the valuation inequality: it exhibits the denominator of
`A_j(m)` explicitly as `m! (p-1)^m` and its `p`-power numerator as `p^{C(j,2)}`. In the closed form
every term with `n < j` vanishes and every term with `n ≥ j` contributes a factor `p^{C(j,2)}`. -/
theorem exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff {p : ℕ} (hp : 2 ≤ p)
    (j m : ℕ) :
    ∃ a : ℤ, (m.factorial : ℚ) * ((p : ℚ) - 1) ^ m * collapsedCoeff p j m
      = (p : ℚ) ^ j.choose 2 * (a : ℚ) := by
  rw [collapsedCoeff_eq_sum hp, Finset.mul_sum]
  exact exists_intCast_sum _ fun n _ => exists_intCast_term (by omega) j m n

/-- **`lem_A_valuation`**: `v_p(A_j(m)) ≥ C(j,2) - v_p(m!)`.

Taking `p`-adic valuations in the algebraic form
`GranvilleMoore.exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff`: the integer on the
right has nonnegative valuation and `v_p((p-1)^m) = 0`, so
`v_p(m!) + v_p(A_j(m)) ≥ C(j,2)`.

The hypothesis `A_j(m) ≠ 0` is needed because `padicValRat p 0 = 0`; a consumer that cannot
supply it should use the algebraic form, which has no side condition. -/
theorem le_padicValRat_collapsedCoeff {p : ℕ} (hp : p.Prime) {j m : ℕ}
    (h : collapsedCoeff p j m ≠ 0) :
    (j.choose 2 : ℤ) - padicValRat p (m.factorial : ℚ)
      ≤ padicValRat p (collapsedCoeff p j m) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfac : (m.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : ((p : ℚ) - 1) ≠ 0 := sub_ne_zero_of_ne fun hx => hp.ne_one (by exact_mod_cast hx)
  have hpm : ((p : ℚ) - 1) ^ m ≠ 0 := pow_ne_zero _ hp1
  obtain ⟨a, ha⟩ := exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff hp.two_le j m
  have hL : (m.factorial : ℚ) * ((p : ℚ) - 1) ^ m * collapsedCoeff p j m ≠ 0 :=
    mul_ne_zero (mul_ne_zero hfac hpm) h
  have ha0 : (a : ℚ) ≠ 0 := fun hz => hL (by rw [ha, hz, mul_zero])
  have hint : 0 ≤ padicValRat p (a : ℚ) := by rw [padicValRat.of_int]; positivity
  have hval := congrArg (padicValRat p) ha
  rw [padicValRat.mul (mul_ne_zero hfac hpm) h, padicValRat.mul hfac hpm,
    padicValRat.pow ((p : ℚ) - 1), padicValRat_natCast_sub_one hp, mul_zero, add_zero,
    padicValRat.mul (pow_ne_zero _ hp0) ha0, padicValRat.pow (p : ℚ),
    padicValRat.self hp.one_lt, mul_one] at hval
  linarith

/-! ### The leading coefficient -/

/-- `X - 1 - C c` is `X - C (1 + c)`, hence monic of degree one. -/
private theorem monic_X_sub_one_sub_C (c : ℚ) : (X - 1 - C c : ℚ[X]).Monic := by
  rw [show (X - 1 - C c : ℚ[X]) = X - C (1 + c) by rw [map_add, map_one]; ring]
  exact monic_X_sub_C _

private theorem natDegree_X_sub_one_sub_C (c : ℚ) : (X - 1 - C c : ℚ[X]).natDegree = 1 := by
  rw [show (X - 1 - C c : ℚ[X]) = X - C (1 + c) by rw [map_add, map_one]; ring, natDegree_X_sub_C]

/-- The polynomial `∏_{s<m} (X - 1 - s(p-1))` of `GranvilleMoore.C_mul_binomPoly_eq_prod` is
monic of degree `m`, so its coefficient in degree `m` is `1`. -/
private theorem coeff_prod_X_sub_one_sub_C_self (p m : ℕ) :
    (∏ s ∈ range m, (X - 1 - C ((s : ℚ) * ((p : ℚ) - 1)))).coeff m = 1 := by
  have hmon : (∏ s ∈ range m, (X - 1 - C ((s : ℚ) * ((p : ℚ) - 1)))).Monic :=
    monic_prod_of_monic _ _ fun s _ => monic_X_sub_one_sub_C _
  have hdeg : (∏ s ∈ range m, (X - 1 - C ((s : ℚ) * ((p : ℚ) - 1)))).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_sub_one_sub_C _]
    simp only [natDegree_X_sub_one_sub_C, Finset.sum_const, card_range, smul_eq_mul, mul_one]
  have := hmon.coeff_natDegree
  rwa [hdeg] at this

/-- **The leading coefficient of `B_m`**: `m! (p-1)^m β_{m,m} = 1`, i.e.
`β_{m,m} = 1/(m! (p-1)^m)`.

Clearing the denominators of `B_m` turns it into the monic polynomial
`∏_{s<m} (X - 1 - s(p-1))` of degree `m` (`GranvilleMoore.C_mul_binomPoly_eq_prod`), whose
top coefficient is `1`. -/
theorem factorial_mul_pow_mul_binomPolyCoeff_self {p : ℕ} (hp : p ≠ 1) (m : ℕ) :
    (m.factorial : ℚ) * ((p : ℚ) - 1) ^ m * binomPolyCoeff p m m = 1 := by
  rw [binomPolyCoeff, ← coeff_C_mul, C_mul_binomPoly_eq_prod hp m,
    coeff_prod_X_sub_one_sub_C_self]

/-- Re-indexing the unit product by `s = j - 1 - r`:
`∏_{r<j}(p^{j-r} - 1) = ∏_{s<j}(p^{s+1} - 1)`. -/
private theorem prod_pow_sub_one_reflect (p j : ℕ) :
    ∏ r ∈ range j, ((p : ℚ) ^ (j - r) - 1) = ∏ s ∈ range j, ((p : ℚ) ^ (s + 1) - 1) := by
  rw [← Finset.prod_range_reflect (fun s => ((p : ℚ) ^ (s + 1) - 1)) j]
  refine Finset.prod_congr rfl fun s hs => ?_
  have hsj : s < j := mem_range.mp hs
  rw [show j - s = j - 1 - s + 1 by omega]

/-- **`lem_A_leading`, the factorisation**:
`A_j(j) = β_{j,j} p^{C(j,2)} ∏_{s<j}(p^{s+1} - 1)`.

In the closed form with `m = j` every term with `n < j` vanishes, leaving the single term
`β_{j,j} ∏_{r<j}(p^j - p^r)`; that product factors as `p^{C(j,2)} ∏_{r<j}(p^{j-r} - 1)` by
`GranvilleMoore.prod_pow_sub_pow_eq_pow_mul`, and re-indexing by `s = j - 1 - r` turns the
remaining product into `∏_{s<j}(p^{s+1} - 1)`, each of whose factors is `≡ -1 (mod p)`. -/
theorem collapsedCoeff_self_eq {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    collapsedCoeff p j j
      = binomPolyCoeff p j j * (p : ℚ) ^ j.choose 2 *
          ∏ s ∈ range j, ((p : ℚ) ^ (s + 1) - 1) := by
  rw [collapsedCoeff_eq_sum hp, Finset.sum_range_succ,
    Finset.sum_eq_zero (fun n hn => by
      rw [prod_pow_sub_pow_rat_eq_zero (mem_range.mp hn), mul_zero]), zero_add,
    prod_pow_sub_pow_rat_eq_pow_mul (le_refl j), prod_pow_sub_one_reflect, mul_assoc]

/-- **`lem_A_leading`, division-free**:
`j! (p-1)^j A_j(j) = p^{C(j,2)} ∏_{s<j}(p^{s+1} - 1)`.

The factorisation of `GranvilleMoore.collapsedCoeff_self_eq` with `β_{j,j}` eliminated by
`GranvilleMoore.factorial_mul_pow_mul_binomPolyCoeff_self`. Dividing by `p^{C(j,2)}` and by
`(p-1)^j` this reads `A_j(j)/p^{C(j,2)} = (1/j!) ∏_{s<j}(p^{s+1}-1)/(p-1)^j`, which is the
displayed formula of the paper's proof. -/
theorem factorial_mul_pow_mul_collapsedCoeff_self {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    (j.factorial : ℚ) * ((p : ℚ) - 1) ^ j * collapsedCoeff p j j
      = (p : ℚ) ^ j.choose 2 * ∏ s ∈ range j, ((p : ℚ) ^ (s + 1) - 1) := by
  rw [collapsedCoeff_self_eq hp]
  linear_combination ((p : ℚ) ^ j.choose 2 * ∏ s ∈ range j, ((p : ℚ) ^ (s + 1) - 1)) *
    factorial_mul_pow_mul_binomPolyCoeff_self (p := p) (by omega) j

/-- Both `∏_{s<j}(p^{s+1} - 1)` and `(p-1)^j` are `≡ (-1)^j (mod p)`, so `p` divides their
difference. -/
private theorem dvd_prod_pow_sub_one_sub_pow (p j : ℕ) :
    (p : ℤ) ∣ (∏ s ∈ range j, ((p : ℤ) ^ (s + 1) - 1)) - ((p : ℤ) - 1) ^ j := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
  push_cast
  simp

/-- **`lem_A_leading`, the congruence**: there is an integer `a` with
`j! (p-1)^j A_j(j) = p^{C(j,2)} ((p-1)^j + p a)`.

Equivalently `j! A_j(j)/p^{C(j,2)} = 1 + p a/(p-1)^j`, and since `p ∤ p - 1` the correction
term has positive valuation: this is the congruence `A_j(j)/p^{C(j,2)} ≡ 1/j! (mod p)`, with
`j!` cleared instead of inverted. It comes from the division-free identity together with
`∏_{s<j}(p^{s+1} - 1) ≡ (p-1)^j (mod p)`, both sides being `≡ (-1)^j`. -/
theorem exists_int_factorial_mul_pow_mul_collapsedCoeff_self {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    ∃ a : ℤ, (j.factorial : ℚ) * ((p : ℚ) - 1) ^ j * collapsedCoeff p j j
      = (p : ℚ) ^ j.choose 2 * (((p : ℚ) - 1) ^ j + (p : ℚ) * (a : ℚ)) := by
  obtain ⟨a, ha⟩ := dvd_prod_pow_sub_one_sub_pow p j
  refine ⟨a, ?_⟩
  have h := congrArg (fun z : ℤ => (z : ℚ)) ha
  push_cast at h
  rw [factorial_mul_pow_mul_collapsedCoeff_self hp]
  linear_combination ((p : ℚ) ^ j.choose 2) * h

end GranvilleMoore
