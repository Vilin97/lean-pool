/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# Dickson permutation lemmas

Mathlib already has the Dickson polynomials `Polynomial.dickson 1 1 m` together
with

* `Polynomial.dickson_one_one_eval_add_inv :
     x * y = 1 → (dickson 1 1 n).eval (x + y) = x ^ n + y ^ n`
* `Polynomial.dickson_one_one_mul :
     dickson 1 1 (m * n) = (dickson 1 1 m).comp (dickson 1 1 n)`
* `Nat.pow_sub_one_gcd_pow_sub_one`

What it lacks, and what is proved here, is the permutation criterion `D_m`
permutes a finite field `K` as soon as `gcd(m, |K|² - 1) = 1`, its two
arithmetic instances for the exponents `2^k - 1` and `(2^k+1)/3`, and the
consequence that `D_(3h)` and `D_3` have the same value distribution whenever
`D_h` is a permutation.
-/

open Polynomial

namespace KasamiCyclicAdditive

/-! ## Auxiliary lemmas for the permutation criterion -/

/-- Every element `x` of a finite field `K` is of the form `u + u⁻¹` for a nonzero `u`
in the algebraic closure of `K`: take `u` to be a root of `Y² - x*Y + 1`. -/
theorem exists_add_inv_eq (K : Type*) [Field K] (x : K) :
    ∃ u : AlgebraicClosure K, u ≠ 0 ∧ u + u⁻¹ = algebraMap K (AlgebraicClosure K) x := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root
      (X ^ 2 - C (algebraMap K (AlgebraicClosure K) x) * X + 1)
      (by
        rw [show (X ^ 2 - C (algebraMap K (AlgebraicClosure K) x) * X + 1 :
            Polynomial (AlgebraicClosure K)).degree = 2 from by compute_degree!]
        decide)
  have hu' : u ^ 2 - (algebraMap K (AlgebraicClosure K) x) * u + 1 = 0 := by
    simpa [IsRoot] using hu
  have hu0 : u ≠ 0 := by
    rintro rfl; simp at hu'
  refine ⟨u, hu0, ?_⟩
  field_simp
  linear_combination hu'

/-- If `u + u⁻¹` lies in the finite field `K` (of cardinality `q`), then `u` lies in a
quadratic extension of `K`, i.e. `u ^ (q ^ 2) = u`.  Proof: the `q`-power map is a ring
homomorphism fixing `K`, so it sends the root `u` of `Y² - x*Y + 1` to a root, and the two
roots are `u` and `u⁻¹`. -/
theorem pow_card_sq_eq_self (K : Type*) [Field K] [Fintype K] (x : K)
    (u : AlgebraicClosure K) (hu0 : u ≠ 0)
    (hx : u + u⁻¹ = algebraMap K (AlgebraicClosure K) x) :
    u ^ (Fintype.card K ^ 2) = u := by
  have := ringChar.charP K
  obtain ⟨n, hp, hc⟩ := FiniteField.card K (ringChar K)
  have : Fact (Nat.Prime (ringChar K)) := ⟨hp⟩
  set p := ringChar K
  set q := Fintype.card K with hq
  have heq : u ^ 2 - (algebraMap K (AlgebraicClosure K) x) * u + 1 = 0 := by
    have h := hx
    field_simp at h
    linear_combination h
  have key : u ^ q = u ∨ u ^ q = u⁻¹ := by
    have hψ := congrArg (iterateFrobenius (AlgebraicClosure K) p n) heq
    simp only [map_add, map_sub, map_mul, map_one, map_pow, map_zero,
      iterateFrobenius_def, ← hc] at hψ
    have hax : (algebraMap K (AlgebraicClosure K) x) ^ q
        = algebraMap K (AlgebraicClosure K) x := by
      rw [← map_pow, hq, FiniteField.pow_card]
    rw [hax] at hψ
    have hfac : (u * u ^ q - 1) * (u ^ q - u) = 0 := by
      linear_combination u * hψ - u ^ q * heq
    rcases mul_eq_zero.1 hfac with h | h
    · right
      field_simp
      linear_combination h
    · left; linear_combination h
  rcases key with h | h
  · rw [sq, pow_mul, h, h]
  · rw [sq, pow_mul, h, inv_pow, h, inv_inv]

/-- An element of the quadratic extension with `u + u⁻¹` in `K` is an
`(q² - 1)`-th root of unity. -/
theorem pow_card_sq_sub_one_eq_one (K : Type*) [Field K] [Fintype K] (x : K)
    {u : AlgebraicClosure K} (hu0 : u ≠ 0)
    (hux : u + u⁻¹ = algebraMap K (AlgebraicClosure K) x) :
    u ^ (Fintype.card K ^ 2 - 1) = 1 := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq4 : 4 ≤ Fintype.card K ^ 2 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ Fintype.card K ^ 2 := Nat.pow_le_pow_left hq 2
  have h := pow_card_sq_eq_self K x u hu0 hux
  have h' : u ^ (Fintype.card K ^ 2 - 1) * u = 1 * u := by
    rw [one_mul, ← pow_succ, show Fintype.card K ^ 2 - 1 + 1 = Fintype.card K ^ 2 by omega]
    exact h
  exact mul_right_cancel₀ hu0 h'

/-- Dickson evaluation in the quadratic extension: `D_m(u + u⁻¹) = u^m + u^(-m)`. -/
theorem dickson_eval_eq_pow_add_inv_pow (K : Type*) [Field K] (x : K)
    {u : AlgebraicClosure K} (hu0 : u ≠ 0)
    (hux : u + u⁻¹ = algebraMap K (AlgebraicClosure K) x) (m : ℕ) :
    algebraMap K (AlgebraicClosure K) ((dickson 1 1 m).eval x) = u ^ m + (u⁻¹) ^ m := by
  rw [← Polynomial.eval₂_at_apply (algebraMap K (AlgebraicClosure K)) x,
    ← Polynomial.eval_map, Polynomial.map_dickson, map_one,
    ← hux, dickson_one_one_eval_add_inv u u⁻¹ (mul_inv_cancel₀ hu0)]

/-- Raising to the `m`-th power is injective on `N`-th roots of unity when `gcd(m, N) = 1`. -/
private theorem pow_left_injective_of_coprime {L : Type*} [Field L] {N m : ℕ} (hN : 1 < N)
    (hm : Nat.Coprime m N) {a b : L} (ha : a ^ N = 1) (hb : b ^ N = 1)
    (hab : a ^ m = b ^ m) : a = b := by
  obtain ⟨m', -, hmm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hN
  have hdm : N * (m * m' / N) + 1 = m * m' := by
    have := Nat.div_add_mod (m * m') N
    omega
  have expand : ∀ c : L, c ^ N = 1 → c ^ (m * m') = c := by
    intro c hc
    rw [← hdm, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]
  calc a = a ^ (m * m') := (expand a ha).symm
    _ = (a ^ m) ^ m' := by rw [pow_mul]
    _ = (b ^ m) ^ m' := by rw [hab]
    _ = b ^ (m * m') := by rw [pow_mul]
    _ = b := expand b hb

/-! ## The permutation criterion -/

/-- `D_m` permutes a finite field `K` as soon as `m` is coprime to `|K|² - 1`.

Proof sketch.  Let `q = |K|` and let `L` be an extension of `K` with `q²`
elements.  Every `x : K` is `u + u⁻¹` for some `u : Lˣ`: the polynomial
`Y² - x*Y + 1` has its roots in `L`, and their product is `1`.  By
`dickson_one_one_eval_add_inv`, `D_m(u + u⁻¹) = u^m + u^(-m)`. Coprimality of
`m` with `q² - 1 = |Lˣ|` makes `u ↦ u^m` a bijection of `Lˣ` commuting with
`u ↦ u⁻¹`, hence a bijection of the set of unordered pairs `{u, u⁻¹}`, which is
exactly `K` under `u ↦ u + u⁻¹`.  Since `K` is finite it is enough to prove
injectivity. -/
theorem dickson_bijective {K : Type*} [Field K] [Fintype K] {m : ℕ}
    (hm : Nat.Coprime m (Fintype.card K ^ 2 - 1)) :
    Function.Bijective (fun x : K => (dickson 1 1 m).eval x) := by
  rw [← Finite.injective_iff_bijective]
  intro x₁ x₂ hx
  simp only at hx
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq4 : 4 ≤ Fintype.card K ^ 2 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ Fintype.card K ^ 2 := Nat.pow_le_pow_left hq 2
  have hN : 1 < Fintype.card K ^ 2 - 1 := by omega
  obtain ⟨u₁, hu₁0, hu₁⟩ := exists_add_inv_eq K x₁
  obtain ⟨u₂, hu₂0, hu₂⟩ := exists_add_inv_eq K x₂
  have h1 := pow_card_sq_sub_one_eq_one K x₁ hu₁0 hu₁
  have h2 := pow_card_sq_sub_one_eq_one K x₂ hu₂0 hu₂
  have key : u₁ ^ m + (u₁⁻¹) ^ m = u₂ ^ m + (u₂⁻¹) ^ m := by
    rw [← dickson_eval_eq_pow_add_inv_pow K x₁ hu₁0 hu₁ m,
      ← dickson_eval_eq_pow_add_inv_pow K x₂ hu₂0 hu₂ m, hx]
  rw [inv_pow, inv_pow] at key
  have hv0 : u₁ ^ m ≠ 0 := pow_ne_zero _ hu₁0
  have hw0 : u₂ ^ m ≠ 0 := pow_ne_zero _ hu₂0
  have hfac : (u₁ ^ m - u₂ ^ m) * (u₁ ^ m * u₂ ^ m - 1) = 0 := by
    field_simp at key
    linear_combination key
  rcases mul_eq_zero.1 hfac with h | h
  · have huu : u₁ = u₂ := pow_left_injective_of_coprime hN hm h1 h2 (by linear_combination h)
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [← hu₁, ← hu₂, huu]
  · have hinv : u₂ ^ m = (u₁⁻¹) ^ m := by
      rw [inv_pow]
      field_simp
      linear_combination h
    have h1' : (u₁⁻¹) ^ (Fintype.card K ^ 2 - 1) = 1 := by
      rw [inv_pow, h1, inv_one]
    have huu : u₂ = u₁⁻¹ := pow_left_injective_of_coprime hN hm h2 h1' hinv
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [← hu₁, ← hu₂, huu, inv_inv]
    ring

/-! ## The two arithmetic instances -/

/-- `2^k - 1` is coprime to `2^(2n) - 1` when `gcd(k, 2n) = 1`.

Immediate from
`Nat.pow_sub_one_gcd_pow_sub_one`: `gcd(2^a - 1, 2^b - 1) = 2^gcd(a,b) - 1`,
here `2^1 - 1 = 1`. -/
theorem coprime_two_pow_sub_one {k n : ℕ} (hkn : Nat.Coprime k (2 * n)) :
    Nat.Coprime (2 ^ k - 1) (2 ^ (2 * n) - 1) := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 k (2 * n)
  unfold Nat.Coprime at *
  rw [hg, hkn]
  norm_num

/-- With `3 * h = 2^k + 1`, `gcd(k, n) = 1` and `3 ∤ h`, the number `h` is
coprime to `2^(2n) - 1`.

This is where the normalisation `k ≢ 3 (mod 6)` enters: that condition is
exactly `3 ∤ h`.

Proof.  `2^k + 1` divides `2^(2k) - 1`, and by `Nat.pow_sub_one_gcd_pow_sub_one`,
`gcd(2^(2k) - 1, 2^(2n) - 1) = 2^(2 gcd(k,n)) - 1 = 3`. So
`gcd(2^k + 1, 2^(2n) - 1)` divides `3`; it *is* `3`, since `3` divides both.
Hence `gcd(3h, 2^(2n) - 1) = 3`, so `d := gcd(h, 2^(2n) - 1)` divides `3` and is
`1` or `3`.  It is `3` only if `3 ∣ h`, which is excluded. -/
theorem coprime_third_of_two_pow_add_one {k n h : ℕ} (hkn : Nat.Coprime k n)
    (hh : 3 * h = 2 ^ k + 1) (h3 : ¬ (3 ∣ h)) :
    Nat.Coprime h (2 ^ (2 * n) - 1) := by
  set N := 2 ^ (2 * n) - 1 with hNdef
  have hsq : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [pow_mul']
  have hA : (2 ^ k + 1) ∣ (2 ^ (2 * k) - 1) := by
    refine ⟨2 ^ k - 1, ?_⟩
    rw [hsq, ← Nat.sq_sub_sq (2 ^ k) 1]
  have hg : Nat.gcd (2 ^ (2 * k) - 1) N = 3 := by
    rw [hNdef, Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_mul_left, hkn]
    norm_num
  have hdh : Nat.gcd h N ∣ h := Nat.gcd_dvd_left _ _
  have hdN : Nat.gcd h N ∣ N := Nat.gcd_dvd_right _ _
  have hd3 : Nat.gcd h N ∣ 3 := by
    have h1 : Nat.gcd h N ∣ 2 ^ (2 * k) - 1 := (hh ▸ Dvd.dvd.mul_left hdh 3).trans hA
    rw [← hg]
    exact Nat.dvd_gcd h1 hdN
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hdh) h3

/-! ## The payoff -/

/-- If `e = 3h` and `D_h` permutes `K`, then `D_e` and `D_3` have the same
value distribution, in the strong sense that they give equal sums against any
function.

`dickson_one_one_mul` gives `D_e = D_3 ∘ D_h`, so the substitution `y = D_h x`
— a bijection by `dickson_bijective` — turns one sum into the other. -/
theorem sum_dickson_eq_cubic {K : Type*} [Field K] [Fintype K]
    {M : Type*} [AddCommMonoid M] {e h : ℕ} (he : e = 3 * h)
    (hh : Nat.Coprime h (Fintype.card K ^ 2 - 1)) (f : K → M) :
    ∑ x : K, f ((dickson 1 1 e).eval x) = ∑ x : K, f ((dickson 1 1 3).eval x) := by
  refine Fintype.sum_bijective (fun x : K => (dickson 1 1 h).eval x) (dickson_bijective hh)
    _ _ ?_
  intro x
  rw [he, Polynomial.dickson_one_one_mul, Polynomial.eval_comp]

end KasamiCyclicAdditive
