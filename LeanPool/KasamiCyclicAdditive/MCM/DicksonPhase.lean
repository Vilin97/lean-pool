/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.MCM.DicksonPermutation

/-!
# Dickson value sum for every odd normalized parameter

Removes the residual `3 ∤ h` restriction from `sum_dickson_eq_cubic`: for
every odd `k` coprime to `n`, `D_(2^k+1)` and `D_3` have equal sums against any
function on `GF(2^n)`, even at the odd-dimensional bad residue `k ≡ 3 (mod 6)`.
-/

open Finset Polynomial

namespace KasamiCyclicAdditive

/-! ### Elementary arithmetic facts about `2 ^ k + 1` -/

/-- `3` divides `2 * 4 ^ m + 1`. -/
private lemma three_dvd_two_mul_four_pow_add_one (m : ℕ) : 3 ∣ 2 * 4 ^ m + 1 := by
  induction m with
  | zero => decide
  | succ i ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨4 * c - 1, by rw [pow_succ]; omega⟩

/-- For odd `k`, `3` divides `2 ^ k + 1`. -/
private lemma three_dvd_two_pow_add_one {k : ℕ} (hk : Odd k) : 3 ∣ 2 ^ k + 1 := by
  obtain ⟨m, rfl⟩ := hk
  have h : (2 : ℕ) ^ (2 * m + 1) + 1 = 2 * 4 ^ m + 1 := by rw [pow_succ, pow_mul]; ring
  rw [h]
  exact three_dvd_two_mul_four_pow_add_one m

/-- `9 ∣ 2 ^ m + 1` exactly when `m ≡ 3 (mod 6)`. -/
private lemma nine_dvd_two_pow_add_one_iff (m : ℕ) : 9 ∣ 2 ^ m + 1 ↔ m % 6 = 3 := by
  have key : (2 : ℕ) ^ m % 9 = 2 ^ (m % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod m 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  constructor
  · intro h
    interval_cases hm : (m % 6) <;> omega
  · intro h
    rw [h] at key
    norm_num at key
    omega

/-! ### The Dickson evaluation on `GF(2 ^ n)` only depends on the exponent mod `2 ^ (2n) - 1` -/

/-- On a field `K` with `|K| = 2 ^ n`, the value of `D_m` at a point only depends on `m`
modulo `2 ^ (2 * n) - 1`.  This is proved by writing a point as `u + u⁻¹` in the algebraic
closure, where `u` satisfies `u ^ (2 ^ (2 * n)) = u`. -/
private lemma dickson_eval_period {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (hcard : Fintype.card K = 2 ^ n) (x : K) (a t : ℕ) :
    (dickson 1 1 (a + t * (2 ^ (2 * n) - 1))).eval x = (dickson 1 1 a).eval x := by
  classical
  obtain ⟨u, hu0, hxu⟩ := exists_add_inv_eq K x
  have hfinj : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
    (algebraMap K (AlgebraicClosure K)).injective
  -- `u` lies in the quadratic extension: its order divides `2^(2n) - 1`
  have hexp : Fintype.card K ^ 2 = 2 ^ (2 * n) := by
    rw [hcard, ← pow_mul, Nat.mul_comm]
  have hper : u ^ (2 ^ (2 * n) - 1) = 1 := by
    have h := pow_card_sq_sub_one_eq_one K x hu0 hxu
    rwa [hexp] at h
  have hperinv : (u⁻¹) ^ (2 ^ (2 * n) - 1) = 1 := by rw [inv_pow, hper, inv_one]
  have main : ∀ m : ℕ,
      algebraMap K (AlgebraicClosure K) ((dickson 1 1 m).eval x) = u ^ m + (u⁻¹) ^ m :=
    fun m => dickson_eval_eq_pow_add_inv_pow K x hu0 hxu m
  have e1 : u ^ (a + t * (2 ^ (2 * n) - 1)) = u ^ a := by
    rw [pow_add, pow_mul', hper, one_pow, mul_one]
  have e2 : (u⁻¹) ^ (a + t * (2 ^ (2 * n) - 1)) = (u⁻¹) ^ a := by
    rw [pow_add, pow_mul', hperinv, one_pow, mul_one]
  refine hfinj ?_
  rw [main, main, e1, e2]

/-- The non-exceptional case: for odd `m` coprime to `n` with `9 ∤ 2^m + 1`, the
Dickson value-sums of `D_(2^m+1)` and `D_3` agree. -/
private lemma sum_dickson_eq_three_of_not_nine_dvd
    {K : Type*} [Field K] [Fintype K]
    {M : Type*} [AddCommMonoid M]
    {n m : ℕ} (hcard : Fintype.card K = 2 ^ n)
    (hm : Odd m) (hmn : Nat.Coprime m n) (h9 : ¬ (9 ∣ 2 ^ m + 1)) (f : K → M) :
    ∑ x : K, f ((dickson 1 1 (2 ^ m + 1)).eval x)
      = ∑ x : K, f ((dickson 1 1 3).eval x) := by
  classical
  have hcard2 : Fintype.card K ^ 2 - 1 = 2 ^ (2 * n) - 1 := by
    rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨h, hh⟩ := three_dvd_two_pow_add_one hm
  have h3 : ¬ (3 ∣ h) := by
    rintro ⟨c, rfl⟩
    exact h9 ⟨c, by omega⟩
  have hcop : Nat.Coprime h (Fintype.card K ^ 2 - 1) := by
    rw [hcard2]
    exact coprime_third_of_two_pow_add_one hmn hh.symm h3
  exact sum_dickson_eq_cubic hh hcop f

/-- For every odd Kasami parameter `k` coprime to `n`, the Dickson
polynomial `D_(2^k+1)` has the same value distribution on `GF(2^n)` as `D_3`, in
the strong form of equality of sums against an arbitrary function.

This is the form consumed by the MCM phase proof, and it covers the residue
`k ≡ 3 (mod 6)`, where `9 ∣ 2^k + 1` rules out the generic Dickson permutation
argument. -/
theorem sum_dickson_kasami_eq_three
    {K : Type*} [Field K] [Fintype K]
    {M : Type*} [AddCommMonoid M]
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n)
    (hk : Odd k) (hkn : Nat.Coprime k n) (f : K → M) :
    ∑ x : K, f ((dickson 1 1 (2 ^ k + 1)).eval x)
      = ∑ x : K, f ((dickson 1 1 3).eval x) := by
  classical
  by_cases h9 : 9 ∣ 2 ^ k + 1
  · have hk6 : k % 6 = 3 := (nine_dvd_two_pow_add_one_iff k).1 h9
    have h3n : ¬ (3 ∣ n) := by
      intro h3n
      have h3k : 3 ∣ k := by omega
      have : (3 : ℕ) ∣ Nat.gcd k n := Nat.dvd_gcd h3k h3n
      rw [hkn] at this
      omega
    set k' := k + 2 * n with hk'
    have hk'odd : Odd k' := by
      obtain ⟨j, rfl⟩ := hk
      exact ⟨j + n, by rw [hk']; ring⟩
    have hk'n : Nat.Coprime k' n := (Nat.coprime_add_mul_right_left k n 2).mpr hkn
    have hk'6 : k' % 6 ≠ 3 := by omega
    have h9' : ¬ (9 ∣ 2 ^ k' + 1) := fun h => hk'6 ((nine_dvd_two_pow_add_one_iff k').1 h)
    have hshift : ∀ x : K, (dickson 1 1 (2 ^ k' + 1)).eval x
        = (dickson 1 1 (2 ^ k + 1)).eval x := by
      intro x
      have hexp : 2 ^ k' + 1 = (2 ^ k + 1) + 2 ^ k * (2 ^ (2 * n) - 1) := by
        have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
        have : (2 : ℕ) ^ k' = 2 ^ k * 2 ^ (2 * n) := by rw [hk', pow_add]
        rw [this, Nat.mul_sub, mul_one]
        have : (2 : ℕ) ^ k ≤ 2 ^ k * 2 ^ (2 * n) := Nat.le_mul_of_pos_right _ (by positivity)
        omega
      rw [hexp]
      exact dickson_eval_period hcard x _ _
    calc ∑ x : K, f ((dickson 1 1 (2 ^ k + 1)).eval x)
        = ∑ x : K, f ((dickson 1 1 (2 ^ k' + 1)).eval x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hshift x]
      _ = ∑ x : K, f ((dickson 1 1 3).eval x) :=
          sum_dickson_eq_three_of_not_nine_dvd hcard hk'odd hk'n h9' f
  · exact sum_dickson_eq_three_of_not_nine_dvd hcard hk hkn h9 f

end KasamiCyclicAdditive
