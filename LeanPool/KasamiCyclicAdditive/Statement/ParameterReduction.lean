/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Statement.Definitions

/-!
# Reduction of the Kasami parameter modulo the extension degree

The literature statement only requires `gcd(k,n)=1`; it does not normalize
`k` to the range `1 ≤ k < n`.  The substantive proof is naturally carried
out in that range.

This file proves that the Kasami exponent, derivative image, and coefficient
triple count are unchanged when `k` is replaced by `k % n` over a field of
cardinality `2^n`.  Thus the normalization used by the proof is a theorem,
not an extra hypothesis in the statement.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The Kasami exponent is periodic in `k` modulo `n`, modulo the
multiplicative exponent `2^n - 1` of `GF(2^n)^×`. -/
theorem kasamiExponent_modEq_degree (n k : ℕ) :
    kasamiExponent k ≡ kasamiExponent (k % n) [MOD 2 ^ n - 1] := by
  have hk : k = k % n + n * (k / n) := (Nat.mod_add_div k n).symm
  have hbase : 2 ^ n ≡ 1 [MOD 2 ^ n - 1] :=
    Nat.modEq_sub Nat.one_le_two_pow
  have htwo : 2 ^ k ≡ 2 ^ (k % n) [MOD 2 ^ n - 1] := by
    rw [hk, pow_add, pow_mul]
    simpa using (hbase.pow (k / n)).mul_left (2 ^ (k % n))
  have hfour : 4 ^ k ≡ 4 ^ (k % n) [MOD 2 ^ n - 1] := by
    have hsq : ∀ m : ℕ, (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by
      intro m
      rw [← mul_pow]
      norm_num
    rw [hsq k, hsq (k % n)]
    exact htwo.mul htwo
  have hsub :
      4 ^ k - 2 ^ k ≡ 4 ^ (k % n) - 2 ^ (k % n) [MOD 2 ^ n - 1] :=
    Nat.ModEq.sub
      (Nat.pow_le_pow_left (by norm_num) k)
      (Nat.pow_le_pow_left (by norm_num) (k % n))
      hfour htwo
  simpa [kasamiExponent] using hsub.add (Nat.ModEq.refl 1)

omit [DecidableEq K] in
/-- In a finite field, nonzero powers only depend on the exponent modulo
`|K| - 1`.  The nonzero hypotheses on the exponents handle the base `0`
without a separate convention. -/
theorem pow_eq_of_modEq_card_sub_one
    (x : K) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ≡ b [MOD Fintype.card K - 1]) :
    x ^ a = x ^ b := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ha, hb]
  · have hpow : x ^ (Fintype.card K - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one x hx
    have hrem :
        a % (Fintype.card K - 1) = b % (Fintype.card K - 1) := h
    calc
      x ^ a =
          x ^ (a % (Fintype.card K - 1) +
            (Fintype.card K - 1) * (a / (Fintype.card K - 1))) := by
              rw [Nat.mod_add_div]
      _ = x ^ (a % (Fintype.card K - 1)) := by
            rw [pow_add, pow_mul, hpow, one_pow, mul_one]
      _ = x ^ (b % (Fintype.card K - 1)) := by rw [hrem]
      _ = x ^ (b % (Fintype.card K - 1) +
            (Fintype.card K - 1) * (b / (Fintype.card K - 1))) := by
              rw [pow_add, pow_mul, hpow, one_pow, mul_one]
      _ = x ^ b := by rw [Nat.mod_add_div]

omit [DecidableEq K] in
/-- Two distinct nonzero coefficients provide the three distinct field
elements `0`, `v₁`, and `v₂`.  If `|K| = 2^n`, this already forces
`n ≥ 2`; characteristic two is not needed for this cardinality argument. -/
theorem extension_degree_at_least_two_of_coefficients
    {n : ℕ} (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    2 ≤ n := by
  classical
  have hthree : 3 ≤ Fintype.card K := by
    have hset : ({0, v₁, v₂} : Finset K).card = 3 := by
      have h01 : (0 : K) ≠ v₁ := Ne.symm hv₁
      have h02 : (0 : K) ≠ v₂ := Ne.symm hv₂
      simp [h01, h02, hne]
    calc
      3 = ({0, v₁, v₂} : Finset K).card := hset.symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card K := Finset.card_univ
  rw [hcard] at hthree
  by_contra hn
  have hn' : n ≤ 1 := by omega
  interval_cases n <;> norm_num at hthree

/-- If `n ≥ 2` and `k` is coprime to `n`, then `k % n` is the
unique normalized representative needed by the proof: it is positive, below
`n`, and remains coprime to `n`. -/
theorem mod_parameter_admissible
    {n k : ℕ} (hn : 2 ≤ n) (hkn : Nat.Coprime k n) :
    1 ≤ k % n ∧ k % n < n ∧ Nat.Coprime (k % n) n := by
  have hnpos : 0 < n := by omega
  have hrlt : k % n < n := Nat.mod_lt k hnpos
  have hrcoprime : Nat.Coprime (k % n) n := by
    rw [Nat.coprime_iff_gcd_eq_one]
    rw [← Nat.gcd_rec n k]
    simpa [Nat.gcd_comm] using hkn.gcd_eq_one
  have hrpos : 1 ≤ k % n := by
    have hrne : k % n ≠ 0 := by
      intro hrzero
      have hzero : Nat.Coprime 0 n := by
        simpa [hrzero] using hrcoprime
      have hnone : n = 1 := (Nat.coprime_zero_left n).mp hzero
      omega
    omega
  exact ⟨hrpos, hrlt, hrcoprime⟩

omit [DecidableEq K] in
/-- Over a field with `2^n` elements, the normalized Kasami derivative is
unchanged when the parameter is reduced modulo `n`. -/
theorem kasamiDerivative_mod_degree
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) (b : K) :
    kasamiDerivative k b = kasamiDerivative (k % n) b := by
  have hexp :
      kasamiExponent k ≡ kasamiExponent (k % n) [MOD Fintype.card K - 1] := by
    rw [hcard]
    exact kasamiExponent_modEq_degree n k
  have hp (x : K) :
      x ^ kasamiExponent k = x ^ kasamiExponent (k % n) :=
    pow_eq_of_modEq_card_sub_one x
      (by simp [kasamiExponent]) (by simp [kasamiExponent]) hexp
  unfold kasamiDerivative
  rw [hp (b + 1), hp b]

/-- The derivative image is unchanged under `k ↦ k % n`. -/
theorem derivativeImage_mod_degree
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) :
    derivativeImage k K = derivativeImage (k % n) K := by
  apply Finset.image_congr
  intro b _hb
  exact kasamiDerivative_mod_degree hcard b

/-- The coefficient triple count is unchanged under `k ↦ k % n`. -/
theorem coefficientTripleCount_mod_degree
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} :
    coefficientTripleCount k v₁ v₂ =
      coefficientTripleCount (k % n) v₁ v₂ := by
  simp only [coefficientTripleCount,
    derivativeImage_mod_degree (K := K) (n := n) (k := k) hcard]

end KasamiCyclicAdditive
