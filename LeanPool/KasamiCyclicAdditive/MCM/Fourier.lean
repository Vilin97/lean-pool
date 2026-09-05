/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.Arithmetic
import LeanPool.KasamiCyclicAdditive.MCM.Halfspace
import LeanPool.KasamiCyclicAdditive.MCM.FrobeniusSum

/-!
# The MCM Fourier/Dickson reduction

For a multiplicative character `χ` with `χ^(2^k+1) ≠ 1`, additive Fourier
inversion reduces the untwisted and additively twisted MCM character sums

`∑_s χ(M_k s)`  and  `∑_s ψ(s) χ(M_k s)`

to Gauss-sum ratios against sparse Dickson-polynomial character sums, using the
identities

`b^(2^k+1) T_k(b⁻¹)²     = D_(2^k-1)(b)`,
`b^(2^k+1) T_k(1+b⁻¹)²   = D_(2^k+1)(b)`.

For the complementary case of a nonprincipal cubic `χ` and odd `k`, the MCM map
is invisible to `χ`: `χ(M_k s) = χ(s)`.
-/

open Finset Polynomial

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- Untwisted MCM character sum.  Multiplicative characters vanish at zero. -/
noncomputable def mcmCharSum (k : ℕ) (χ : MulChar K ℂ) : ℂ :=
  ∑ s : K, χ (mcmMap k s)

/-- Additively twisted MCM character sum. -/
noncomputable def mcmTwistedCharSum (k : ℕ) (ψ : AddChar K ℂ) (χ : MulChar K ℂ) : ℂ :=
  ∑ s : K, ψ s * χ (mcmMap k s)

/-! ### Characteristic-two preliminaries -/

section CharTwo

omit [Fintype K] [DecidableEq K] in
/-- `frobSum k` is additive, being a sum of `2`-power Frobenius maps. -/
private lemma frobSum_add (k : ℕ) (x y : K) :
    frobSum k (x + y) = frobSum k x + frobSum k y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [frobSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => add_pow_char_pow x y 2 i

omit [Fintype K] [DecidableEq K] [CharP K 2] in
/-- `frobSum k` vanishes at `0`. -/
private lemma frobSum_zero (k : ℕ) : frobSum k (0 : K) = 0 := by
  refine Finset.sum_eq_zero fun i _ => zero_pow ?_
  positivity

omit [Fintype K] [DecidableEq K] in
/-- Squaring `frobSum k` shifts every exponent up by one. -/
private lemma frobSum_sq (k : ℕ) (s : K) :
    frobSum k s ^ 2 = ∑ i ∈ Finset.range k, s ^ (2 ^ (i + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [frobSum, sum_pow_char]
  exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul, pow_succ]

omit [DecidableEq K] [CharP K 2] in
/-- Hence the exponents `2 ^ (n + j)` and `2 ^ j` agree on `K`. -/
private lemma pow_two_pow_add_card {n : ℕ} (hcard : Fintype.card K = 2 ^ n) (a : K) (j : ℕ) :
    a ^ (2 ^ (n + j)) = a ^ (2 ^ j) := by
  rw [pow_add, pow_mul, pow_card_two_pow hcard]

end CharTwo

/-! ### Dickson polynomial identities -/

section Dickson

/-- `D_(d + 2n) + D_d = D_(d + n) * D_n` for Dickson polynomials of parameter `1`. -/
theorem dickson_add_formula (R : Type*) [CommRing R] :
    ∀ n d : ℕ, dickson 1 (1 : R) (d + 2 * n) + dickson 1 1 d
      = dickson 1 1 (d + n) * dickson 1 1 n
  | 0, d => by simp [dickson_zero]; ring
  | 1, d => by
      have h : d + 2 * 1 = d + 2 := by ring
      rw [h, dickson_add_two]; simp; ring
  | (n + 2), d => by
      have h1 := dickson_add_formula R n (d + 2)
      have h2 := dickson_add_formula R (n + 1) (d + 1)
      have e1 : d + 2 + 2 * n = d + 2 * n + 2 := by ring
      have e2 : d + 2 + n = d + n + 2 := by ring
      have e3 : d + 1 + 2 * (n + 1) = d + 2 * n + 3 := by ring
      have e4 : d + 1 + (n + 1) = d + n + 2 := by ring
      rw [e1, e2] at h1
      rw [e3, e4] at h2
      have r1 : dickson 1 (1 : R) (d + 2 * (n + 2))
          = X * dickson 1 1 (d + 2 * n + 3) - dickson 1 1 (d + 2 * n + 2) := by
        have h : d + 2 * (n + 2) = d + 2 * n + 2 + 2 := by ring
        rw [h, dickson_add_two]; simp
      have r2 : dickson 1 (1 : R) (d + 2) = X * dickson 1 1 (d + 1) - dickson 1 1 d := by
        rw [dickson_add_two]; simp
      have r3 : dickson 1 (1 : R) (n + 2) = X * dickson 1 1 (n + 1) - dickson 1 1 n := by
        rw [dickson_add_two]; simp
      have e6 : d + (n + 2) = d + n + 2 := by ring
      rw [r1, r3, e6]
      linear_combination X * h2 - h1 + r2

/-- In characteristic two, `D_(2 ^ k) = X ^ (2 ^ k)`. -/
theorem dickson_two_pow (R : Type*) [CommRing R] [CharP R 2] :
    ∀ k : ℕ, dickson 1 (1 : R) (2 ^ k) = X ^ (2 ^ k)
  | 0 => by simp
  | (k + 1) => by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [pow_succ, dickson_one_one_mul, dickson_two_pow R k, dickson_one_one_charP R 2,
        pow_comp, X_comp, ← pow_mul, ← pow_succ]
      congr 1
      ring

omit [Fintype K] [DecidableEq K] in
/-- In characteristic two every `D_m` vanishes at `0`. -/
private lemma dickson_eval_zero : ∀ m : ℕ, (dickson 1 1 m).eval (0 : K) = 0
  | 0 => by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      simp [dickson_zero]
      linear_combination h2
  | 1 => by simp
  | (m + 2) => by simp [dickson_add_two, dickson_eval_zero m]

omit [Fintype K] [DecidableEq K] in
/-- `D_(2 ^ (k+1) - 1) = X ^ (2 ^ k) * D_(2 ^ k - 1) + X`. -/
private lemma dickson_pred_succ (k : ℕ) :
    dickson 1 (1 : K) (2 ^ (k + 1) - 1) = X ^ (2 ^ k) * dickson 1 1 (2 ^ k - 1) + X := by
  have h2 : (2 : K[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero K[X] 2
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have key := dickson_add_formula K (2 ^ k - 1) 1
  have e1 : 1 + 2 * (2 ^ k - 1) = 2 ^ (k + 1) - 1 := by omega
  have e2 : 1 + (2 ^ k - 1) = 2 ^ k := by omega
  rw [e1, e2, dickson_two_pow K k] at key
  simp only [dickson_one] at key
  linear_combination key - X * h2

omit [Fintype K] [DecidableEq K] in
/-- `D_(2 ^ k + 1) = X ^ (2 ^ k + 1) + D_(2 ^ k - 1)`. -/
private lemma dickson_succ_two_pow (k : ℕ) :
    dickson 1 (1 : K) (2 ^ k + 1) = X ^ (2 ^ k + 1) + dickson 1 1 (2 ^ k - 1) := by
  have h2 : (2 : K[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero K[X] 2
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have key := dickson_add_two 1 (1 : K) (2 ^ k - 1)
  have e1 : 2 ^ k - 1 + 2 = 2 ^ k + 1 := by omega
  have e2 : 2 ^ k - 1 + 1 = 2 ^ k := by omega
  rw [e1, e2, dickson_two_pow K k] at key
  rw [key]
  simp only [map_one, one_mul]
  have h : X * X ^ (2 ^ k) = (X : K[X]) ^ (2 ^ k + 1) := by ring
  rw [h]
  linear_combination -dickson 1 (1 : K) (2 ^ k - 1) * h2

omit [Fintype K] [DecidableEq K] in
/-- Sparse Dickson identity `b^(2^k+1) * T_k(b⁻¹)^2 = D_(2^k-1)(b)`. -/
private lemma sparse_dickson_pred : ∀ (k : ℕ) (b : K), b ≠ 0 →
    b ^ (2 ^ k + 1) * frobSum k b⁻¹ ^ 2 = (dickson 1 1 (2 ^ k - 1)).eval b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro k
  induction k with
  | zero => intro b hb; simp [frobSum]; linear_combination -h2
  | succ k ih =>
    intro b hb
    have hsq : frobSum (k + 1) b⁻¹ ^ 2 = frobSum k b⁻¹ ^ 2 + (b⁻¹) ^ (2 ^ (k + 1)) := by
      rw [frobSum_succ, add_pow_char, ← pow_mul, ← pow_succ]
    have hexp : (2 : ℕ) ^ (k + 1) + 1 = 2 ^ k + (2 ^ k + 1) := by ring
    have h3 : b ^ (2 ^ (k + 1) + 1) * (b⁻¹) ^ (2 ^ (k + 1)) = b := by
      rw [inv_pow, hexp, pow_add]
      field_simp
      rw [← pow_succ]
      ring
    rw [hsq, mul_add, h3, hexp, pow_add, mul_assoc, ih b hb, dickson_pred_succ k]
    simp

omit [Fintype K] [DecidableEq K] in
/-- Sparse Dickson identity `b^(2^k+1) * T_k(1+b⁻¹)^2 = D_(2^k+1)(b)`. -/
private lemma sparse_dickson_succ {k : ℕ} (hk : Odd k) (b : K) (hb : b ≠ 0) :
    b ^ (2 ^ k + 1) * frobSum k (1 + b⁻¹) ^ 2 = (dickson 1 1 (2 ^ k + 1)).eval b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsum : frobSum k (1 + b⁻¹) = 1 + frobSum k b⁻¹ := by
    rw [frobSum_add, frobSum_one hk]
  have hsq : frobSum k (1 + b⁻¹) ^ 2 = 1 + frobSum k b⁻¹ ^ 2 := by
    rw [hsum, add_pow_char, one_pow]
  rw [hsq, mul_add, mul_one, sparse_dickson_pred k b hb, dickson_succ_two_pow k]
  simp

end Dickson

/-! ### Character preliminaries -/

section Characters

omit [DecidableEq K] [CharP K 2] in
/-- Shifted Gauss sum evaluation, valid also at `c = 0`. -/
private lemma sum_mul_addChar {χ : MulChar K ℂ} (hchi : χ ≠ 1) (ψ : AddChar K ℂ) (c : K) :
    ∑ x : K, χ x * ψ (c * x) = χ⁻¹ c * gaussSum χ ψ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul, AddChar.map_zero_eq_one, mul_one, MulChar.sum_eq_zero_of_ne_one hchi,
      MulChar.map_zero, zero_mul]
  · have h := gaussSum_mulShift χ ψ (Units.mk0 c hc)
    have h2 : gaussSum χ (AddChar.mulShift ψ (Units.mk0 c hc))
        = ∑ x : K, χ x * ψ (c * x) := by
      simp [gaussSum, AddChar.mulShift_apply]
    rw [h2] at h
    simp only [Units.val_mk0] at h
    have hcc : χ c⁻¹ * χ c = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, MulChar.map_one]
    calc ∑ x : K, χ x * ψ (c * x)
        = χ c⁻¹ * χ c * ∑ x : K, χ x * ψ (c * x) := by rw [hcc, one_mul]
      _ = χ c⁻¹ * gaussSum χ ψ := by rw [mul_assoc, h]
      _ = χ⁻¹ c * gaussSum χ ψ := by rw [MulChar.inv_apply']

omit [DecidableEq K] [CharP K 2] in
/-- A character killed by a power of two is trivial. -/
private lemma eq_one_of_pow_two_pow {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) (hk : k ≤ n)
    {χ : MulChar K ℂ} (h : χ ^ (2 ^ k) = 1) : χ = 1 := by
  refine MulChar.ext fun u => ?_
  set x : K := (u : K) with hxdef
  have hx : x ≠ 0 := u.ne_zero
  have hu : IsUnit x := isUnit_iff_ne_zero.2 hx
  have hy : (x ^ (2 ^ (n - k))) ^ (2 ^ k) = x := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hk]
    exact pow_card_two_pow hcard x
  have hyne : x ^ (2 ^ (n - k)) ≠ 0 := pow_ne_zero _ hx
  have hstep : χ x = (χ ^ (2 ^ k)) (x ^ (2 ^ (n - k))) := by
    rw [MulChar.pow_apply' χ (by positivity), ← map_pow, hy]
  rw [hstep, h, MulChar.one_apply (isUnit_iff_ne_zero.2 hyne), MulChar.one_apply hu]

end Characters

/-! ### The adjoint of `T_k` for the trace pairing -/

section Adjoint

/-- The adjoint `T*` of `T_k` for the trace pairing. -/
private def adjSum (n k : ℕ) (a : K) : K :=
  ∑ i ∈ Finset.range k, a ^ (2 ^ (n - i))

omit [Fintype K] [DecidableEq K] [CharP K 2] in
/-- One further term of the adjoint sum. -/
private lemma adjSum_succ (n k : ℕ) (a : K) :
    adjSum n (k + 1) a = adjSum n k a + a ^ (2 ^ (n - k)) := by
  simp [adjSum, Finset.sum_range_succ]

omit [Fintype K] [DecidableEq K] [CharP K 2] in
/-- An additive character invariant under squaring is invariant under every
`2 ^ m`-power. -/
private lemma addChar_pow_two_pow {ψ : AddChar K ℂ} (hpsi_sq : ∀ x : K, ψ (x ^ 2) = ψ x)
    (m : ℕ) (x : K) : ψ (x ^ (2 ^ m)) = ψ x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : x ^ (2 ^ (m + 1)) = (x ^ (2 ^ m)) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [this, hpsi_sq, ih]

omit [DecidableEq K] [CharP K 2] in
/-- Moving a `2 ^ i`-power across the pairing:
`ψ (a * s ^ (2 ^ i)) = ψ (a ^ (2 ^ (n - i)) * s)`. -/
private lemma addChar_mul_frob {n : ℕ} (hcard : Fintype.card K = 2 ^ n) {ψ : AddChar K ℂ}
    (hpsi_sq : ∀ x : K, ψ (x ^ 2) = ψ x) {i : ℕ} (hi : i ≤ n) (a s : K) :
    ψ (a * s ^ (2 ^ i)) = ψ (a ^ (2 ^ (n - i)) * s) := by
  have h := addChar_pow_two_pow hpsi_sq i (a ^ (2 ^ (n - i)) * s)
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hi, pow_card_two_pow hcard] at h
  exact h

omit [DecidableEq K] [CharP K 2] in
/-- `adjSum` is the adjoint of `frobSum` through `ψ`:
`ψ (a * T_k s) = ψ (T*_k a * s)`. -/
private lemma addChar_adjSum {n : ℕ} (hcard : Fintype.card K = 2 ^ n) {ψ : AddChar K ℂ}
    (hpsi_sq : ∀ x : K, ψ (x ^ 2) = ψ x) :
    ∀ (k : ℕ), k ≤ n → ∀ a s : K, ψ (a * frobSum k s) = ψ (adjSum n k a * s) := by
  intro k
  induction k with
  | zero => intro _ a s; simp [frobSum, adjSum]
  | succ k ih =>
    intro hk a s
    rw [frobSum_succ, mul_add, AddChar.map_add_eq_mul, ih (by omega) a s,
      addChar_mul_frob hcard hpsi_sq (by omega) a s, adjSum_succ, add_mul, AddChar.map_add_eq_mul]

omit [DecidableEq K] in
/-- `(T*_k a) ^ (2 ^ k) = T_k(a) ^ 2`. -/
private lemma adjSum_pow {n : ℕ} (hcard : Fintype.card K = 2 ^ n) {k : ℕ} (hk : k ≤ n) (a : K) :
    adjSum n k a ^ (2 ^ k) = frobSum k a ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [adjSum, sum_pow_char_pow, frobSum_sq]
  rw [← Finset.sum_range_reflect (fun i => a ^ (2 ^ (i + 1))) k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← pow_mul, ← pow_add]
  have h1 : n - i + k = n + (k - i) := by omega
  have h2 : k - 1 - i + 1 = k - i := by omega
  rw [h1, h2, pow_two_pow_add_card hcard]

omit [DecidableEq K] in
/-- For odd `k`, `(1 + T*_k a) ^ (2 ^ k) = T_k(1 + a) ^ 2`. -/
private lemma adjSum_one_add_pow {n : ℕ} (hcard : Fintype.card K = 2 ^ n) {k : ℕ} (hkn : k ≤ n)
    (hk : Odd k) (a : K) :
    (1 + adjSum n k a) ^ (2 ^ k) = frobSum k (1 + a) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [add_pow_char_pow, one_pow, adjSum_pow hcard hkn, frobSum_add, frobSum_one hk,
    add_pow_char, one_pow]

end Adjoint

/-! ### Factorisation of `χ ∘ M_k` -/

section Factor

omit [Fintype K] [DecidableEq K] [CharP K 2] in
/-- `χ ∘ M_k` factors as `χ^(2^k+1)` evaluated at `T_k s` times `χ⁻¹^(2^k)`
evaluated at `s`. -/
private lemma mulChar_mcmMap (k : ℕ) (χ : MulChar K ℂ) (s : K) :
    χ (mcmMap k s) = (χ ^ (2 ^ k + 1)) (frobSum k s) * ((χ⁻¹) ^ (2 ^ k)) s := by
  have hne : (2 : ℕ) ^ k + 1 ≠ 0 := by positivity
  have hne' : (2 : ℕ) ^ k ≠ 0 := by positivity
  rw [MulChar.pow_apply' _ hne, MulChar.pow_apply' _ hne', MulChar.inv_apply']
  rw [mcmMap, div_eq_mul_inv, map_mul, map_pow, ← inv_pow, ← map_pow]
  congr 1
  rw [← map_pow, inv_pow]

end Factor

/-! ### Fourier/adjoint and Dickson bridges -/

omit [DecidableEq K] [CharP K 2] in
/-- Fourier inversion and the adjoint of `T_k` convert the untwisted MCM sum
into an adjoint character sum. -/
private lemma mcmCharSum_mul_gauss_eq_adjoint_sum
    {n k : ℕ} (hklt : k < n) (hcard : Fintype.card K = 2 ^ n)
    (ψ : AddChar K ℂ) (hpsi_sq : ∀ x : K, ψ (x ^ 2) = ψ x)
    (χ E F : MulChar K ℂ)
    (_hE : E = (χ⁻¹) ^ (2 ^ k + 1)) (hF : F = (χ⁻¹) ^ (2 ^ k))
    (hEne : E ≠ 1) (hFne : F ≠ 1) (hEinv : E⁻¹ = χ ^ (2 ^ k + 1)) :
    mcmCharSum k χ * gaussSum E ψ
      = ∑ a : K, E a * (F⁻¹ (adjSum n k a) * gaussSum F ψ) := by
  have hpointwise : ∀ s : K, χ (mcmMap k s) * gaussSum E ψ
      = ∑ a : K, E a * ψ (frobSum k s * a) * F s := by
    intro s
    rw [← Finset.sum_mul, sum_mul_addChar hEne ψ (frobSum k s), hEinv,
      mulChar_mcmMap k χ s, ← hF]
    ring
  have hexpand : mcmCharSum k χ * gaussSum E ψ
      = ∑ s : K, ∑ a : K, E a * ψ (frobSum k s * a) * F s := by
    rw [mcmCharSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => hpointwise s
  rw [hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sum_mul_addChar hFne ψ (adjSum n k a), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm (frobSum k s) a, addChar_adjSum hcard hpsi_sq k hklt.le a s]
  ring

omit [DecidableEq K] in
/-- Inversion reindexing and the sparse `D_(2^k-1)` identity evaluate the
untwisted adjoint character sum. -/
private lemma adjoint_sum_eq_gauss_mul_dickson_pred
    {n k : ℕ} (hklt : k < n) (hcard : Fintype.card K = 2 ^ n)
    (ψ : AddChar K ℂ) (χ E F : MulChar K ℂ)
    (hE : E = (χ⁻¹) ^ (2 ^ k + 1)) (hFinv : F⁻¹ = χ ^ (2 ^ k)) :
    (∑ a : K, E a * (F⁻¹ (adjSum n k a) * gaussSum F ψ))
      = gaussSum F ψ * ∑ b : K, χ ((dickson 1 1 (2 ^ k - 1)).eval b) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (fun x : K => x⁻¹) inv_involutive.bijective _ _ (fun a => ?_)
  rcases eq_or_ne a 0 with rfl | ha
  · rw [hE, MulChar.pow_apply' _ (by positivity), MulChar.map_zero,
      zero_pow (by positivity), zero_mul]
    simp only [inv_zero, dickson_eval_zero, MulChar.map_zero, mul_zero]
  · have hEa : E a = χ ((a⁻¹) ^ (2 ^ k + 1)) := by
      rw [hE, MulChar.pow_apply' _ (by positivity), MulChar.inv_apply', ← map_pow]
    have hFa : F⁻¹ (adjSum n k a) = χ (frobSum k a ^ 2) := by
      rw [hFinv, MulChar.pow_apply' _ (by positivity), ← map_pow, adjSum_pow hcard hklt.le]
    have hsp := sparse_dickson_pred k a⁻¹ (inv_ne_zero ha)
    rw [inv_inv] at hsp
    rw [hEa, hFa, ← mul_assoc, ← map_mul, hsp]
    ring

omit [DecidableEq K] [CharP K 2] in
/-- Fourier inversion and the adjoint of `T_k` convert the additively twisted
MCM sum into the shifted adjoint character sum. -/
private lemma mcmTwistedCharSum_mul_gauss_eq_adjoint_sum
    {n k : ℕ} (hklt : k < n) (hcard : Fintype.card K = 2 ^ n)
    (ψ : AddChar K ℂ) (hpsi_sq : ∀ x : K, ψ (x ^ 2) = ψ x)
    (χ E F : MulChar K ℂ)
    (_hE : E = (χ⁻¹) ^ (2 ^ k + 1)) (hF : F = (χ⁻¹) ^ (2 ^ k))
    (hEne : E ≠ 1) (hFne : F ≠ 1) (hEinv : E⁻¹ = χ ^ (2 ^ k + 1)) :
    mcmTwistedCharSum k ψ χ * gaussSum E ψ
      = ∑ a : K, E a * (F⁻¹ (1 + adjSum n k a) * gaussSum F ψ) := by
  have hpointwise : ∀ s : K, ψ s * χ (mcmMap k s) * gaussSum E ψ
      = ∑ a : K, E a * ψ (frobSum k s * a) * (ψ s * F s) := by
    intro s
    rw [← Finset.sum_mul, sum_mul_addChar hEne ψ (frobSum k s), hEinv,
      mulChar_mcmMap k χ s, ← hF]
    ring
  have hexpand : mcmTwistedCharSum k ψ χ * gaussSum E ψ
      = ∑ s : K, ∑ a : K, E a * ψ (frobSum k s * a) * (ψ s * F s) := by
    rw [mcmTwistedCharSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => hpointwise s
  rw [hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sum_mul_addChar hFne ψ (1 + adjSum n k a), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm (frobSum k s) a, addChar_adjSum hcard hpsi_sq k hklt.le a s, add_mul, one_mul,
    AddChar.map_add_eq_mul]
  ring

omit [DecidableEq K] in
/-- Inversion reindexing and the sparse `D_(2^k+1)` identity evaluate the
twisted adjoint character sum. -/
private lemma twisted_adjoint_sum_eq_gauss_mul_dickson_succ
    {n k : ℕ} (hklt : k < n) (hcard : Fintype.card K = 2 ^ n) (hk : Odd k)
    (ψ : AddChar K ℂ) (χ E F : MulChar K ℂ)
    (hE : E = (χ⁻¹) ^ (2 ^ k + 1)) (hFinv : F⁻¹ = χ ^ (2 ^ k)) :
    (∑ a : K, E a * (F⁻¹ (1 + adjSum n k a) * gaussSum F ψ))
      = gaussSum F ψ * ∑ b : K, χ ((dickson 1 1 (2 ^ k + 1)).eval b) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (fun x : K => x⁻¹) inv_involutive.bijective _ _ (fun a => ?_)
  rcases eq_or_ne a 0 with rfl | ha
  · rw [hE, MulChar.pow_apply' _ (by positivity), MulChar.map_zero,
      zero_pow (by positivity), zero_mul]
    simp only [inv_zero, dickson_eval_zero, MulChar.map_zero, mul_zero]
  · have hEa : E a = χ ((a⁻¹) ^ (2 ^ k + 1)) := by
      rw [hE, MulChar.pow_apply' _ (by positivity), MulChar.inv_apply', ← map_pow]
    have hFa : F⁻¹ (1 + adjSum n k a) = χ (frobSum k (1 + a) ^ 2) := by
      rw [hFinv, MulChar.pow_apply' _ (by positivity), ← map_pow,
        adjSum_one_add_pow hcard hklt.le hk]
    have hsp := sparse_dickson_succ hk a⁻¹ (inv_ne_zero ha)
    rw [inv_inv] at hsp
    rw [hEa, hFa, ← mul_assoc, ← map_mul, hsp]
    ring

omit [DecidableEq K] in
/-- The untwisted MCM character sum as a Gauss-sum ratio against a sparse
Dickson character sum. -/
theorem mcmCharSum_eq_dickson
    {n k : ℕ} (hklt : k < n) (hcard : Fintype.card K = 2 ^ n)
    (ψ : AddChar K ℂ) (hpsi : ψ.IsPrimitive)
    (hpsi_sq : ∀ x : K, ψ (x ^ 2) = ψ x)
    (χ : MulChar K ℂ) (hchie : χ ^ (2 ^ k + 1) ≠ 1) :
    mcmCharSum k χ
      = (gaussSum ((χ⁻¹) ^ (2 ^ k)) ψ /
          gaussSum ((χ⁻¹) ^ (2 ^ k + 1)) ψ)
        * (∑ b : K, χ ((dickson 1 1 (2 ^ k - 1)).eval b)) := by
  have hcardC : ((Fintype.card K : ℕ) : ℂ) ≠ 0 := by
    rw [hcard]
    exact_mod_cast pow_ne_zero n (two_ne_zero' ℕ)
  have hEne : ((χ⁻¹) ^ (2 ^ k + 1)) ≠ 1 := by
    intro h
    refine hchie ?_
    rw [inv_pow] at h
    simpa using congrArg Inv.inv h
  have hFne : ((χ⁻¹) ^ (2 ^ k)) ≠ 1 := by
    intro h
    refine hchie ?_
    have hi : χ⁻¹ = 1 := eq_one_of_pow_two_pow hcard hklt.le h
    have : χ = 1 := by simpa using congrArg Inv.inv hi
    rw [this, one_pow]
  set E : MulChar K ℂ := (χ⁻¹) ^ (2 ^ k + 1) with hE
  set F : MulChar K ℂ := (χ⁻¹) ^ (2 ^ k) with hF
  have hEinv : E⁻¹ = χ ^ (2 ^ k + 1) := by rw [hE, ← inv_pow, inv_inv]
  have hFinv : F⁻¹ = χ ^ (2 ^ k) := by rw [hF, ← inv_pow, inv_inv]
  have hG1 : gaussSum E ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcardC hEne hpsi
  have hFourier := mcmCharSum_mul_gauss_eq_adjoint_sum
    hklt hcard ψ hpsi_sq χ E F hE hF hEne hFne hEinv
  have hDickson := adjoint_sum_eq_gauss_mul_dickson_pred
    hklt hcard ψ χ E F hE hFinv
  rw [hDickson] at hFourier
  rw [div_mul_eq_mul_div, eq_div_iff hG1]
  exact hFourier

omit [DecidableEq K] in
/-- The additively twisted MCM character sum as a Gauss-sum ratio against a
sparse Dickson character sum. -/
theorem mcmTwistedCharSum_eq_dickson
    {n k : ℕ} (hklt : k < n)
    (hcard : Fintype.card K = 2 ^ n) (hk : Odd k)
    (ψ : AddChar K ℂ) (hpsi : ψ.IsPrimitive)
    (hpsi_sq : ∀ x : K, ψ (x ^ 2) = ψ x)
    (χ : MulChar K ℂ) (hchie : χ ^ (2 ^ k + 1) ≠ 1) :
    mcmTwistedCharSum k ψ χ
      = (gaussSum ((χ⁻¹) ^ (2 ^ k)) ψ /
          gaussSum ((χ⁻¹) ^ (2 ^ k + 1)) ψ)
        * (∑ b : K, χ ((dickson 1 1 (2 ^ k + 1)).eval b)) := by
  have hcardC : ((Fintype.card K : ℕ) : ℂ) ≠ 0 := by
    rw [hcard]
    exact_mod_cast pow_ne_zero n (two_ne_zero' ℕ)
  have hEne : ((χ⁻¹) ^ (2 ^ k + 1)) ≠ 1 := by
    intro h
    refine hchie ?_
    rw [inv_pow] at h
    simpa using congrArg Inv.inv h
  have hFne : ((χ⁻¹) ^ (2 ^ k)) ≠ 1 := by
    intro h
    refine hchie ?_
    have hi : χ⁻¹ = 1 := eq_one_of_pow_two_pow hcard hklt.le h
    have : χ = 1 := by simpa using congrArg Inv.inv hi
    rw [this, one_pow]
  set E : MulChar K ℂ := (χ⁻¹) ^ (2 ^ k + 1) with hE
  set F : MulChar K ℂ := (χ⁻¹) ^ (2 ^ k) with hF
  have hEinv : E⁻¹ = χ ^ (2 ^ k + 1) := by rw [hE, ← inv_pow, inv_inv]
  have hFinv : F⁻¹ = χ ^ (2 ^ k) := by rw [hF, ← inv_pow, inv_inv]
  have hG1 : gaussSum E ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcardC hEne hpsi
  have hFourier := mcmTwistedCharSum_mul_gauss_eq_adjoint_sum
    hklt hcard ψ hpsi_sq χ E F hE hF hEne hFne hEinv
  have hDickson := twisted_adjoint_sum_eq_gauss_mul_dickson_succ
    hklt hcard hk ψ χ E F hE hFinv
  rw [hDickson] at hFourier
  rw [div_mul_eq_mul_div, eq_div_iff hG1]
  exact hFourier

omit [DecidableEq K] in
/-- Cubic exceptional case: if `χ^3=1` and `χ` is nonprincipal,
then for odd `k` the MCM map is invisible to `χ`: `χ(M_k(s))=χ(s)`. -/
theorem cubic_mcm_apply
    {n k : ℕ} (hcard : Fintype.card K = 2 ^ n) (hk : Odd k) (hkn : Nat.Coprime k n)
    (χ : MulChar K ℂ) (hchi3 : χ ^ 3 = 1) :
    ∀ s : K, χ (mcmMap k s) = χ s := by
  obtain ⟨c, hc⟩ : (3 : ℕ) ∣ 2 ^ k + 1 := by
    have h : ((2 ^ k + 1 : ℕ) : ZMod 3) = 0 := by
      push_cast
      have h2 : (2 : ZMod 3) = -1 := by decide
      rw [h2, hk.neg_one_pow]
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).1 h
  have he : χ ^ (2 ^ k + 1) = 1 := by rw [hc, pow_mul, hchi3, one_pow]
  have hr : (χ⁻¹) ^ (2 ^ k) = χ := by
    have h1 : (χ⁻¹) ^ (2 ^ k) * χ⁻¹ = 1 := by
      rw [← pow_succ, hc, pow_mul, inv_pow, hchi3, inv_one, one_pow]
    rw [mul_eq_one_iff_eq_inv.1 h1, inv_inv]
  intro s
  rw [mulChar_mcmMap k χ s, he, hr]
  rcases eq_or_ne s 0 with rfl | hs
  · rw [MulChar.map_zero, mul_zero]
  · rw [MulChar.one_apply
      (isUnit_iff_ne_zero.2 (frobSum_ne_zero_of_odd hcard hk hkn hs)), one_mul]

end KasamiCyclicAdditive
