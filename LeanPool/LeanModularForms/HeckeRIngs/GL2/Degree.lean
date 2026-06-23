/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GL2.MultiplicationTable

/-!
# Degree formulas for GL₂ Hecke operators

Shimura Theorem 3.24, identities 6 and 7: degree formulas for the GL₂ Hecke algebra.

## Main results

* `deg_T_diag_ppow` — `deg(T(pⁱ, p^{i+k})) = p^{k−1}(p+1)` for k > 0
* `deg_T_diag_scalar` — `deg(T(c,c)) = 1`
* `deg_T_sum_prime_pow` — `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ`
* `deg_T_sum` — `deg(T(m)) = σ₁(m)`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Theorem 3.24
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2
open scoped ArithmeticFunction.sigma

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

/-! ### Identity 6: Degree formulas (wrapping existing results) -/

include hp in
/-- Theorem 3.24(6): `deg(T(pⁱ, p^{i+k})) = p^{k-1}(p+1)` for k > 0. -/
theorem deg_T_diag_ppow (i k : ℕ) (hk : 0 < k) :
    HeckeCosetDeg (GLPair 2) (TDiag (![p ^ i, p ^ (i + k)])) =
    ↑(p ^ (k - 1) * (p + 1)) :=
  HeckeCoset_deg_T_diag_two_prime p hp (![p ^ i, p ^ (i + k)])
    (fun j => by fin_cases j <;> exact pow_pos hp.pos _)
    (fun j hj => by
      have hi0 : j = 0 := by omega
      subst hi0; simpa using Nat.pow_dvd_pow p (by omega : i ≤ i + k))
    k hk (by
    change p ^ (i + k) / p ^ i = p ^ k
    rw [Nat.pow_div (by omega) hp.pos]; congr 1; omega)

/-- Scalar case: `deg(T(c, c)) = 1`. -/
theorem deg_T_diag_scalar (c : ℕ) (hc : 0 < c) :
    HeckeCosetDeg (GLPair 2) (TDiag (fun _ => c)) = 1 :=
  HeckeCoset_deg_T_diag_two_scalar (fun _ => c) (fun _ => hc) (divChain_const 2 c) rfl

/-! ### Identity 7: Degree of T(m) -/

/-- `deg` of `TAd` when conditions hold. -/
private lemma deg_T_ad_of_pos' (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (hdvd : a ∣ d) :
    deg (GLPair 2) (TAd a d) =
    HeckeCosetDeg (GLPair 2) (TDiag ![a, d]) := by
  unfold deg; rw [T_ad_of_pos a d ha hd hdvd]
  unfold TElem; simp

include hp in
/-- Non-scalar case: `deg(TAd(pⁱ, p^{k-i})) = p^{k-2i-1}(p+1)` when `2i < k`. -/
private lemma deg_ppow_term_lt' (i k : ℕ) (h2i : 2 * i < k) :
    deg (GLPair 2) (TAd (p ^ i) (p ^ (k - i))) =
    ↑(p ^ (k - 2 * i - 1) * (p + 1)) := by
  rw [deg_T_ad_of_pos' (p ^ i) (p ^ (k - i))
    (pow_pos hp.pos i) (pow_pos hp.pos (k - i)) (Nat.pow_dvd_pow p (by omega))]
  rw [show TDiag (![p ^ i, p ^ (k - i)]) =
      TDiag (![p ^ i, p ^ (i + (k - 2 * i))]) from by
    congr 1; ext j; fin_cases j <;> simp only [show k - i = i + (k - 2 * i) from by omega]]
  exact deg_T_diag_ppow p hp i (k - 2 * i) (by omega)

include hp in
/-- Scalar case: `deg(TAd(p^i, p^i)) = 1` when `2i = k`. -/
private lemma deg_ppow_term_eq' (i k : ℕ) (h2i : 2 * i = k) :
    deg (GLPair 2) (TAd (p ^ i) (p ^ (k - i))) = 1 := by
  rw [show k - i = i from by omega,
    deg_T_ad_of_pos' (p ^ i) (p ^ i) (pow_pos hp.pos i) (pow_pos hp.pos i) (dvd_refl _),
    show TDiag (![p ^ i, p ^ i]) = TDiag (fun _ => p ^ i) from by
      congr 1; exact funext fun j => by fin_cases j <;> rfl]
  exact deg_T_diag_scalar (p ^ i) (pow_pos hp.pos i)

include hp in
/-- For i in the shifted tail, degree of the (k+2)-expansion term equals the k-expansion term.
    Key fact: both have the same "gap" (ratio d/a), so their degrees coincide. -/
private lemma deg_ppow_shift' (i k : ℕ) (hi : i < k / 2 + 1) :
    deg (GLPair 2) (TAd (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
    deg (GLPair 2) (TAd (p ^ i) (p ^ (k - i))) := by
  by_cases h2i : 2 * i < k
  · rw [deg_ppow_term_lt' p hp (i + 1) (k + 2) (by omega),
      show k + 2 - 2 * (i + 1) - 1 = k - 2 * i - 1 from by omega,
      (deg_ppow_term_lt' p hp i k h2i).symm]
  · rw [deg_ppow_term_eq' p hp (i + 1) (k + 2) (by omega),
      deg_ppow_term_eq' p hp i k (by omega)]

/-- `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ`.
    Proof by strong induction: for k >= 2, split the expansion at i=0 to get
    `deg = p^{k-1}(p+1) + deg_tail`, where the tail's degree equals `deg(TSum(p^{k-2}))`
    by a shift argument (the degree of `TAd(p^{i+1}, p^{k-i-1})` equals that of
    `TAd(p^i, p^{k-2-i})` since both have the same diagonal ratio). -/
theorem deg_T_sum_prime_pow (k : ℕ) :
    deg (GLPair 2) (TSum ⟨p ^ k, pow_pos hp.pos k⟩) =
    ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
  rw [T_sum_ppow_expansion p hp k, map_sum]
  match k with
  | 0 =>
    simp only [Nat.zero_div, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    exact deg_ppow_term_eq' p hp 0 0 rfl
  | 1 =>
    simp only [show (1 : ℕ) / 2 = 0 from rfl, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    convert deg_ppow_term_lt' p hp 0 1 (by omega) using 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    push_cast; ring
  | k + 2 =>
    have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
    rw [hdiv, Finset.sum_range_succ']
    have h_tail : ∑ i ∈ Finset.range (k / 2 + 1),
        (deg (GLPair 2)) (TAd (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
        ∑ i ∈ Finset.range (k / 2 + 1), (deg (GLPair 2)) (TAd (p ^ i) (p ^ (k - i))) :=
      Finset.sum_congr rfl fun i hi => by
        rw [Finset.mem_range] at hi; exact deg_ppow_shift' p hp i k hi
    rw [h_tail, show deg (GLPair 2) (TAd (p ^ 0) (p ^ (k + 2 - 0))) =
        ↑(p ^ (k + 1) * (p + 1)) from by
      simpa [show k + 2 - 0 - 1 = k + 1 from by omega] using
        deg_ppow_term_lt' p hp 0 (k + 2) (by omega)]
    have ih_k := ih k (by omega)
    rw [T_sum_ppow_expansion p hp k, map_sum] at ih_k; rw [ih_k]
    conv_rhs =>
      rw [show k + 2 + 1 = (k + 1 + 1) + 1 from by omega,
        Finset.sum_range_succ,
        show k + 1 + 1 = (k + 1) + 1 from by omega,
        Finset.sum_range_succ]
    push_cast; ring
/-- `deg(TSum(1)) = 1`, used as base case for deg_T_sum. -/
private lemma deg_T_sum_one : deg (GLPair 2) (TSum 1) = 1 := by
  change deg (GLPair 2) (∑ a ∈ Nat.divisors 1, TAd a (1 / a)) = 1
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  rw [deg_T_ad_of_pos' 1 1 one_pos one_pos (dvd_refl 1),
    show TDiag (![1, 1] : Fin 2 → ℕ) = TDiag (fun _ => 1) from by
      congr 1; exact funext fun j => by fin_cases j <;> rfl]
  exact deg_T_diag_scalar 1 Nat.one_pos

/-- Theorem 3.24(7): `deg(T(m)) = σ₁(m)`.
    By prime factorization + coprime multiplicativity + prime-power case. -/
theorem deg_T_sum (m : ℕ+) :
    deg (GLPair 2) (TSum m) = (σ 1) (m : ℕ) := by
  obtain ⟨n, hn⟩ := m
  revert hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one =>
    intro hn
    rw [show (⟨1, hn⟩ : ℕ+) = (1 : ℕ+) from rfl, deg_T_sum_one]
    simp
  | @prime_pow p k hp hk =>
    intro hn
    rw [deg_T_sum_prime_pow p hp k]; simp only [ArithmeticFunction.sigma_one_apply]
    have h := @Nat.sum_divisors_prime_pow ℕ _ k p id hp; simp only [id] at h
    exact_mod_cast h.symm
  | @coprime a b ha hb hcop iha ihb =>
    intro hn
    rw [show TSum ⟨a * b, hn⟩ = TSum ⟨a, by omega⟩ * TSum ⟨b, by omega⟩ from
      (T_sum_mul_coprime ⟨a, by omega⟩ ⟨b, by omega⟩ hcop).symm,
      map_mul, iha (by omega), ihb (by omega)]
    simp only [ArithmeticFunction.sigma_one_apply]
    exact_mod_cast (Nat.Coprime.sum_divisors_mul hcop).symm

end HeckeRing.GL2
