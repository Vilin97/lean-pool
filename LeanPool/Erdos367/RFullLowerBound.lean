/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Aesop

/-!
# Erdős #367: r-full part and the odd-r extension

For a positive integer m with prime factorization m = ∏ p^{a_p}, and r ≥ 1,
the r-full part is B_r(m) = ∏_{p : a_p ≥ r} p^{a_p}.

Main theorem: for odd r ≥ 1 and q ≥ 2, with n = (q^r - 1)^r,
  (i)   B_r(n) = n,
  (ii)  q^r ∣ n + 1,
  (iii) B_r(n) · B_r(n+1) ≥ n · q^r,
  (iv)  (B_r(n) · B_r(n+1))^r > n^{r+1}.
-/

namespace RFullOdd

open Finset Finsupp Nat

/-! ## Definition of the r-full part -/

/-- The r-full part of m: the product of prime-power components p^{a_p} of m
    for which the exponent a_p ≥ r. -/
noncomputable def rFullPart (r m : ℕ) : ℕ :=
  (m.factorization.filter (fun p => r ≤ m.factorization p)).prod (fun p v => p ^ v)

/-! ## Factorization of rFullPart -/

/-
The factorization of rFullPart r m equals the filtered factorization of m.
-/
lemma rFullPart_factorization (r m : ℕ) (_hm : m ≠ 0) :
    (rFullPart r m).factorization =
      m.factorization.filter (fun p => r ≤ m.factorization p) := by
  unfold rFullPart
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  have hp_support : p ∈ m.factorization.support := by
    rw [Finsupp.support_filter] at hp
    exact Finset.mem_of_mem_filter p hp
  exact Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp_support)

/-
rFullPart r m is nonzero when m is nonzero.
-/
lemma rFullPart_pos (r m : ℕ) (_hm : m ≠ 0) : 0 < rFullPart r m := by
  exact Finset.prod_pos fun p hp =>
    pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp |>.1)) _

/-! ## Key properties of rFullPart -/

/-
B_r(m) divides m.
-/
lemma rFullPart_dvd (r m : ℕ) (hm : m ≠ 0) : rFullPart r m ∣ m := by
  have h_factorization :
      rFullPart r m =
        ∏ p ∈ Nat.primeFactors m,
          p ^ (if r ≤ m.factorization p then m.factorization p else 0) := by
    unfold rFullPart
    simpa [Finsupp.prod, Finset.prod_ite] using
      (Finset.prod_congr rfl fun x hx => by
        rw [Finsupp.filter_apply]
        aesop)
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  exact h_factorization.symm ▸
    Finset.prod_dvd_prod_of_dvd _ _ fun p hp => by
      split_ifs <;> simp +decide [*]

/-
L1: A perfect r-th power is r-full: B_r(m^r) = m^r for m ≥ 1 and r ≥ 1.
-/
lemma rFullPart_pow (r m : ℕ) (hm : m ≠ 0) (hr : r ≠ 0) :
    rFullPart r (m ^ r) = m ^ r := by
  apply Nat.factorization_inj
  · exact Nat.ne_of_gt ( rFullPart_pos _ _ ( pow_ne_zero _ hm ) );
  · aesop;
  · ext p
    by_cases hp : p.Prime
    · rw [rFullPart_factorization _ _ (pow_ne_zero _ hm)]
      by_cases h : r ≤ r * m.factorization p
      · simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
          smul_eq_mul, Finsupp.filter_smul, mul_eq_mul_left_iff,
          Finsupp.filter_apply, h]
        left
        rfl
      · simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
          smul_eq_mul, Finsupp.filter_smul, mul_eq_mul_left_iff,
          Finsupp.filter_apply, h]
        left
        cases hv : m.factorization p with
        | zero => rfl
        | succ v =>
            exfalso
            apply h
            rw [hv]
            exact Nat.le_mul_of_pos_right r (Nat.succ_pos v)
    · simp_all +decide [rFullPart_factorization]

/-
If d^r ∣ m and m ≠ 0, then d^r ∣ B_r(m).
-/
lemma pow_dvd_rFullPart (r m d : ℕ) (hm : m ≠ 0) (hdvd : d ^ r ∣ m) :
    d ^ r ∣ rFullPart r m := by
  by_cases hr : r = 0
  · simp [hr]
  rw [ ← Nat.factorization_le_iff_dvd ];
  · intro p
    have := Nat.factorization_le_iff_dvd
      (show d ^ r ≠ 0 from by aesop)
      (show m ≠ 0 from hm) |>.2 hdvd
    simp_all +decide [Finsupp.le_def]
    by_cases h : r ≤ m.factorization p <;> simp_all +decide [ rFullPart_factorization ];
    nlinarith [ this p ];
  · aesop;
  · exact Nat.ne_of_gt ( rFullPart_pos r m hm )

/-- If d^r ∣ m and m ≠ 0, then d^r ≤ B_r(m). -/
lemma pow_le_rFullPart (r m d : ℕ) (hm : m ≠ 0) (hdvd : d ^ r ∣ m) :
    d ^ r ≤ rFullPart r m :=
  Nat.le_of_dvd (rFullPart_pos r m hm) (pow_dvd_rFullPart r m d hm hdvd)

/-! ## L2: Odd-power divisibility -/

/-
For odd r and a ≥ 1, (a + 1) ∣ (a^r + 1).
    Proof: a ≡ -1 (mod a+1), so a^r ≡ (-1)^r = -1 (mod a+1).
-/
lemma odd_pow_add_one_dvd (r a : ℕ) (hr : Odd r) :
    (a + 1) ∣ (a ^ r + 1) := by
  simpa using hr.nat_add_dvd_pow_add_pow a 1

/-! ## Main theorem: the odd-r case -/

variable {r q : ℕ}

/-- (i) B_r(n) = n where n = (q^r - 1)^r. -/
theorem erdos367_i (hr : 0 < r) (hq : 2 ≤ q) :
    rFullPart r ((q ^ r - 1) ^ r) = (q ^ r - 1) ^ r := by
  apply rFullPart_pow
  · have : 2 ≤ q ^ r := le_trans hq (Nat.le_self_pow hr.ne' q)
    omega
  · exact hr.ne'

/-
(ii) q^r ∣ (q^r - 1)^r + 1.
-/
theorem erdos367_ii (hr : Odd r) (hq : 2 ≤ q) :
    q ^ r ∣ (q ^ r - 1) ^ r + 1 := by
  convert odd_pow_add_one_dvd r ( q ^ r - 1 ) hr using 1;
  rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by linarith ) ) ]

/-- B_r(n+1) ≥ q^r. -/
theorem erdos367_Br_succ_ge (hr_odd : Odd r) (_hr : 0 < r) (hq : 2 ≤ q) :
    q ^ r ≤ rFullPart r ((q ^ r - 1) ^ r + 1) := by
  apply pow_le_rFullPart r _ q
  · positivity
  · exact erdos367_ii hr_odd hq

/-- (iii) B_r(n) · B_r(n+1) ≥ n · q^r. -/
theorem erdos367_iii (hr_odd : Odd r) (hr : 0 < r) (hq : 2 ≤ q) :
    (q ^ r - 1) ^ r * q ^ r ≤
      rFullPart r ((q ^ r - 1) ^ r) * rFullPart r ((q ^ r - 1) ^ r + 1) := by
  rw [erdos367_i hr hq]
  exact Nat.mul_le_mul_left _ (erdos367_Br_succ_ge hr_odd hr hq)

/-
(iv) (B_r(n) · B_r(n+1))^r > n^(r+1).
-/
theorem erdos367_iv (hr_odd : Odd r) (hr : 0 < r) (hq : 2 ≤ q) :
    ((q ^ r - 1) ^ r) ^ (r + 1) <
      (rFullPart r ((q ^ r - 1) ^ r) * rFullPart r ((q ^ r - 1) ^ r + 1)) ^ r := by
  refine lt_of_lt_of_le ?_ (Nat.pow_le_pow_left (erdos367_iii hr_odd hr hq) r)
  rw [mul_pow, pow_succ]
  gcongr
  · exact pow_pos
      (pow_pos (Nat.sub_pos_of_lt (one_lt_pow₀ (by linarith) (by linarith))) _)
      _
  · exact Nat.sub_lt (by positivity) (by positivity)

/-! ## Axiom verification -/

end RFullOdd
