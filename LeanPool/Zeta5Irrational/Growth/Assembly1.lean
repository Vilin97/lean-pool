/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.PrimeSum
public import LeanPool.Zeta5Irrational.Norm
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Growth: decomposition of `log m_K` and the small primes
-/

public section

open Finset Filter

namespace Zeta5Irrational

/-- `log m_K = ∑_{k ≤ 2h} c(k) (-L_k)`. -/
lemma log_mN (n : ℕ) :
    Real.log (mN n : ℝ) = ∑ k ∈ Icc 1 (2 * (37 * n)), cPrime k * (-(Lp n k : ℝ)) := by
  unfold mN
  push_cast
  rw [Real.log_prod
      (fun p hp => by
        have := (Finset.mem_filter.mp hp).2.pos
        exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  simp only [Real.log_zpow]
  rw [Finset.sum_filter]
  have e : range (2 * (37 * n) + 1) = insert 0 (Icc 1 (2 * (37 * n))) := by
    ext k;
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [e, Finset.sum_insert (by simp)]
  simp only [Nat.not_prime_zero, ite_false, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold cPrime
  split_ifs <;> push_cast <;> ring

/-- Splitting `(0, N]` at `a ≤ b ≤ c`. -/
lemma sum_split4 (F : ℕ → ℝ) {a b c N : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hcN : c ≤ N) :
    ∑ k ∈ Icc 1 N, F k =
      ∑ k ∈ Ioc 0 a, F k + ∑ k ∈ Ioc a b, F k + ∑ k ∈ Ioc b c, F k + ∑ k ∈ Ioc c N, F k := by
  have e : Icc 1 N = Ioc 0 N := by ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) (hab.trans (hbc.trans hcN)), ←
    Finset.sum_Ioc_consecutive _ hab (hbc.trans hcN), ← Finset.sum_Ioc_consecutive _ hbc hcN]
  ring

/-! ### Small primes -/

lemma log_mul_natLog_le {k Z : ℕ} (hk : 2 ≤ k) (hZ : 1 ≤ Z) :
    (Nat.log k Z : ℝ) * Real.log k ≤ Real.log Z := by
  have h := Nat.pow_log_le_self k (show Z ≠ 0 by omega)
  have h' : ((k ^ Nat.log k Z : ℕ) : ℝ) ≤ (Z : ℝ) := by exact_mod_cast h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [← Real.log_pow]
  push_cast at h'
  exact Real.log_le_log (pow_pos hk0 _) h'

lemma cPrime_natLog_le {k Z : ℕ} (hZ : 1 ≤ Z) :
    cPrime k * (Nat.log k Z : ℝ) ≤ cPrime k + (if k * k ≤ Z then Real.log Z else 0) := by
  unfold cPrime
  split_ifs with hp hkk
  · have := log_mul_natLog_le hp.two_le hZ
    have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    nlinarith
  · have hlt : Nat.log k Z ≤ 1 := by
      have : Z < k ^ 2 := by rw [sq]; omega
      exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) this)
    have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have : (Nat.log k Z : ℝ) ≤ 1 := by exact_mod_cast hlt
    nlinarith
  · simp only [zero_add, zero_mul]
    have : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
    exact Real.log_nonneg this
  · simp

lemma sum_cPrime_le_theta (M : ℕ) : ∑ k ∈ Ioc 0 M, cPrime k ≤ Chebyshev.theta M := by
  rw [theta_eq_sum_cPrime, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega
  · intro k _ _; unfold cPrime; split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_refl _

lemma cPrime_nonneg' (k : ℕ) : 0 ≤ cPrime k := by
  unfold cPrime; split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl _

/-- The small-prime range. -/
lemma small_range_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 (n / 10), cPrime k * (-(Lp n k : ℝ)) ≤
      6 * (37 * n) *
          (Chebyshev.theta (n / 10 : ℕ) + (Real.sqrt (200 * n) + 1) * Real.log (200 * n)) +
        (37 * n) * 100 := by
  have hZ : 1 ≤ 200 * n := by omega
  have hterm :
    ∀ k ∈ Ioc 0 (n / 10),
      cPrime k * (-(Lp n k : ℝ)) ≤
        6 * (37 * n) * (cPrime k + (if k * k ≤ 200 * n then Real.log (200 * n : ℕ) else 0)) +
          (37 * n) * (if k ≤ 24 then 4 else 0) := by
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    have hLp : Lp n k = Lsmall n k := by unfold Lp Mcut; rw [ite_eq_left (by omega)]
    rw [hLp]; unfold Lsmall
    simp only [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
      neg_neg, Nat.cast_mul, Nat.cast_ofNat]
    have h1 := cPrime_natLog_le (k := k) hZ
    have hc0 := cPrime_nonneg' k
    have h24 : cPrime k * (padicValNat k 24 : ℝ) ≤ (if k ≤ 24 then 4 else 0) := by
      unfold cPrime
      split_ifs with hp h24
      · have hv : k ^ padicValNat k 24 ∣ 24 := by have := Fact.mk hp; exact pow_padicValNat_dvd
        have := Nat.le_of_dvd (by norm_num) hv
        have h' : ((k ^ padicValNat k 24 : ℕ) : ℝ) ≤ 24 := by exact_mod_cast this
        have hk0 : (0 : ℝ) < k := by exact_mod_cast hp.pos
        have : (padicValNat k 24 : ℝ) * Real.log k ≤ Real.log 24 := by
          rw [← Real.log_pow];
          push_cast at h'; exact Real.log_le_log (pow_pos hk0 _) h'
        have : Real.log 24 < 4 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 24 / 16 by norm_num)
          have h16 : Real.log 16 = 4 * Real.log 2 := by
            rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
          have := Real.log_two_lt_d9
          have e : Real.log 24 = Real.log (24 / 16) + Real.log 16 := by
            rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
          linarith
        linarith
      · have : padicValNat k 24 = 0 :=
          padicValNat.eq_zero_of_not_dvd
            (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
        rw [this]; simp
      · simp
      · simp
    have hn0 : (0 : ℝ) ≤ 37 * n := by positivity
    have e1 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6 * (37 * n) by positivity)
    have e2 := mul_le_mul_of_nonneg_left h24 hn0
    push_cast at e1
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hθ :=
    sum_cPrime_le_theta
      (n / 10)
        -- the square-root part
  have hsq :
    ∑ k ∈ Ioc 0 (n / 10), (if k * k ≤ 200 * n then Real.log (200 * n : ℕ) else 0) ≤
      (Real.sqrt (200 * n) + 1) * Real.log (200 * n) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hlog : 0 ≤ Real.log (200 * n : ℕ) := Real.log_nonneg (by exact_mod_cast hZ)
    have hcard :
      (((Ioc 0 (n / 10)).filter fun k => k * k ≤ 200 * n).card : ℝ) ≤ Real.sqrt (200 * n) + 1 := by
      have hsub :
        (Ioc 0 (n / 10)).filter (fun k => k * k ≤ 200 * n) ⊆ Icc 1 (Nat.sqrt (200 * n)) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
        exact ⟨hk.1.1, Nat.le_sqrt.mpr hk.2⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      have h2 : ((Nat.sqrt (200 * n) : ℕ) : ℝ) ≤ Real.sqrt (200 * n) := by
        have := Real.nat_sqrt_le_real_sqrt (a := 200 * n)
        push_cast at this; exact this
      have :
        (((Ioc 0 (n / 10)).filter fun k => k * k ≤ 200 * n).card : ℝ) ≤
          (Nat.sqrt (200 * n) : ℝ) :=
        by exact_mod_cast (show _ ≤ Nat.sqrt (200 * n) by omega)
      linarith
    push_cast at hlog ⊢
    exact mul_le_mul_of_nonneg_right hcard hlog
  have h24 : ∑ k ∈ Ioc 0 (n / 10), (if k ≤ 24 then (4 : ℝ) else 0) ≤ 100 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : ((Ioc 0 (n / 10)).filter fun k => k ≤ 24).card ≤ 24 := by
      calc
        _ ≤ (Icc 1 24).card :=
          Finset.card_le_card
            (fun k hk => by
              simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢;
              omega)
        _ = 24 := by simp
    have : (((Ioc 0 (n / 10)).filter fun k => k ≤ 24).card : ℝ) ≤ 24 := by exact_mod_cast this
    linarith
  have hn0 : (0 : ℝ) ≤ 37 * n := by positivity
  push_cast at hsq ⊢
  nlinarith [mul_le_mul_of_nonneg_left h24 hn0,
    mul_le_mul_of_nonneg_left (add_le_add hθ hsq) (show (0 : ℝ) ≤ 6 * (37 * n) by positivity)]

end Zeta5Irrational
