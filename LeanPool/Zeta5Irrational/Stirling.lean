/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # Stirling-type bounds used in Section 6 of the paper

* `log_factorial_le` : `log m! ≤ m log m - m + (log m)/2 + 1` for `m ≥ 1`;
* `log_factorial_ge` : `m log m - m ≤ log m!`;
* `sum_log_factorial_two_mul_ge` : `∑_{i=1}^{h-1} log (2i)! ≥ h² log 2h - (3/2) h² - 2h log 2h`,
  the bound displayed before (6.15) in the paper.
-/

public section

open Real Finset

namespace Zeta5Irrational

lemma log_factorial_le {m : ℕ} (hm : 1 ≤ m) :
    Real.log (m.factorial) ≤ m * Real.log m - m + Real.log m / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h1
  have hm0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hs : (0 : ℝ) < √(2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1) := by
    positivity
  unfold Stirling.stirlingSeq at h1
  rw [Real.log_div hfac.ne' hs.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hm0.ne' (exp_pos 1).ne',
    Real.log_exp, Real.log_mul (by norm_num) hm0.ne',
    Real.log_div (exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_sqrt (by norm_num)] at h1
  push_cast at h1 ⊢
  linarith

lemma log_factorial_ge (m : ℕ) : m * Real.log m - m ≤ Real.log (m.factorial) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := Stirling.le_log_factorial_stirling (n := m) hm.ne'
  have h1 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have h2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith

/-- An antiderivative of `x log (2x)`. -/
noncomputable def Gaux (x : ℝ) : ℝ :=
  x ^ 2 / 2 * Real.log (2 * x) - x ^ 2 / 4

lemma hasDerivAt_Gaux {x : ℝ} (hx : 0 < x) : HasDerivAt Gaux (x * Real.log (2 * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
  have h2 : HasDerivAt (fun x : ℝ => Real.log (2 * x)) (2 / (2 * x)) x := h1.log (by positivity)
  have h3 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (2 * x / 2) x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h4 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (2 * x / 4) x := by
    simpa using (hasDerivAt_pow 2 x).div_const 4
  have key :
    HasDerivAt (fun x : ℝ => x ^ 2 / 2 * Real.log (2 * x) - x ^ 2 / 4)
      (2 * x / 2 * Real.log (2 * x) + x ^ 2 / 2 * (2 / (2 * x)) - 2 * x / 4) x :=
    (h3.mul h2).sub h4
  have e :
    2 * x / 2 * Real.log (2 * x) + x ^ 2 / 2 * (2 / (2 * x)) - 2 * x / 4 = x * Real.log (2 * x) :=
    by field_simp; ring
  rw [e] at key
  exact key

lemma integral_x_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, x * Real.log (2 * x) = Gaux b - Gaux a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_Gaux ?_) ?_
  · rw [Set.uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine continuousOn_id.mul (ContinuousOn.log (continuousOn_const.mul continuousOn_id) ?_)
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    positivity

lemma monotoneOn_x_log : MonotoneOn (fun x : ℝ => x * Real.log (2 * x)) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hlog : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  exact mul_le_mul hxy (Real.log_le_log (by linarith) (by linarith)) hlog (by linarith)

lemma sum_range_cast (m : ℕ) : ∑ k ∈ range m, (k : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `∑_{i=1}^{h-1} log (2i)! ≥ h² log (2h) - (3/2) h² - 2 h log (2h)`. -/
lemma sum_log_factorial_two_mul_ge {h : ℕ} (hh : 2 ≤ h) :
    (h : ℝ) ^ 2 * Real.log (2 * h) - 3 / 2 * (h : ℝ) ^ 2 - 2 * h * Real.log (2 * h) ≤
      ∑ i ∈ Icc 1 (h - 1), Real.log ((2 * i).factorial) := by
  have e1 : Icc 1 (h - 1) = Ico 1 h := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico];
    omega
      -- Step 1: `log (2i)! ≥ 2i log (2i) - 2i`
  have hstep1 :
    ∑ i ∈ Icc 1 (h - 1), (2 * (i : ℝ) * Real.log (2 * i) - 2 * i) ≤
      ∑ i ∈ Icc 1 (h - 1), Real.log ((2 * i).factorial) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := log_factorial_ge (2 * i)
    push_cast at this
    linarith
  have hsplit :
    ∑ i ∈ Icc 1 (h - 1), (2 * (i : ℝ) * Real.log (2 * i) - 2 * i) =
      2 * ∑ i ∈ Icc 1 (h - 1), ((i : ℝ) * Real.log (2 * i)) -
        ∑ i ∈ Icc 1 (h - 1), (2 * (i : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact
      Finset.sum_congr rfl fun i _ => by
        ring
          -- Step 2: sum vs integral for `i log (2i)`
  have hmono :
    MonotoneOn (fun x : ℝ => x * Real.log (2 * x)) (Set.Icc 1 (1 + ((h - 2 : ℕ) : ℝ))) :=
    monotoneOn_x_log.mono fun x hx => hx.1
  have hcmp := hmono.integral_le_sum
  have hnn : (0 : ℝ) ≤ ((h - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [integral_x_log one_pos (by linarith)] at hcmp
  have hsum :
    ∑ i ∈ Icc 1 (h - 1), ((i : ℝ) * Real.log (2 * i)) =
      (1 : ℝ) * Real.log (2 * 1) +
        ∑ i ∈ range (h - 2), (1 + ((i + 1 : ℕ) : ℝ)) * Real.log (2 * (1 + ((i + 1 : ℕ) : ℝ))) := by
    rw [e1, Finset.sum_Ico_eq_sum_range, show h - 1 = (h - 2) + 1 by omega,
      Finset.sum_range_succ', add_comm]
    congr 1
    · push_cast; ring_nf
    · refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring_nf
  have hcast : (1 : ℝ) + ((h - 2 : ℕ) : ℝ) = (h : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)];
    push_cast; ring
  rw [hcast] at hcmp
        -- Step 3: bounds for `Gaux (h - 1)` and `Gaux 1`
  have hh1 : (1 : ℝ) ≤ (h : ℝ) - 1 := by
    have : (2 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hhpos : (0 : ℝ) < h := by positivity
  have hlog2h : 0 ≤ Real.log (2 * h) := Real.log_nonneg (by linarith)
  have hlogratio : Real.log (2 * ((h : ℝ) - 1)) ≥ Real.log (2 * h) - 1 / ((h : ℝ) - 1) := by
    have h1 : Real.log (2 * ((h : ℝ) - 1)) = Real.log (2 * h) + Real.log (((h : ℝ) - 1) / h) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    have h2 : Real.log (((h : ℝ) - 1) / h) = -Real.log ((h : ℝ) / (h - 1)) := by
      rw [← Real.log_inv]; congr 1; rw [inv_div]
    have h3 : Real.log ((h : ℝ) / (h - 1)) ≤ (h : ℝ) / (h - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h4 : (h : ℝ) / (h - 1) - 1 = 1 / ((h : ℝ) - 1) := by field_simp; ring
    linarith
  have hG1 : Gaux 1 ≤ 1 / 4 := by
    unfold Gaux
    have := Real.log_two_lt_d9
    norm_num; linarith
  have hGh :
    Gaux ((h : ℝ) - 1) ≥
      (h : ℝ) ^ 2 / 2 * Real.log (2 * h) - h * Real.log (2 * h) - ((h : ℝ) - 1) / 2 -
        ((h : ℝ) - 1) ^ 2 / 4 := by
    unfold Gaux
    have hpos : (0 : ℝ) < (h : ℝ) - 1 := by linarith
    have e2 : ((h : ℝ) - 1) ^ 2 * (1 / ((h : ℝ) - 1)) = (h : ℝ) - 1 := by field_simp
    have e3 :
      ((h : ℝ) - 1) ^ 2 * Real.log (2 * h) ≥
        (h : ℝ) ^ 2 * Real.log (2 * h) - 2 * h * Real.log (2 * h) :=
      by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hlogratio.le (sq_nonneg ((h : ℝ) - 1))]
      -- Step 4: assemble
  have hsum_i : ∑ i ∈ Icc 1 (h - 1), (2 * (i : ℝ)) = (h : ℝ) * (h - 1) := by
    rw [e1, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.cast_add, Nat.cast_one, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_range_cast, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hf1 : (0 : ℝ) ≤ 1 * Real.log (2 * 1) := by norm_num; exact Real.log_nonneg (by norm_num)
  nlinarith

end Zeta5Irrational
