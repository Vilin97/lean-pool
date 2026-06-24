/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
# Legendre Polynomials

In this file, we define the shiftedLegendre polynomials `shiftedLegendre n` for `n : ℕ` as a
polynomial in `ℤ[X]`. We prove some basic properties of the shiftedLegendre polynomials.

-/

open scoped Nat
open BigOperators Finset

variable {R : Type*}

namespace Polynomial

/-- `shiftedLegendre n` is the polynomial defined in terms of derivatives of order n. -/
noncomputable def shiftedLegendre (n : ℕ) : ℝ[X] :=
  C (n ! : ℝ)⁻¹ * derivative^[n] (X ^ n * (1 - X) ^ n)

lemma Finsum_iterate_deriv [CommRing R] (k : ℕ) (h : ℕ → ℕ) :
    derivative^[k] (∑ m ∈ Finset.range (k + 1), (h m) • ((-1) ^ m : R[X]) * X ^ (k + m)) =
    ∑ m ∈ Finset.range (k + 1), (h m) • (-1) ^ m * derivative^[k] (X ^ (k + m)) := by
  induction k + 1 with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, iterate_map_zero]
  | succ n hn =>
    rw[Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at *
    simp only [Fin.val_castSucc, Fin.val_last, iterate_map_add, hn, add_right_inj]
    rw [nsmul_eq_mul, mul_assoc, ← nsmul_eq_mul, Polynomial.iterate_derivative_smul, nsmul_eq_mul,
      mul_assoc]
    rcases n.even_or_odd with (hn1 | hn2)
    · simp_all only [nsmul_eq_mul, Even.neg_pow, one_pow, one_mul]
    · rw [Odd.neg_one_pow hn2]
      simp only [neg_mul, one_mul, iterate_map_neg, mul_neg]

/-- The expand of `shiftedLegendre n`. -/
theorem shiftedLegendre_eq_sum (n : ℕ) : shiftedLegendre n = ∑ k ∈ Finset.range (n + 1),
  C ((-1) ^ k : ℝ) * (Nat.choose n k : ℝ[X]) * (Nat.choose (n + k) n : ℝ[X]) * X ^ k := by
  have h : ((X : ℝ[X]) - X ^ 2) ^ n =
    ∑ m ∈ range (n + 1), n.choose m • (- 1) ^ m * X ^ (n + m) := by
    rw[sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw[neg_pow, pow_two, mul_pow,← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw[Finset.mem_range] at hm
    linarith
  rw [shiftedLegendre, ← mul_pow, mul_one_sub, ← pow_two, h, Finsum_iterate_deriv,
    Finset.mul_sum]
  congr! 1 with x _
  rw [← mul_assoc, Polynomial.iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_div
    (by omega), show n + x - n = x by omega, nsmul_eq_mul, ← mul_assoc, mul_assoc,
    mul_comm]
  simp only [map_pow, map_neg, map_one]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast, ← mul_assoc, ← mul_assoc, add_comm,
    Nat.add_choose, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm]
  nth_rewrite 5 [mul_comm]
  congr 1
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  nth_rewrite 3 [mul_comm]
  congr 1
  apply Polynomial.ext
  intro m
  simp only [coeff_mul_C, coeff_natCast_ite, Nat.cast_ite, CharP.cast_eq_zero, ite_mul,
    zero_mul]
  by_cases h : m = 0
  · subst m
    simp only [↓reduceIte]
    rw [Nat.cast_div]
    · rw [← one_div, ← div_mul_eq_div_mul_one_div]
      norm_cast
      rw [Nat.cast_div]
      · exact Nat.factorial_mul_factorial_dvd_factorial_add x n
      · norm_cast
        apply mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero n)
    · exact Nat.factorial_dvd_factorial (by omega)
    · norm_cast; exact Nat.factorial_ne_zero x
  · simp only [h, ↓reduceIte]

/-- `shiftedLegendre n` is an integer polynomial. -/
lemma shiftedLegendre_eq_int_poly (n : ℕ) : ∃ a : ℕ → ℤ, shiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), (a k : ℝ[X]) * X ^ k := by
  simp_rw [shiftedLegendre_eq_sum]
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  congr! 1 with x
  simp

lemma deriv_one_sub_X {n i : ℕ} : (⇑derivative)^[i] ((1 - X) ^ n : ℝ[X]) =
    (-1) ^ i * (n.descFactorial i) • ((1 - X) ^ (n - i)) := by
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul, Algebra.smul_def, algebraMap_eq, map_natCast]
  simp

theorem differentiableAt_inv_special {x a : ℝ} {n : ℕ}
    (ha : a > 0) (hx : 1 - a * x = 0) :
    ¬DifferentiableAt ℝ (fun x ↦ ↑n ! * a ^ n / (1 - a * x) ^ (n + 1)) x := by
  intro h
  obtain q := h.continuousAt
  simp only [Metric.continuousAt_iff, Real.dist_eq, hx, ne_eq, Nat.succ_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, abs_div, abs_mul, abs_pow, abs_of_nonneg,
    Nat.cast_nonneg] at q
  have h₁ : ↑n ! * |a| ^ n > 0 := by
    apply mul_pos
    · simp only [Nat.cast_pos]
      exact Nat.factorial_pos n
    · apply pow_pos
      exact abs_pos.2 (by linarith)
  specialize q (↑n ! * |a| ^ n) h₁
  rcases q with ⟨q, ⟨qq, qqq⟩⟩
  rcases lt_trichotomy (a * q) 1 with (h1 | h2 | h3)
  · have : |a * q / 2 * q + x - x| < q := by
      simp only [add_sub_cancel_right]
      calc
      _ = a * q / 2 * q := by
        rw [abs_eq_self, mul_comm, ← mul_div_assoc, ← mul_assoc]
        suffices 0 < q * a * q by linarith
        exact mul_pos (mul_pos qq ha) qq
      _ < 1 / 2 * q := by
        nlinarith [mul_pos ha qq]
      _ < q := by linarith
    specialize qqq this
    rw [div_lt_iff₀] at qqq
    · have : 1 <  |1 - a * (a * q / 2 * q + x)| ^ (n + 1) := by
        exact (mul_lt_mul_iff_right₀ h₁).mp
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using qqq)
      rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg] at this
      have : |a * (a * q / 2 * q)| ^ (n + 1) < 1 := by
        apply pow_lt_one₀ (by positivity) _ (by omega)
        · nth_rewrite 2 [mul_comm]
          rw [← mul_assoc, ← mul_div_assoc, ← pow_two]
          rw [show |((a * q) ^ 2 / 2 : ℝ)| = ((a * q) ^ 2 / 2 : ℝ) by
            exact abs_eq_self.2 (by positivity)]
          trans 1 / 2
          · rw [div_lt_div_iff_of_pos_right (by norm_num), ← one_pow (n := 2)]
            apply pow_lt_pow_left₀ <;> nlinarith
          · linarith
      linarith
    · apply pow_pos
      rw [abs_pos, mul_add, add_comm, ← sub_sub, hx, zero_sub]
      suffices a * (a * q / 2 * q) > 0 by linarith
      nth_rewrite 2 [mul_comm]
      rw [← mul_assoc, ← mul_div_assoc, ← pow_two]
      positivity
  · have : |q / 2 + x - x| < q := by
      simp only [add_sub_cancel_right]
      rw [show |(q / 2 : ℝ)| = (q / 2 : ℝ) by exact abs_eq_self.2 (by linarith)]
      linarith
    specialize qqq this
    rw [div_lt_iff₀] at qqq
    · have : 1 <  |1 - a * (q / 2 + x)| ^ (n + 1) := by
        exact (mul_lt_mul_iff_right₀ h₁).mp
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using qqq)
      rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg, ← mul_div_assoc, h2] at this
      have : 1 < (1 / 2 : ℝ) := by
        suffices (1 : ℝ) ≥ |(1 / 2 : ℝ)| ^ (n + 1) by linarith
        rw [show |(1 / 2 : ℝ)| = (1 / 2 : ℝ) by exact abs_eq_self.2 (by linarith)]
        apply pow_le_one₀ <;> linarith
      linarith
    · apply pow_pos
      rw [abs_pos]
      linarith
  · have : |1 / a + x - x| < q := by
      simp only [one_div, add_sub_cancel_right]
      rw [← one_div]
      have : |(1 / a : ℝ)| = (1 / a : ℝ) := by
        rw [abs_eq_self, one_div_nonneg]
        linarith
      rw [this, div_lt_iff₀] <;> linarith
    specialize qqq this
    rw [div_lt_iff₀] at qqq
    · have : 1 <  |1 - a * (1 / a + x)| ^ (n + 1) := by
        exact (mul_lt_mul_iff_right₀ h₁).mp
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using qqq)
      rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg, ← mul_div_assoc, mul_one,
        div_self (by linarith)] at this
      simp only [abs_one, one_pow, lt_self_iff_false] at this
    · rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg, ← mul_div_assoc, mul_one,
        div_self (by linarith)]
      simp

lemma n_derivative {a : ℝ} (n : ℕ) (ha : a > 0) : deriv^[n] (fun x ↦ 1 / (1 - a * x)) =
    fun x ↦ (n) ! * (a ^ n) / (1 - a * x) ^ (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    ext x
    rcases eq_or_ne (1 - a * x) 0 with (h | hne)
    · simp only [h, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, div_zero]
      rw [Function.iterate_succ_apply', hn]
      apply deriv_zero_of_not_differentiableAt
      exact differentiableAt_inv_special ha h
    · rw [Function.iterate_succ_apply', hn, deriv_fun_div]
      · simp only [deriv_const', zero_mul, zero_sub]
        rw [div_eq_div_iff]
        · rw [deriv_fun_pow, deriv_const_sub, deriv_const_mul]
          · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one,
            mul_neg, neg_neg]
            norm_cast
            rw [Nat.factorial_succ, ← pow_mul', Nat.cast_mul]
            ring
          · apply differentiableAt_id
          · apply DifferentiableAt.sub
            · apply differentiableAt_const
            · apply DifferentiableAt.mul
              · apply differentiableAt_const
              · apply differentiableAt_id
        · apply pow_ne_zero
          exact pow_ne_zero (n + 1) hne
        · exact pow_ne_zero (n + 1 + 1) hne
      · apply differentiableAt_const
      · apply DifferentiableAt.pow
        apply DifferentiableAt.sub
        · apply differentiableAt_const
        · apply DifferentiableAt.mul
          · apply differentiableAt_const
          · apply differentiableAt_id
      · exact pow_ne_zero (n + 1) hne

theorem differentiableAt_inv_special' (c x y z : ℝ) (n : ℕ) (hc : c ≠ 0)
    (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) (h1 : 1 - (1 - x * y) * z = 0) :
    ¬DifferentiableAt ℝ (fun y ↦ c / (1 - (1 - x * y) * z) ^ (n + 1)) y := by
  intro h
  obtain q := h.continuousAt
  simp only [Metric.continuousAt_iff, Real.dist_eq, h1, ne_eq, Nat.succ_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, abs_div, abs_pow] at q
  simp only [Set.mem_Ioo] at hx hz
  have h₁ : |c| > 0 := by simp [hc]
  specialize q (|c|) h₁
  rcases q with ⟨q, ⟨qq, qqq⟩⟩
  set d := min (q / 2 + y) (1 / |x * z| + y)
  set d' := min (q / 2) (1 / |x * z|)
  have h' : d = d' + y := by
    simp only [d, d']
    rw [min_add_add_right]
  have hd : |d - y| < q := by
    rw [h', show d' + y - y = d' by ring]
    suffices |d'| ≤ q / 2 by linarith
    rw [abs_of_nonneg (by positivity)]
    exact min_le_left (q / 2) (1 / |x * z|)
  have hd' : 1 - (1 - x * d) * z ≠ 0 := by
    suffices 1 - (1 - x * d) * z > 0 by linarith
    rw [h',
      show 1 - (1 - x * (d' + y)) * z = 1 - (1 - x * y) * z + x * z * d' by
        ring,
      h1, zero_add]
    apply mul_pos
    · apply mul_pos <;> linarith
    simp only [d']
    apply lt_min (by positivity)
    simp only [one_div, inv_pos, abs_pos, ne_eq, mul_eq_zero, not_or]
    constructor <;> linarith
  specialize qqq hd
  rw [div_lt_iff₀] at qqq
  · rw [lt_mul_iff_one_lt_right h₁, h', show 1 - (1 - x * (d' + y)) * z =
      1 - (1 - x * y) * z + x * z * d' by ring, h1, zero_add,
      one_lt_pow_iff_of_nonneg (by positivity) (by norm_num)] at qqq
    have contra : |x * z * d'| ≤ 1 := by
      calc
      _ = |x * z| * |d'| := by rw [abs_mul]
      _ ≤ |x * z| * (1 / |x * z|) := by
        apply mul_le_mul (by linarith) _ (abs_nonneg _) (abs_nonneg _)
        rw [← abs_one_div]
        apply abs_le_abs_of_nonneg (by positivity)
        simp only [d']
        rw [abs_of_nonneg (a := x * z)]
        · exact min_le_right (q / 2) (1 / (x * z))
        · exact mul_nonneg (by linarith) (by linarith)
      _ = 1 := by
        rw [mul_div, mul_one, div_self]
        simp only [ne_eq, abs_eq_zero, mul_eq_zero, not_or]
        constructor <;> linarith
    linarith
  · apply pow_pos
    simpa only [abs_pos] using hd'

lemma n_derivative' {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    (deriv^[n] fun y ↦ 1 / (1 - (1 - x * y) * z)) =
    (fun y ↦ (-1) ^ n * (n) ! * (x * z) ^ n / (1 - (1 - x * y) * z) ^ (n + 1)) := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    ext y
    rcases eq_or_ne (1 - (1 - x * y) * z) 0 with (h | hne)
    · simp only [h, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, div_zero]
      simp only [Set.mem_Ioo] at hx hz
      rw [Function.iterate_succ_apply', hn]
      apply deriv_zero_of_not_differentiableAt
      set c := (-1) ^ n * ↑n ! * (x * z) ^ n
      have hc : c ≠ 0 := by
        simp only [c]
        apply mul_ne_zero
        · simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
            Nat.cast_eq_zero, Nat.factorial_ne_zero, or_self, not_false_eq_true]
        · apply pow_ne_zero
          nlinarith
      exact differentiableAt_inv_special' c x y z n hc hx hz h
    · rw [Function.iterate_succ_apply', hn, deriv_fun_div]
      · simp only [deriv_const', zero_mul, zero_sub]
        have h :
            (fun y ↦ (1 - (1 - x * y) * z) ^ (n + 1)) =
              fun y ↦ (1 - z + x * z * y) ^ (n + 1) := by
          ext _; ring
        rw [div_eq_div_iff]
        · rw [h, deriv_fun_pow, deriv_const_add, deriv_const_mul]
          · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one,
              ← neg_mul]
            rw [show -(-1) ^ n = (-1 : ℝ) ^ (n + 1) by ring,
              show ((n + 1)! : ℝ) = (((n : ℕ) + 1) : ℝ) * (n !) by
                rw [Nat.factorial_succ]
                norm_cast]
            ring
          · apply differentiableAt_id
          · apply DifferentiableAt.add
            · apply differentiableAt_const
            · apply DifferentiableAt.mul
              · apply differentiableAt_const
              · apply differentiableAt_id
        · apply pow_ne_zero
          exact pow_ne_zero (n + 1) hne
        · exact pow_ne_zero (n + 1 + 1) hne
      · apply differentiableAt_const
      · apply DifferentiableAt.pow
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.mul_const
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.const_mul differentiableAt_id
      · exact pow_ne_zero (n + 1) hne

lemma shiftedLegendre_poly_eval_zero_eq_zero {m : ℕ} (h : m < n) :
    eval 0 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; left
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X,
    smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt,
    pow_eq_zero_iff', ne_eq, true_and]
  right
  suffices n - (m - x) > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  rw [Nat.lt_add_one_iff] at hx
  calc
    m - x ≤ m := by simp
    _ < n := by exact h

lemma shiftedLegendre_poly_eval_one_eq_zero {m : ℕ} (h : m < n) :
    eval 1 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; right
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul, eval_pow,
    eval_neg, eval_one, eval_sub, eval_X, sub_self, smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and,
    true_and, false_or]
  right
  suffices n - x > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  linarith

lemma shiftedLegendre_continuousOn {n m : ℕ} : ContinuousOn
    (fun x ↦ eval x ((⇑derivative)^[n - m] (X ^ n * (1 - X) ^ n : ℝ[X]))) (Set.uIcc 0 1) := by
  simp_rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply continuousOn_finsetSum
  intro i _
  simp_rw [Algebra.smul_def, eval_mul]
  apply ContinuousOn.mul
  · simp only [eq_natCast, eval_natCast, zero_le_one, Set.uIcc_of_le]
    apply continuousOn_const
  · apply ContinuousOn.mul
    · simp_rw [Polynomial.iterate_derivative_X_pow_eq_smul]
      simp only [eval_smul, eval_pow, eval_X, smul_eq_mul, zero_le_one,
        Set.uIcc_of_le]
      apply ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
    · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
        Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
        Polynomial.iterate_derivative_X_pow_eq_smul]
      simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
        eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul, zero_le_one,
        Set.uIcc_of_le]
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
      apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_id)

lemma special_deriv_div_continuousOn {m : ℕ} {x z : ℝ} (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) :
    ContinuousOn (fun u ↦ (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u) (Set.uIcc 0 1) := by
  simp_rw [n_derivative' m hx hz]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const continuousOn_id
  · intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc, Set.mem_Ioo] at hy hx hz
    apply pow_ne_zero
    suffices 1 - (1 - x * y) * z > 0 by linarith
    simp only [sub_pos]
    suffices (1 - x * y) * z ≤ z by linarith
    apply mul_le_of_le_one_left (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith

lemma integral_shiftedLegendre_mul_smooth_eq_aux {x z : ℝ} (n m : ℕ) (h : m ≤ n)
    (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) : ∫ (y : ℝ) in (0)..1,
    eval y ((⇑derivative)^[n] (X ^ n * (1 - X) ^ n)) * (fun y ↦ 1 / (1 - (1 - x * y) * z)) y =
    (- 1) ^ m * ∫ (y : ℝ) in (0)..1, eval y ((⇑derivative)^[n - m] (X ^ n * (1 - X) ^ n)) *
    (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) y:= by
  induction m with
  | zero =>
    simp
  | succ m hm =>
    have h₀ : m < n := by linarith
    have h₁ : n - (m + 1) < n := by omega
    rw [hm (LT.lt.le h₀), pow_add, pow_one, mul_assoc]
    congr
    symm
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
    rw [neg_one_mul, neg_eq_iff_eq_neg,
      intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun u ↦ eval u ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X])))
      (u' := fun u ↦
        eval u
          (derivative
            ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X]))))
      (v := fun u ↦ (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u)]
    · rw [shiftedLegendre_poly_eval_one_eq_zero h₁, shiftedLegendre_poly_eval_zero_eq_zero h₁]
      simp only [one_div, zero_mul, sub_self, zero_sub, Function.iterate_succ_apply']
    · apply shiftedLegendre_continuousOn
    · apply special_deriv_div_continuousOn hx hz
    · intro x _
      simp_rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
      simp only [Nat.succ_eq_add_one, nsmul_eq_mul, eval_mul, eval_natCast, map_sum,
        eval_finsetSum]
      apply HasDerivAt.fun_sum
      intro i _
      simp only [derivative_mul, derivative_natCast, zero_mul, zero_add, eval_mul, eval_natCast,
        eval_add]
      apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · rw [Polynomial.iterate_derivative_X_pow_eq_smul]
        simp only [eval_smul, eval_pow, eval_X, smul_eq_mul, LinearMapClass.map_smul,
          derivative_X_pow, map_natCast, eval_mul, eval_natCast]
        apply HasDerivAt.const_mul
        apply hasDerivAt_pow
      · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
          Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
          Polynomial.iterate_derivative_X_pow_eq_smul]
        simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
          eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul, LinearMapClass.map_smul]
        apply HasDerivAt.const_mul
        simp only [derivative_mul, eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X,
          eval_neg]
        have h1 : (derivative ((-1) ^ i : ℝ[X])) = 0 := by
          rw [show ((-1) ^ i : ℝ[X]) = C ((-1) ^ i) by simp, derivative_C]
        rw [h1, eval_zero, zero_mul, zero_add]
        apply HasDerivAt.const_mul
        rw [show (1 - X : ℝ[X]) ^ (n - i) = (X ^ (n - i) : ℝ[X]).comp (1 - X) by simp,
          Polynomial.derivative_comp_one_sub_X (p := X ^ (n - i)),
          Polynomial.derivative_X_pow]
        simp only [mul_comp, pow_comp, X_comp, eval_mul, map_natCast, natCast_comp, eval_neg,
          eval_mul, eval_natCast, eval_pow, eval_sub, eval_one, eval_X]
        rw [← mul_neg_one]
        apply HasDerivAt.pow
        apply HasDerivAt.const_sub
        apply hasDerivAt_id
    · intro y hy
      simp only [Set.mem_Ioo, zero_le_one, min_eq_left, max_eq_right] at hx hy hz
      have hh : 1 - (1 - x * y) * z ≠ 0 := by
        suffices 1 - (1 - x * y) * z > 0 by linarith
        simp only [sub_pos]
        suffices (1 - x * y) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
      have (u : ℝ) : deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u =
        Function.eval u (deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z))) := by
        simp only [one_div, Function.eval]
      simp_rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval,
        n_derivative' _ hx hz]
      have :
          (-1) ^ (m + 1) * ↑(m + 1)! * (x * z) ^ (m + 1) /
            (1 - (1 - x * y) * z) ^ (m + 1 + 1)
        = (0 * (1 - (1 - x * y) * z) ^ (m + 1) -
          (-1) ^ m * ↑m ! * (x * z) ^ m *
            ((m + 1) * (x * z) * (1 - (1 - x * y) * z) ^ m)) /
          ((1 - (1 - x * y) * z) ^ (m + 1)) ^ 2 := by
        simp only [zero_mul, zero_sub]
        rw [div_eq_div_iff]
        · simp only [pow_add, ← neg_mul]
          rw [show -(-1 : ℝ) ^ m = (-1 : ℝ) ^ m * (-1) ^ 1 by ring,
            show ((m + 1)! : ℝ) = (((m : ℕ) + 1) : ℝ) * (m !) by
              rw [Nat.factorial_succ]
              norm_cast]
          ring
        · apply pow_ne_zero _ hh
        · apply pow_ne_zero
          apply pow_ne_zero _ hh
      rw [this]
      apply HasDerivAt.div
      · apply hasDerivAt_const
      · have :
            (↑m + 1) * (x * z) * (1 - (1 - x * y) * z) ^ m =
              deriv (fun y ↦ (1 - (1 - x * y) * z) ^ (m + 1)) y := by
          simp only [show 1 - (1 - x * y) * z = 1 - z + x * z * y by ring]
          rw [deriv_fun_pow,
            show (fun y ↦ 1 - (1 - x * y) * z) = (fun y ↦ 1 - z + x * z * y) by
              ext _
              ring]
          · rw[deriv_const_add, deriv_const_mul]
            · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one]
              norm_cast
              ring
            · exact differentiableAt_id
          · apply DifferentiableAt.const_sub
            apply DifferentiableAt.mul_const
            · apply DifferentiableAt.const_sub
              apply DifferentiableAt.const_mul differentiableAt_id
        simp only [this, hasDerivAt_deriv_iff]
        apply DifferentiableAt.pow
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.mul_const
        · apply DifferentiableAt.const_sub
          apply DifferentiableAt.const_mul differentiableAt_id
      · apply pow_ne_zero _ hh
    · simp_rw [← Function.iterate_succ_apply', Polynomial.iterate_derivative_mul,
        Polynomial.eval_finsetSum]
      simp only [Nat.succ_eq_add_one, nsmul_eq_mul, eval_mul, eval_natCast]
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      apply continuousOn_finsetSum
      intro i _
      apply ContinuousOn.mul continuousOn_const
      · apply ContinuousOn.mul
        · simp_rw [Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [eval_smul, eval_pow, eval_X, smul_eq_mul]
          apply ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
        · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
            Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
            Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
            eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul]
          refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
          apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_id)
    · have : deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) =
        (Function.eval · (deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)))) := by
        ext x
        simp only [one_div, Function.eval]
      rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval]
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      rw [← Set.uIcc_of_le (by norm_num)]
      apply special_deriv_div_continuousOn hx hz

lemma integral_legendre_mul_smooth_eq {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) :
    ∫ (y : ℝ) in (0)..1, eval y (shiftedLegendre n) * (fun y ↦ 1 / (1 - (1 - x * y) * z)) y =
    (- 1) ^ n / n ! * ∫ (y : ℝ) in (0)..1, y ^ n * (1 - y) ^ n *
    (deriv^[n] fun y ↦ 1 / (1 - (1 - x * y) * z)) y := by
  simp only [eval_mul, one_div, eval_C, shiftedLegendre]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [← mul_one_div, one_div]
  nth_rw 4 [mul_comm]
  rw [mul_assoc]
  congr
  obtain h := integral_shiftedLegendre_mul_smooth_eq_aux (n := n) (m := n) (by norm_num) hx hz
  simp only [one_div, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
    eval_mul, eval_pow, eval_X, eval_sub, eval_one] at h
  rw [h]
  simp_rw [← mul_assoc]

private lemma one_sub_pow_pos {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    (1 - (1 - x * y) * z) ^ (n + 1) > 0 := by
  simp only [Set.mem_Ioo] at hx hz
  simp only [Set.mem_Icc] at hy
  apply pow_pos
  simp only [sub_pos]
  suffices (1 - x * y) * z ≤ z by linarith
  apply mul_le_of_le_one_left (by linarith [mul_nonneg (le_of_lt hx.1) hy.1])
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  nlinarith

lemma legendre_integral_special {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) :
    ∫ (y : ℝ) in (0)..1, eval y (shiftedLegendre n) * (1 / (1 - (1 - x * y) * z)) =
    ∫ (y : ℝ) in (0)..1,
      (x * y * z) ^ n * (1 - y) ^ n / (1 - (1 - x * y) * z) ^ (n + 1) := by
  rw [integral_legendre_mul_smooth_eq n hx hz, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun (by simp)
  intro y hy
  simp only
  rw [n_derivative' n hx hz]
  simp_all only [Set.mem_Ioo, Set.mem_Icc]
  rw [← mul_assoc, mul_div, div_eq_div_iff]
  · rw [mul_assoc, mul_assoc, mul_assoc, mul_comm, mul_div]
    symm
    rw [eq_div_iff]
    · symm
      calc
      _ = y ^ n * ((1 - y) ^ n * (↑n ! * (x * z) ^ n * (1 - (1 - x * y) * z) ^ (n + 1))) *
        ((-1) ^ n * (-1) ^ n) := by
        ring
      _ = (x * y * z) ^ n * (1 - y) ^ n * (1 - (1 - x * y) * z) ^ (n + 1) * ↑n ! := by
        rw [← pow_add, ← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, mul_one]
        ring
    · norm_cast
      exact Nat.factorial_ne_zero n
  · linarith [one_sub_pow_pos n hx hz y hy]
  · linarith [one_sub_pow_pos n hx hz y hy]

end Polynomial
