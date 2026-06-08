/-
Copyright (c) 2026 Joseph McKinsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph McKinsey
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log
import LeanPool.Flean.FloatCfg

/-!
# Logarithmic Properties of Scientific Notation for Floating-Point
This module proves facts in ℚ about the sizes and properties of
values like x * b^e where x is in [1, b) and e is an integer.
-/

variable {C : FloatCfg}

/-- For 1 ≤ x, (x * b^e) has an exponent at least e. -/
lemma le_log_of_ge_1 {b : ℕ} {e : ℤ} (h : 1 < b) {x : ℚ} (h' : 1 ≤ x) :
  e ≤ Int.log b (x * b ^ e) := by
  suffices b^e ≤ x * b^e by
    -- Use the b^x ≤ y connection between log and zpow
    apply (Int.zpow_le_iff_le_log (b := b) h (by positivity)).1
    exact this
  -- then, it's linear arithmetic
  nth_rw 1 [<-one_mul ((b : ℚ)^e)]
  exact (mul_le_mul_iff_left₀ (zpow_pos (by positivity) e)).mpr h'

/-- When 1 ≤ x < 2, x*b^e has exponent exactly e. -/
lemma log_one_to_two_eq {b : ℕ} {e : ℤ} (h : 1 < b) {x : ℚ} (h' : 1 ≤ x) (h'' : x < b) :
  Int.log b (x * b ^ e) = e := by
  have bpos : (0 : ℚ) < b := by norm_cast; linarith
  have x_be_pos : 0 < x * b^e := mul_pos (by linarith) (zpow_pos bpos e)
  apply le_antisymm
  · -- Since log rounds down...
    suffices x * b^e < b^(e + 1) by
      -- Then we can use the x < b^y connection.
      have : Int.log b (x * b^e) < e + 1 := by
        apply (Int.lt_zpow_iff_log_lt (b := b) h (x_be_pos)).1
        exact this
      linarith
    -- Basic factoring and linear arithmetic
    rw [zpow_add_one₀ (by linarith), mul_comm]
    exact (mul_lt_mul_iff_right₀ (zpow_pos bpos e)).mpr h''
  exact le_log_of_ge_1 h h'

/-- When 0 < x < 1, then x*2^e has exponent < e. -/
lemma log_zero_to_one_lt (x : ℚ) (e : ℤ) (h : 0 < x) (h' : x < 1) :
  Int.log 2 |x * 2 ^ e| < e := by
  rw [<-Int.lt_zpow_iff_log_lt (by norm_num)]
  · rw [abs_of_nonneg (by positivity)]
    simp only [Nat.cast_ofNat]
    rw [mul_lt_iff_lt_one_left (by positivity)]
    exact h'
  positivity

lemma mantissa_ge_one {m : ℕ} : 1 ≤ ((m : ℚ) / C.prec + 1) := by
  suffices 0 ≤ (m : ℚ) / C.prec by linarith
  positivity

lemma mantissa_lt_two {m : ℕ} (h : m < C.prec) : ((m : ℚ) / C.prec + 1) < 2 := by
  suffices (m : ℚ) / C.prec < 1 by linarith
  apply (div_lt_one (by norm_cast; exact C.prec_pos)).mpr
  norm_cast

--lemma mantissa_2e_pos {e : ℤ} {m : ℕ} : 0 < ((m : ℚ) / C.prec + 1) * 2^e := by
--  positivity

lemma q_exp_eq_exp {e : ℤ} {m : ℕ} (h : m < C.prec) :
  Int.log 2 |((m : ℚ) / ↑C.prec + 1) * 2 ^ e| = e := by
  have mantissa_lt : ((m : ℚ) / C.prec + 1) < 2 := by
    suffices (m : ℚ) / C.prec < 1 by linarith
    suffices (m : ℚ) < C.prec by
      apply Bound.div_lt_one_of_pos_of_lt
      · norm_cast; exact Nat.zero_lt_of_lt h
      exact this
    norm_cast
  rw [abs_of_nonneg (by positivity)]
  exact log_one_to_two_eq (by norm_num) mantissa_ge_one (by norm_cast)

lemma q_mantissa_eq_mantissa {e : ℤ} {m : ℕ} (h : m < C.prec) :
    |(((m : ℚ)/C.prec) + 1) * 2^e| * (2^(Int.log 2 |(((m : ℚ)/C.prec) + 1) * 2^e|))⁻¹
      = (m : ℚ) / C.prec + 1 := by
  rw [q_exp_eq_exp h, abs_of_pos (by positivity), mul_assoc,
    mul_inv_cancel₀, mul_one]
  positivity

lemma mantissa_size_aux (q : ℚ) (h : q ≠ 0) : 1 ≤ |q| * (2 ^ Int.log 2 |q|)⁻¹ ∧
  |q| * (2 ^ Int.log 2 |q|)⁻¹ < 2 := by
  constructor
  · suffices (2 ^ Int.log 2 |q|) ≤ |q| by
      rw [<-mul_one (2 ^ _)] at this
      rw [mul_comm]
      exact (le_inv_mul_iff₀ (zpow_pos rfl _ : (0 : ℚ) < 2 ^ Int.log 2 |q|)).2 this
    exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr h)
  suffices |q| < 2 ^ (Int.log 2 |q| + 1) by
    rw [zpow_add_one₀ (by norm_num), mul_comm] at this
    exact (mul_inv_lt_iff₀ (zpow_pos rfl _ : (0 : ℚ) < 2 ^ Int.log 2 |q|)).2 this
  apply Int.lt_zpow_succ_log_self (by norm_num : 1 < 2)


lemma small_floor_aux {q : ℚ} {n : ℕ} (h : q < 1) (h' : 0 ≤ q) (n_pos : 0 < n) :
  ⌊q * n⌋.natAbs < n := by
  suffices ⌊q * n⌋.natAbs < (n : ℤ) by
    norm_cast at this
  rw [Int.natAbs_of_nonneg (by positivity)]
  suffices q * n < n by
    exact Int.floor_lt.mpr this
  exact (mul_lt_iff_lt_one_left (by norm_cast : 0 < (n : ℚ))).2 h

lemma small_ceil {q : ℚ} {n : ℕ} (h : q ≤ 1) (h' : 0 ≤ q) (n_nonneg : 0 ≤ n) :
  ⌈q * n⌉.natAbs ≤ n := by
  suffices ⌈q * n⌉.natAbs ≤ (n : ℤ) by
    norm_cast at this
  rw [Int.natAbs_of_nonneg (by positivity)]
  apply Int.ceil_le.mpr
  exact mul_le_of_le_one_left (by norm_cast) h

lemma mantissa_nonneg (C : FloatCfg) (q : ℚ) (q_nezero : q ≠ 0) :
  0 ≤ (|q| * ((2 : ℚ)^Int.log 2 |q|)⁻¹ - 1) * C.prec := by
  apply mul_nonneg
  · linarith [(mantissa_size_aux q q_nezero).1]
  exact_mod_cast le_of_lt C.prec_pos

lemma casesQPlane (P : ℚ → ℚ → Prop)
  (h1 : ∀ q1 > 0, ∀ q2 > 0, P q1 q2)
  (h2 : ∀ q1 < 0, ∀ q2 > 0, P q1 q2)
  (h3 : ∀ q1 > 0, ∀ q2 < 0, P q1 q2)
  (h4 : ∀ q1 < 0, ∀ q2 < 0, P (-q1) (-q2) → P q2 q1) (q1 q2 : ℚ)
  (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) : P q1 q2 := by
  have h : ∀q ≠ (0 : ℚ), q > 0 ∨ q < 0 := by
    intro q qnezero
    by_cases h : q > 0
    · exact Or.inl h
    exact lt_or_gt_of_ne (Ne.symm qnezero)
  rcases (h q1 q1_nezero) with h' | h'
  · rcases (h q2 q2_nezero) with h'' | h''
    · exact h1 q1 h' q2 h''
    exact h3 q1 h' q2 h''
  · rcases (h q2 q2_nezero) with h'' | h''
    · exact h2 q1 h' q2 h''
    apply h4 q2 h'' q1 h'
    apply h1
    · exact Left.neg_pos_iff.mpr h''
    exact Left.neg_pos_iff.mpr h'
