/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Clemens Posch
-/
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
Numeric inequalities for Tran–Vu’s covering induction (`L = 1000`).
-/

namespace KahnKalai

open Nat Finset

/-- Least integer strictly larger than `0.9 ℓ`. -/
noncomputable def kmin (ℓ : ℕ) : ℕ := ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1

lemma kmin_pos (ℓ : ℕ) : 1 ≤ kmin ℓ := Nat.succ_le_succ (Nat.zero_le _)

lemma kmin_gt (ℓ : ℕ) : ((9 : ℝ) / 10) * ℓ < kmin ℓ := by
  unfold kmin
  have := Nat.lt_floor_add_one (((9 : ℝ) / 10) * (ℓ : ℝ))
  simpa [add_comm] using this

lemma kmin_le_add_one (ℓ : ℕ) : (kmin ℓ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ + 1 := by
  unfold kmin
  have hnn : 0 ≤ ((9 : ℝ) / 10) * (ℓ : ℝ) := by positivity
  have hf : (⌊((9 : ℝ) / 10) * ℓ⌋₊ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ := Nat.floor_le hnn
  push_cast
  linarith

lemma kmin_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : kmin ℓ ≤ ℓ := by
  by_cases h : ℓ ≤ 9
  · interval_cases ℓ <;> unfold kmin <;> norm_num
  · have hk := kmin_le_add_one ℓ
    have h10 : (10 : ℝ) ≤ ℓ := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h) : 10 ≤ ℓ)
    have : ((9 : ℝ) / 10) * ℓ + 1 ≤ ℓ := by nlinarith
    exact_mod_cast hk.trans this

lemma eleven_mul_kmin_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    11 * kmin ℓ ≤ 10 * (ℓ + 1) := by
  by_cases h : ℓ ≤ 9
  · interval_cases ℓ <;> unfold kmin <;> norm_num
  · have hk : (kmin ℓ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ + 1 := kmin_le_add_one ℓ
    have h10 : (10 : ℝ) ≤ ℓ := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h) : 10 ≤ ℓ)
    have h' : (11 : ℝ) * (((9 : ℝ) / 10) * ℓ + 1) ≤ 10 * (ℓ + 1) := by nlinarith
    have : (11 : ℝ) * kmin ℓ ≤ 10 * (ℓ + 1) :=
      (mul_le_mul_of_nonneg_left hk (by norm_num)).trans h'
    exact_mod_cast this

lemma two_rpow_one_div_ten_le :
    (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ (11 : ℝ) / 10 := by
  have hpos : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (by norm_num) _
  have h10 : ((2 : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) ≤ ((11 : ℝ) / 10) ^ (10 : ℕ) := by
    have lhs : ((2 : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have rhs : ((11 : ℝ) / 10) ^ (10 : ℕ) = 11 ^ 10 / 10 ^ 10 := div_pow _ _ _
    rw [lhs, rhs]
    exact (le_div_iff₀ (by positivity)).mpr (by norm_num)
  exact (pow_le_pow_iff_left₀ hpos (by positivity) (by norm_num)).1 h10

lemma fifty_pow_le_hundred_rpow :
    (50 : ℝ) ≤ (100 : ℝ) ^ ((9 : ℝ) / 10) := by
  have hpow : (50 : ℝ) ^ (10 : ℕ) ≤ (100 : ℝ) ^ (9 : ℕ) := by norm_num
  have h50 : (50 : ℝ) = ((50 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h100 : ((100 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 10) = (100 : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hle : ((50 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10)
      ≤ ((100 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow (by positivity) hpow (by positivity)
  calc
    (50 : ℝ) = ((50 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := h50
    _ ≤ ((100 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 10) := hle
    _ = (100 : ℝ) ^ ((9 : ℝ) / 10) := h100

lemma fifty_pow_le_hundred_kmin (ℓ : ℕ) :
    (50 : ℝ) ^ ℓ ≤ (100 : ℝ) ^ kmin ℓ := by
  have h1 : (50 : ℝ) ^ ℓ ≤ ((100 : ℝ) ^ ((9 : ℝ) / 10)) ^ ℓ :=
    pow_le_pow_left₀ (by positivity) fifty_pow_le_hundred_rpow ℓ
  have h2 : ((100 : ℝ) ^ ((9 : ℝ) / 10)) ^ ℓ = (100 : ℝ) ^ (((9 : ℝ) / 10) * ℓ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm]
  have h3 : (100 : ℝ) ^ (((9 : ℝ) / 10) * ℓ) ≤ (100 : ℝ) ^ (kmin ℓ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt (kmin_gt ℓ))
  have h4 : (100 : ℝ) ^ (kmin ℓ : ℝ) = (100 : ℝ) ^ kmin ℓ := Real.rpow_natCast _ _
  calc
    (50 : ℝ) ^ ℓ ≤ ((100 : ℝ) ^ ((9 : ℝ) / 10)) ^ ℓ := h1
    _ = (100 : ℝ) ^ (((9 : ℝ) / 10) * ℓ) := h2
    _ ≤ (100 : ℝ) ^ (kmin ℓ : ℝ) := h3
    _ = (100 : ℝ) ^ kmin ℓ := h4

lemma fortyfour_eight_le_three_fifty (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (44 : ℝ) * 8 ^ ℓ ≤ 3 * 50 ^ ℓ := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h8 : (8 : ℝ) ≤ 50 := by norm_num
    calc
      (44 : ℝ) * 8 ^ (n + 1) = 8 * (44 * 8 ^ n) := by ring
      _ ≤ 50 * (3 * 50 ^ n) := mul_le_mul h8 ih (by positivity) (by positivity)
      _ = 3 * 50 ^ (n + 1) := by ring

lemma eleven_two_pow_le_twelve_fifty (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (11 : ℝ) * 2 ^ (3 * ℓ + 4) ≤ 12 * 50 ^ ℓ := by
  have h := fortyfour_eight_le_three_fifty ℓ hℓ
  have hpow : (2 : ℝ) ^ (3 * ℓ + 4) = 16 * 8 ^ ℓ := by
    calc
      (2 : ℝ) ^ (3 * ℓ + 4) = 2 ^ (4 + 3 * ℓ) := by ring_nf
      _ = 2 ^ 4 * 2 ^ (3 * ℓ) := pow_add _ _ _
      _ = 16 * (2 ^ 3) ^ ℓ := by
        rw [pow_mul]
        norm_num
      _ = 16 * 8 ^ ℓ := by norm_num
  have : (11 : ℝ) * 16 * 8 ^ ℓ ≤ 12 * 50 ^ ℓ := by
    have h' : (176 : ℝ) * 8 ^ ℓ ≤ 12 * 50 ^ ℓ := by
      have : (176 : ℝ) * 8 ^ ℓ = (4 : ℝ) * (44 * 8 ^ ℓ) := by ring
      have : (12 : ℝ) * 50 ^ ℓ = 4 * (3 * 50 ^ ℓ) := by ring
      nlinarith
    convert h' using 1
    ring
  rw [hpow]
  convert this using 1
  ring

lemma eleven_two_pow_le_twelve_hundred (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (11 : ℝ) * 2 ^ (3 * ℓ + 4) ≤ 12 * 100 ^ kmin ℓ :=
  (eleven_two_pow_le_twelve_fifty ℓ hℓ).trans <|
    mul_le_mul_of_nonneg_left (fifty_pow_le_hundred_kmin ℓ) (by positivity)

lemma choose_geom_tail_le (ℓ : ℕ) :
    ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k
      ≤ ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ := by
  have hsum :
      ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k
        ≤ ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ kmin ℓ * ℓ.choose k := by
    refine sum_le_sum ?_
    intro k hk
    have hk' : kmin ℓ ≤ k := (mem_Icc.mp hk).1
    have hpow : ((1 : ℝ) / 100) ^ k ≤ ((1 : ℝ) / 100) ^ kmin ℓ :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) hk'
    exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hre : ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ kmin ℓ * ℓ.choose k
      = ((1 : ℝ) / 100) ^ kmin ℓ * ∑ k ∈ Icc (kmin ℓ) ℓ, (ℓ.choose k : ℝ) := by
    simp [mul_sum]
  have hchoose : ∑ k ∈ Icc (kmin ℓ) ℓ, (ℓ.choose k : ℝ)
      ≤ ∑ k ∈ range (ℓ + 1), (ℓ.choose k : ℝ) := by
    refine sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro k hk
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
    · intro _ _ _; exact Nat.cast_nonneg _
  have hbin : ∑ k ∈ range (ℓ + 1), (ℓ.choose k : ℝ) = (2 : ℝ) ^ ℓ := by
    simpa using congrArg (fun n : ℕ => (n : ℝ)) (sum_range_choose ℓ)
  calc
    ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k
        ≤ ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ kmin ℓ * ℓ.choose k := hsum
    _ = ((1 : ℝ) / 100) ^ kmin ℓ * ∑ k ∈ Icc (kmin ℓ) ℓ, (ℓ.choose k : ℝ) := hre
    _ ≤ ((1 : ℝ) / 100) ^ kmin ℓ * ∑ k ∈ range (ℓ + 1), (ℓ.choose k : ℝ) :=
      mul_le_mul_of_nonneg_left hchoose (by positivity)
    _ = ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ := by rw [hbin]

lemma bad_frac_le_of_two (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ * 2 ^ (ℓ + 2)
      ≤ (12 / 11) * (1 / (2 : ℝ) ^ (ℓ + 2)) := by
  have h := eleven_two_pow_le_twelve_hundred ℓ hℓ
  have hA : (0 : ℝ) < (100 : ℝ) ^ kmin ℓ := by positivity
  have hE : (0 : ℝ) < (2 : ℝ) ^ (ℓ + 2) := by positivity
  have hD : (0 : ℝ) < (11 : ℝ) := by norm_num
  have hpow : ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ * 2 ^ (ℓ + 2)
      = ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ (2 * ℓ + 2) := by
    have : (2 : ℝ) ^ ℓ * 2 ^ (ℓ + 2) = 2 ^ (2 * ℓ + 2) := by
      rw [← pow_add]; ring_nf
    ring
  rw [hpow, one_div_pow]
  have : (2 : ℝ) ^ (2 * ℓ + 2) / 100 ^ kmin ℓ
      ≤ 12 / (11 * 2 ^ (ℓ + 2)) := by
    rw [div_le_div_iff₀ hA (mul_pos hD hE)]
    have hexp : (2 : ℝ) ^ (2 * ℓ + 2) * (11 * 2 ^ (ℓ + 2)) = 11 * 2 ^ (3 * ℓ + 4) := by
      have : (2 : ℝ) ^ (2 * ℓ + 2) * 2 ^ (ℓ + 2) = 2 ^ (3 * ℓ + 4) := by
        rw [← pow_add]; ring_nf
      ring
    simpa [hexp] using h
  convert this using 1
  · ring
  · field_simp

lemma bad_frac_le_one :
    ((1 : ℝ) / 100) * 2 ^ (1 + 2) ≤ (12 / 11) * (1 / (2 : ℝ) ^ (1 + 2)) := by
  norm_num

lemma frac_gap (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (1 : ℝ) / 2 ^ (ℓ + 2) ≤ 1 / 2 ^ (kmin ℓ - 1 + 2) - 1 / 2 ^ (ℓ + 2) := by
  have hk : kmin ℓ ≤ ℓ := kmin_le ℓ hℓ
  have hle : kmin ℓ - 1 + 2 ≤ ℓ + 1 := by omega
  have hpow : (2 : ℝ) ^ (kmin ℓ - 1 + 2) ≤ 2 ^ (ℓ + 1) :=
    pow_le_pow_right₀ (by norm_num) hle
  have hle' : (1 : ℝ) / 2 ^ (ℓ + 1) ≤ 1 / 2 ^ (kmin ℓ - 1 + 2) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have h2 : (1 : ℝ) / 2 ^ (ℓ + 1) = 2 * (1 / 2 ^ (ℓ + 2)) := by
    have : (2 : ℝ) ^ (ℓ + 2) = 2 ^ (ℓ + 1) * 2 := pow_succ _ _
    field_simp [this]
    ring
  have hle'' : 2 * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤ 1 / 2 ^ (kmin ℓ - 1 + 2) := by
    simpa [h2] using hle'
  linarith

lemma two_div_three_add_le :
    (2 : ℝ) / 3 + 1 / 2 ^ (0 + 2) ≤ (11 : ℝ) / 12 := by
  norm_num

lemma occupation_mul_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {β : ℝ}
    (hβ : β ≤ (12 / 11) * (1 / (2 : ℝ) ^ (ℓ + 2))) :
    (2 / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) ≤
      ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (kmin ℓ - 1 + 2)) * (1 - β) := by
  set a : ℝ := (2 : ℝ) / 3
  set b : ℝ := 1 / (2 : ℝ) ^ (kmin ℓ - 1 + 2)
  set d : ℝ := 1 / (2 : ℝ) ^ (ℓ + 2)
  have hb0 : 0 ≤ b := by positivity
  have hd0 : 0 ≤ d := by positivity
  have ha0 : 0 < a := by norm_num [a]
  have hgap : d ≤ b - d := frac_gap ℓ hℓ
  have hb_le : b ≤ (1 : ℝ) / 4 := by
    have : 2 ≤ kmin ℓ - 1 + 2 := by
      have := kmin_pos ℓ
      omega
    have : (2 : ℝ) ^ (2 : ℕ) ≤ 2 ^ (kmin ℓ - 1 + 2) :=
      pow_le_pow_right₀ (by norm_num) this
    have : (1 : ℝ) / 2 ^ (kmin ℓ - 1 + 2) ≤ 1 / 4 := by
      have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
      simpa [h4] using one_div_le_one_div_of_le (by positivity) this
    simpa [b] using this
  have hab : a + b ≤ (11 : ℝ) / 12 := by
    have : a + 1 / 4 = (11 : ℝ) / 12 := by norm_num [a]
    linarith
  have hden : (0 : ℝ) < a + b := add_pos_of_pos_of_nonneg ha0 hb0
  have hfrac : (12 / 11) * d ≤ (b - d) / (a + b) := by
    have hde : (0 : ℝ) < (11 : ℝ) / 12 := by norm_num
    have h1 : d / ((11 : ℝ) / 12) ≤ (b - d) / (a + b) :=
      div_le_div₀ (le_trans hd0 hgap) hgap hden hab
    have h2 : d / ((11 : ℝ) / 12) = (12 / 11) * d := by field_simp
    simpa [h2] using h1
  have hc : β ≤ (b - d) / (a + b) := hβ.trans (by simpa [d] using hfrac)
  have hmul : β * (a + b) ≤ b - d := (le_div_iff₀ hden).mp hc
  have : a + d ≤ (a + b) * (1 - β) := by nlinarith
  simpa [a, b, d] using this

end KahnKalai
