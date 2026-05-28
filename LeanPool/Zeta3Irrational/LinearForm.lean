/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import LeanPool.Zeta3Irrational.Integral
import LeanPool.Zeta3Irrational.D

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators

lemma d_cube_ne_zero {r : ℕ} : ((d (Finset.Icc 1 r) ^ 3) : ℝ) ≠ (0 : ℝ) := by
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
  apply d_ne_zero; simp

lemma J_rr_linear (r : ℕ) :
    ∃ a : ℤ,
      J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
        a / (d (Finset.Icc 1 r)) ^ 3 := by
  if h : r = 0 then
    rw [h, zeta_3]; use 0; simp
  else
    rw [J_rr]
    simp only [sub_right_inj]
    simp_rw [eq_div_iff d_cube_ne_zero, Finset.mul_sum, Finset.sum_mul]
    use ∑ i ∈ Finset.Icc 1 r, 2 * ↑(d (Finset.Icc 1 r)) ^ 3 / ↑i ^ 3
    simp only [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_assoc]
    nth_rewrite 2 [mul_comm]
    rw [mul_one_div, Int.cast_div]
    · simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, mul_div_assoc']
    · rw [← Nat.cast_pow, ← Nat.cast_pow, d_cube', Nat.cast_pow]
      apply Dvd.dvd.mul_left
      norm_cast
      apply dvd_d_of_mem
      simp_all
    · simp_all only [Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
      linarith

lemma Icc_diff_Icc {r s : ℕ} (_ : r > s) (_ : ¬s = 0) :
    Finset.Icc 1 r \ Finset.Icc 1 s = Finset.Icc (s + 1) r := by
  ext x
  constructor
  · intro hx
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le, and_true]
    exact LT.lt.nat_succ_le (hx.2 hx.1.1)
  · intro hx
    simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_sdiff, and_true, not_and, not_le]
    constructor
    · linarith
    · intro
      linarith

lemma one_div_sum_eq {r s : ℕ} (h : r > s) :
    ∑ m ∈ Finset.Icc 1 r, (1 / m ^ 2 : ℝ) - ∑ m ∈ Finset.Icc 1 s, (1 / m ^ 2 : ℝ) =
    ∑ m ∈ Finset.Icc 1 (r - s), (1 / (s + m) ^ 2 : ℝ) := by
  rw [← Finset.sum_sdiff_eq_sub]
  · if h1 : s = 0 then
      simp_all
    else
      simp_rw [← Nat.cast_add]
      rw [Icc_diff_Icc h h1, ← Nat_Ico_succ_right, ← Nat_Ico_succ_right,
        Finset.sum_Ico_add (f := fun (x : ℕ) => 1 / ((x ^ 2) : ℝ)) (c := s),
        show s + 1 = 1 + s by omega, show r - s + 1 + s = r + 1 by omega]
  · exact Finset.Icc_subset_Icc_right (LT.lt.le (gt_iff_lt.1 h))

lemma J_rs_linear {r s : ℕ} (h : r > s) : ∃ a : ℤ, J r s = a / (d (Finset.Icc 1 r)) ^ 3 := by
  rw [J_rs (by linarith)]
  simp_rw [eq_div_iff d_cube_ne_zero, one_div_sum_eq h]
  use (∑ m ∈ Finset.Icc 1 (r - s), (d (Finset.Icc 1 r)) ^ 2 / (s + m) ^ 2 *
    (d (Finset.Icc 1 r)) / (r - s))
  rw [Finset.sum_div, Finset.sum_mul, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 3 = 1 + 2 by omega, pow_add, pow_one, mul_comm, mul_assoc, mul_div_assoc', mul_one_div,
    mul_div_assoc', mul_comm, ← mul_div_assoc', Int.cast_div]
  · rw [Int.cast_mul, Int.cast_div]
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, Int.cast_add,
      Int.cast_sub]
      rw [mul_div_assoc']
    · norm_cast
      rw [d_sq']
      apply dvd_d_of_mem
      simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_image, zero_le, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀, exists_eq_right]
      omega
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_add, Int.cast_natCast,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      rw [← Nat.cast_add]
      norm_cast; omega
  · apply Dvd.dvd.mul_left
    rw [← Nat.cast_sub (by linarith)]
    norm_cast
    apply dvd_d_of_mem
    simp_all only [gt_iff_lt, Finset.mem_Icc, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
      and_true]
    linarith
  · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_sub, Int.cast_natCast]
    rw [← Nat.cast_sub (by linarith)]
    norm_cast; linarith

lemma multi_integral_sum_comm (c : ℕ → ℤ) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
    -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
      ↑(c x_2) * x.2 ^ x_2
    = ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
      ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
        ↑(c x_2) * x.2 ^ x_2 := by
    symm
    calc
    _ = ∑ x_1 ∈ Finset.range (n + 1),
      ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ∑ x_2 ∈ Finset.range (n + 1),
      -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
        ↑(c x_2) * x.2 ^ x_2 := by
      congr! 1 with a _
      rw [← MeasureTheory.integral_finset_sum]
      intro i _
      have h :
          (fun (x : ℝ × ℝ) ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) *
            ↑(c a) * x.1 ^ a * ↑(c i) * x.2 ^ i) =
          fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) *
            x.1 ^ a * x.2 ^ i * (↑(c i) * ↑(c a)) := by
        ext x; ring
      rw [h]
      apply MeasureTheory.Integrable.mul_const
      exact integrableOn_J_rs a i
    _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
      -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
        ↑(c x_2) * x.2 ^ x_2 := by
      rw [← MeasureTheory.integral_finset_sum]
      intro i _
      apply MeasureTheory.integrable_finset_sum
      intro j _
      have h :
          (fun (x : ℝ × ℝ) ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) *
            ↑(c i) * x.1 ^ i * ↑(c j) * x.2 ^ j) =
          fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) *
            x.1 ^ i * x.2 ^ j * (↑(c i) * ↑(c j)) := by
        ext x; ring
      rw [h]
      apply MeasureTheory.Integrable.mul_const
      exact integrableOn_J_rs i j

lemma multi_integral_mul_const (c d : ℕ) (p q : ℝ) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      -(x.1 * x.2).log / (1 - x.1 * x.2) * p * x.1 ^ c * q * x.2 ^ d =
    p * q * J c d := by
  simp only [J]
  symm
  rw [mul_comm, ← smul_eq_mul, ← integral_smul_const]
  apply MeasureTheory.setIntegral_congr_fun (by measurability)
  intro x _
  simp only [smul_eq_mul]
  ring

/-- The integer coefficient of the rational part of `J r s`. -/
noncomputable def p (r s : ℕ) : ℤ :=
  if h : r > s then (J_rs_linear h).choose
  else if h : r < s then (J_rs_linear h).choose
  else -(J_rr_linear r).choose

/-- The integer coefficient of the zeta part of `J r s`. -/
noncomputable def q (r s : ℕ) : ℤ :=
  if r > s then 0
  else if r < s then 0
  else 2

lemma J_symm (r s : ℕ) : J r s = J s r := by
  if h : r = s then rw [h]
  else
    rw [J_rs (by tauto), J_rs (by tauto), ← neg_div_neg_eq]; ring

lemma linear_int_aux : ∃ a b : ℕ → ℕ → ℤ, ∀ r s : ℕ, J r s =
    b r s * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 +
      a r s / (d (Finset.Icc 1 (Nat.max r s))) ^ 3 := by
  use p
  use q
  intro x y
  if h : x > y then
    rcases J_rs_linear h with ⟨a, ha⟩
    simp only [p, q]
    simp_all only [gt_iff_lt, one_div, ite_true, Int.cast_zero, zero_mul, dite_true,
      zero_add]
    rw [(J_rs_linear h).choose_spec] at ha
    rw [show x.max y = x by exact max_eq_left_iff.2 (LT.lt.le h)]
    simp_all
  else if h1 : x < y then
    rcases J_rs_linear h1 with ⟨a, ha⟩
    simp only [p, q]
    obtain h2 := J_symm x y
    simp_all only [gt_iff_lt, one_div, ite_true, ite_self, Int.cast_zero, zero_mul, dite_true,
      zero_add, dite_false]
    rw [(J_rs_linear h1).choose_spec] at ha
    simp only [not_lt] at h
    simp_all
  else
    have h : x = y := by linarith
    rcases J_rr_linear y with ⟨a, ha⟩
    simp only [p, q]
    simp_all only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, ite_false,
      Int.cast_ofNat, not_isEmpty_of_nonempty, tsum_empty, mul_zero, zero_sub, sub_right_inj,
      dite_false, Int.cast_neg, max_self]
    rw [(J_rr_linear y).choose_spec, ← Mathlib.Tactic.RingNF.add_neg, ← neg_div] at ha
    simp_all

end LeanPool.Zeta3Irrational
