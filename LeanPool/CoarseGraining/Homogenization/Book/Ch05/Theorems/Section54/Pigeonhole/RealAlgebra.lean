/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Common

/-! # Real Algebra -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace Pigeonhole

noncomputable section

/-!
# Real-variable staging for the Section 5.4 pigeonhole lemma

The final pigeonhole proof needs a small logarithmic estimate for the chosen
number of scale steps.  This file is reserved for that pure real algebra,
separate from the law-facing scalar-chain input.
-/

/-- The logarithmic scale count used in the pigeonhole lemma makes the
exponential tail at most `sigma`. -/
theorem exp_neg_half_delta_mul_natCeil_two_delta_inv_abs_log_le
    {delta sigma : ℝ} (hdelta_pos : 0 < delta)
    (hsigma_pos : 0 < sigma) (hsigma_le_one : sigma ≤ 1) :
    Real.exp
        (-((1 / 2 : ℝ) * delta *
          (Nat.ceil (2 * delta⁻¹ * |Real.log sigma|) : ℝ))) ≤ sigma := by
  let k : ℕ := Nat.ceil (2 * delta⁻¹ * |Real.log sigma|)
  have hceil : 2 * delta⁻¹ * |Real.log sigma| ≤ (k : ℝ) := by
    simpa [k] using Nat.le_ceil (2 * delta⁻¹ * |Real.log sigma|)
  have hhalf_delta_pos : 0 < (1 / 2 : ℝ) * delta := by positivity
  have hlog_nonpos : Real.log sigma ≤ 0 :=
    Real.log_nonpos hsigma_pos.le hsigma_le_one
  have habs_log : |Real.log sigma| = -Real.log sigma :=
    abs_of_nonpos hlog_nonpos
  have hscale :
      ((1 / 2 : ℝ) * delta) * (2 * delta⁻¹ * |Real.log sigma|) =
        |Real.log sigma| := by
    field_simp [hdelta_pos.ne']
  have hlog_abs_le :
      |Real.log sigma| ≤ ((1 / 2 : ℝ) * delta) * (k : ℝ) := by
    calc
      |Real.log sigma| =
          ((1 / 2 : ℝ) * delta) * (2 * delta⁻¹ * |Real.log sigma|) :=
        hscale.symm
      _ ≤ ((1 / 2 : ℝ) * delta) * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hceil hhalf_delta_pos.le
  have hlog_bound :
      -(((1 / 2 : ℝ) * delta) * (k : ℝ)) ≤ Real.log sigma := by
    have hneg := neg_le_neg hlog_abs_le
    simpa [habs_log] using hneg
  rw [← Real.exp_log hsigma_pos]
  exact Real.exp_le_exp.mpr (by simpa [k, mul_assoc] using hlog_bound)

/-- The elementary estimate `(1 + δ)⁻¹ ≤ exp (-δ / 2)` on the range used by
the pigeonhole lemma. -/
theorem inv_one_add_delta_le_exp_neg_half
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 2) :
    (1 + delta)⁻¹ ≤ Real.exp (-((1 / 2 : ℝ) * delta)) := by
  have hlog_low : (1 / 2 : ℝ) * delta ≤ Real.log (1 + delta) := by
    have hmain := Real.le_log_one_add_of_nonneg hdelta_nonneg
    have hden_pos : 0 < delta + 2 := by positivity
    have hhalf_le : (1 / 2 : ℝ) * delta ≤ 2 * delta / (delta + 2) := by
      rw [le_div_iff₀ hden_pos]
      nlinarith
    exact le_trans hhalf_le hmain
  have hbase_pos : 0 < 1 + delta := by positivity
  calc
    (1 + delta)⁻¹ = (Real.exp (Real.log (1 + delta)))⁻¹ := by
      rw [Real.exp_log hbase_pos]
    _ = Real.exp (-Real.log (1 + delta)) := by
      rw [Real.exp_neg]
    _ ≤ Real.exp (-((1 / 2 : ℝ) * delta)) :=
      Real.exp_le_exp.mpr (neg_le_neg hlog_low)

/-- Iterated version of `inv_one_add_delta_le_exp_neg_half`. -/
theorem inv_one_add_delta_pow_le_exp_neg_half_mul
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 2) (k : ℕ) :
    ((1 + delta)⁻¹) ^ k ≤
      Real.exp (-((1 / 2 : ℝ) * delta * (k : ℝ))) := by
  have hbase := inv_one_add_delta_le_exp_neg_half hdelta_nonneg hdelta_le
  calc
    ((1 + delta)⁻¹) ^ k ≤ Real.exp (-((1 / 2 : ℝ) * delta)) ^ k :=
      pow_le_pow_left₀ (by positivity : 0 ≤ (1 + delta)⁻¹) hbase k
    _ = Real.exp (-((1 / 2 : ℝ) * delta * (k : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The manuscript scale count makes the repeated `(1 + δ)⁻¹` loss no larger
than `σ`. -/
theorem inv_one_add_delta_pow_natCeil_two_delta_inv_abs_log_le
    {delta sigma : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    (hsigma_pos : 0 < sigma) (hsigma_le_one : sigma ≤ 1) :
    ((1 + delta)⁻¹) ^ Nat.ceil (2 * delta⁻¹ * |Real.log sigma|) ≤ sigma := by
  have hpow :=
    inv_one_add_delta_pow_le_exp_neg_half_mul hdelta_pos.le hdelta_le
      (Nat.ceil (2 * delta⁻¹ * |Real.log sigma|))
  have hexp :=
    exp_neg_half_delta_mul_natCeil_two_delta_inv_abs_log_le
      hdelta_pos hsigma_pos hsigma_le_one
  exact le_trans hpow hexp

end

end Pigeonhole
end Section54
end Ch05
end Book
end Homogenization
