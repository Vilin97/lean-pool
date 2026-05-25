/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import LeanPool.PentagonalNumberTheorem.Generic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.RCLike.Basic

/-!

# Pentagonal number theorem for real/complex numbers

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
for real/complex numbers.

-/

open Filter
variable {K : Type*} [RCLike K]

namespace Pentagonal

theorem gamma_bound (k n : ℕ) {x : K} (hx : ‖x‖ < 1) :
    ‖gamma k n x‖ ≤ ‖x‖ ^ ((k + 1) * n) * ∏' i, (1 + ‖x‖ ^ i) := by
  unfold gamma
  rw [norm_mul, norm_prod, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  trans ∏ i ∈ Finset.Ico (k + 1) (n + 1 + (k + 1)), (1 + ‖x‖ ^ i)
  · rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    apply Finset.prod_le_prod (by simp) fun _ _ ↦ (norm_sub_le _ _).trans_eq ?_
    rw [norm_one, norm_pow]
    ring
  have : Multipliable (1 + ‖x‖ ^ ·) := multipliable_one_add_of_summable (by simpa using hx)
  apply ge_of_tendsto (this.tendsto_prod_tprod_nat)
  rw [eventually_atTop]
  refine ⟨n + 1 + (k + 1), fun a ha ↦ ?_⟩
  have : Finset.Ico (k + 1) (n + 1 + (k + 1)) ⊆ Finset.range a := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_subset_Ico (by simp) ha
  rw [← Finset.prod_sdiff this]
  apply le_mul_of_one_le_left (Finset.prod_nonneg (fun _ _ ↦ by trans 1 <;> simp))
  generalize Finset.range a \ Finset.Ico (k + 1) (n + 1 + (k + 1)) = s
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s h ih =>
    rw [Finset.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (by simp) ih

theorem summable_gamma_complex (k : ℕ) {x : K} (hx : ‖x‖ < 1) : Summable (gamma k · x) := by
  rw [← summable_norm_iff]
  refine Summable.of_nonneg_of_le (by simp) (gamma_bound k · hx) <| Summable.mul_right _ ?_
  simp_rw [pow_mul]
  apply summable_geometric_of_lt_one (by simp)
  exact (pow_lt_one_iff_of_nonneg (by simp) (by simp)).mpr hx

theorem tsum_gamma_bound (k : ℕ) {x : K} (hx : ‖x‖ < 1) :
    ‖∑' n, gamma k n x‖ ≤ (1 - ‖x‖)⁻¹ * ∏' i, (1 + ‖x‖ ^ i) := by
  obtain hsum := (summable_gamma_complex k hx).norm
  have hx' : ‖x‖ ^ (k + 1) < 1 := (pow_lt_one_iff_of_nonneg (by simp) (by simp)).mpr hx
  apply (norm_tsum_le_tsum_norm hsum).trans
  refine (Summable.tsum_le_tsum (gamma_bound k · hx) hsum ?_).trans ?_
  · simp_rw [pow_mul]
    exact Summable.mul_right _ <| summable_geometric_of_lt_one (by simp) hx'
  rw [tsum_mul_right]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · simp_rw [pow_mul]
    rw [tsum_geometric_of_lt_one (by simp) hx']
    rw [inv_le_inv₀ (by simpa using hx') (by simpa using hx), sub_le_sub_iff_left]
    exact pow_le_of_le_one (by simp) hx.le (by simp)
  -- hx : ‖x‖ < 1
  -- ⊢ 0 ≤ ∏' (i : ℕ), (1 + ‖x‖ ^ i)
  rw [← Real.rexp_tsum_eq_tprod (fun _ ↦ (show (0 : ℝ) < 1 by simp).trans_le (by simp)) (
    Real.summable_log_one_add_of_summable <| by simpa using hx)]
  apply Real.exp_nonneg

theorem multipliable_pentagonalLhs_complex' (k : ℕ) {x : K} (hx : ‖x‖ < 1) :
    Multipliable (fun n ↦ 1 - x ^ (n + k + 1)) := by
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_summable
  simp_rw [norm_neg, norm_pow, pow_add]
  apply ((summable_geometric_of_lt_one (by simp) hx).mul_right _).mul_right

end Pentagonal

open Pentagonal

theorem multipliable_pentagonalLhs_complex {x : K} (hx : ‖x‖ < 1) :
    Multipliable (fun n ↦ 1 - x ^ (n + 1)) := by
  simpa using multipliable_pentagonalLhs_complex' 0 hx

theorem summable_pentagonalRhs_complex {x : K} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℕ) ↦
    ((-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)))) := by
  simp_rw [mul_sub]
  refine Summable.sub ?_ ?_
  <;> rw [← summable_norm_iff]
  <;> simp_rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  <;> refine Summable.of_nonneg_of_le (by simp) ?_ (summable_geometric_of_lt_one (by simp) hx)
  <;> refine fun k ↦ pow_le_pow_of_le_one (by simp) (hx.le) ?_
  · obtain rfl | h0 := Nat.eq_zero_or_pos k
    · simp
    rw [Nat.le_div_iff_mul_le (by simp)]
    exact Nat.mul_le_mul_left _ (by linarith)
  · rw [Nat.le_div_iff_mul_le (by simp)]
    exact Nat.mul_le_mul (by simp) (by simp)

/-- **Pentagonal number theorem** for real/complex numbers, summation over natural numbers.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} + x^{(k+1)(3k+2)/2}\right) $$ -/
theorem pentagonalNumberTheorem_complex {x : K} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' k, (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)) := by
  refine pentagonalNumberTheorem_generic ?_ ?_ ?_ ?_ ?_
  · exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx
  · exact (summable_gamma_complex · hx)
  · exact (multipliable_pentagonalLhs_complex' · hx)
  · exact summable_pentagonalRhs_complex hx
  · apply Filter.Tendsto.zero_mul_isBoundedUnder_le
    · apply Filter.isBoundedUnder_le_mul_tendsto_zero ⟨1, by simp⟩
      apply (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx).comp
      rw [Filter.tendsto_atTop_atTop]
      refine fun k ↦ ⟨k, fun n hn ↦ hn.trans ?_⟩
      rw [Nat.le_div_iff_mul_le (by simp)]
      exact Nat.mul_le_mul (by simp) (by simp)
    · use (1 - ‖x‖)⁻¹ * ∏' i, (1 + ‖x‖ ^ i)
      simp_rw [eventually_map, Function.comp_apply, eventually_atTop]
      exact ⟨0, fun k _ ↦ tsum_gamma_bound k hx⟩

theorem summable_pentagonalRhs_intNeg_complex {x : K} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℤ) ↦ (-1) ^ k * x ^ (k * (3 * k + 1) / 2)) := by
  apply Summable.of_add_one_of_neg_add_one
  all_goals
  rw [← summable_norm_iff]
  simp_rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  refine Summable.of_nonneg_of_le (fun k ↦ by apply zpow_nonneg (by simp)) (fun k ↦ ?_)
    (summable_geometric_of_lt_one (by simp) hx)
  rw [← zpow_natCast]
  obtain h0 | h0 := eq_or_lt_of_le (norm_nonneg x)
  · simp_rw [← h0]
    obtain rfl | hk0 := eq_or_ne k 0
    · norm_num
    rw [zero_zpow _ ?_, zero_zpow _ (by simpa using hk0)]
    grind
  apply zpow_le_zpow_right_of_le_one₀ h0 hx.le
  grind

/-- **Pentagonal number theorem** for real/complex numbers, summation over integers, opposite order.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k + 1)/2} $$ -/
theorem pentagonalNumberTheorem_intNeg_complex {x : K} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' (k : ℤ), (-1) ^ k * x ^ (k * (3 * k + 1) / 2) := by
  rw [← tsum_nat_add_neg_add_one (summable_pentagonalRhs_intNeg_complex hx),
    pentagonalNumberTheorem_complex hx]
  refine tsum_congr fun k ↦ ?_
  rw [sub_eq_add_neg _ (x ^ _), mul_add, ← neg_mul_comm]
  congrm $(by norm_cast) * $(by norm_cast) + ?_ * ?_
  · trans (-1) ^ (k + 1)
    · ring
    · rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
      norm_cast
  · rw [← zpow_natCast]
    congr

theorem summable_pentagonalRhs_intPos_complex {x : K} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℤ) ↦ (-1) ^ k * x ^ (k * (3 * k - 1) / 2)) := by
  rw [← neg_injective.summable_iff (by intro x hx; contrapose! hx; use -x; simp)]
  convert summable_pentagonalRhs_intNeg_complex hx
  rw [Function.comp_apply]
  congrm ?_ * x ^ ($(by ring_nf) / 2)
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

/-- **Pentagonal number theorem** for real/complex numbers, summation over integers, classic order.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k - 1)/2} $$ -/
theorem pentagonalNumberTheorem_intPos_complex {x : K} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' (k : ℤ), (-1) ^ k * x ^ (k * (3 * k - 1) / 2) := by
  rw [pentagonalNumberTheorem_intNeg_complex hx, ← neg_injective.tsum_eq (by simp)]
  refine tsum_congr fun k ↦ ?_
  congrm ?_ * x ^ ($(by ring_nf) / 2)
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
