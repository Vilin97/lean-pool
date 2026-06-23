/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import LeanPool.LeanModularForms.Modularforms.JacobiTheta
public import LeanPool.LeanModularForms.Modularforms.AtImInfty

/-! # QExpansion -/


@[expose] public section

/-!
# Limits at infinity

In this file we establishes basic results about q-expansions. The results are put under the `QExp`
namespace.

TODO:
* Are any of these results in Mathlib, perhaps phrased in some other way?
-/

open scoped Real
open UpperHalfPlane hiding I
open Complex Asymptotics Topology Filter

namespace QExp

lemma tendsto_nat (a : ℕ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (-2 * π * n)) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  convert tendsto_tsum_of_dominated_convergence (f := fun z n ↦ a n * cexp (2 * π * I * z * n))
    (𝓕 := atImInfty) (g := Set.indicator {0} (fun _ ↦ a 0)) ha ?_ ?_
  · simp
  · intro k
    rcases eq_or_ne k 0 with (rfl | hk)
    · simp
    · simp only [Set.mem_singleton_iff, hk, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I]
      rw [← mul_zero ‖a k‖]
      refine Tendsto.const_mul ‖a k‖ <| (Real.tendsto_exp_atBot).comp ?_
      simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
        coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, zero_add, tendsto_neg_atBot_iff]
      rw [tendsto_mul_const_atTop_of_pos, tendsto_const_mul_atTop_of_pos] <;> try positivity
      exact tendsto_im_atImInfty
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I, mul_right_comm]
    simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, neg_mul]
    gcongr
    have hz2 : (2 : ℝ) ≤ 2 * z.im := by nlinarith [hz]
    have hbase : 2 * π ≤ 2 * z.im * π := mul_le_mul_of_nonneg_right hz2 (by positivity)
    have hmul : 2 * π * (k : ℝ) ≤ (2 * z.im * π) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    simpa [mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm, add_comm] using hmul

lemma tendsto_int (a : ℤ → ℂ) (ha : Summable fun n : ℤ ↦ ‖a n‖ * rexp (-2 * π * n))
    (ha' : ∀ n, n < 0 → a n = 0) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  have : Tendsto
    (fun z : ℍ ↦ (∑' n : ℕ, (a n * cexp (2 * π * I * z * n)
      + a (-(n + 1 : ℤ)) * cexp (2 * π * I * z * (-(n + 1) : ℤ))))) atImInfty (𝓝 (a 0)) := by
    have := tendsto_nat (fun n ↦ a n) ?_
    · apply this.congr
      exact fun _ ↦ tsum_congr (by simpa using fun _ ↦ ha' _ (by omega))
    · exact (summable_int_iff_summable_nat_and_neg.mp ha).left
  apply this.congr'
  rw [EventuallyEq, eventually_atImInfty]
  use 1, fun z hz ↦ ?_
  rw [← tsum_nat_add_neg_add_one]
  · rfl
  rw [← summable_norm_iff]
  convert_to Summable fun n ↦ ‖a n‖ * rexp (z.im * -2 * π * n)
  · ext n
    rw [norm_mul, mul_right_comm _ I, mul_right_comm _ I, norm_exp_mul_I]
    simp
    ring_nf
    simp
  · apply ha.of_nonneg_of_le (fun _ ↦ by positivity) fun b ↦ ?_
    by_cases hb : 0 ≤ b
    · gcongr
      simp [hz]
    · norm_num at hb
      simp [ha' _ hb]

end QExp
