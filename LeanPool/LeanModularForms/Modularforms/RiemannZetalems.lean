/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # RiemannZetalems -/


@[expose] public section

open TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


lemma zeta_two_eqn : ∑' (n : ℤ), ((n : ℂ) ^ 2)⁻¹ = 2 * riemannZeta 2 := by
  have := tsum_nat_add_neg (f := fun n => 1/((n : ℂ) ^ 2)) ?_
  · simp only [Int.cast_natCast, one_div, Int.cast_neg, even_two, Even.neg_pow, Int.cast_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, add_zero] at this
    rw [← this]
    have hr := zeta_nat_eq_tsum_of_gt_one (k := 2)
    simp only [Nat.one_lt_ofNat, Nat.cast_ofNat, one_div, forall_const] at hr
    rw [hr, Summable.tsum_add]
    · ring
    repeat{
    have := Complex.summable_one_div_nat_cpow (p := 2)
    simp only [cpow_ofNat, one_div, re_ofNat, Nat.one_lt_ofNat, iff_true] at this
    exact this}
  simp only [one_div]
  have := Complex.summable_one_div_nat_cpow (p := 2)
  simp only [cpow_ofNat, one_div, re_ofNat, Nat.one_lt_ofNat, iff_true] at *
  norm_cast at *
  apply Summable.of_nat_of_neg_add_one
  · apply this
  rw [← summable_nat_add_iff 1] at this
  apply this.congr
  intro b
  congr
