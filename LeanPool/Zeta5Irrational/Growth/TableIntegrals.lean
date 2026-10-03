/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.PieceIdx
import Mathlib.Tactic.ReduceModChar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Ring.IsFormallyReal
public import LeanPool.Zeta5Irrational.Growth.InnerSum
public import LeanPool.Zeta5Irrational.Growth.OuterTable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic

/-! # The integrals of the piece tables

`∑_i ∫_{t_i}^{t_{i+1}} (a_i x + b_i)/x³ dx` equals `(5.18)` for the inner table and
`127751/96000 + 9/640` for the outer table.
-/

public section

open Finset intervalIntegral

namespace Zeta5Irrational

lemma integral_lin_div_cube (A B : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (A * x + B) / x ^ 3 = A * (1 / a - 1 / b) + B / 2 * (1 / a ^ 2 - 1 / b ^ 2) := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx;
    rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  have hb : 0 < b := by linarith
  rw [integral_eq_sub_of_hasDerivAt (f := fun x => -A / x - B / 2 / x ^ 2)]
  · field_simp; ring
  · intro x hx
    have hx0 := (hpos x hx).ne'
    have d1 := (hasDerivAt_const x (-A)).div (hasDerivAt_id x) hx0
    have d2 := (hasDerivAt_const x (B / 2)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0)
    have := d1.sub d2
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; exact pow_ne_zero 3 (hpos x hx).ne'

lemma tIn_pos (i : ℕ) (hi : i ≤ 125) : 0 < tIn i := by
  have h0 : tIn 0 = 3 := by simp [tIn, tInL]
  have := grid_mono tIn_mono (Nat.zero_le i) hi
  linarith

lemma tOut_pos (i : ℕ) (hi : i ≤ 13) : 0 < tOut i := by
  have h0 : tOut 0 = 20 / 37 := by simp [tOut, tOutL]
  have := grid_mono tOut_mono (Nat.zero_le i) hi
  linarith

private lemma inner_integrals_rational :
    (range 125).sum (fun i =>
      aInL.getD i 0 * (1 / tInL.getD i 0 - 1 / tInL.getD (i + 1) 0) +
        bInL.getD i 0 / 2 * (1 / (tInL.getD i 0) ^ 2 -
          1 / (tInL.getD (i + 1) 0) ^ 2)) =
      (322437603634266857629 / 7535670527041937280000 : ℚ) := by decide +kernel

private lemma outer_integrals_rational :
    (range 13).sum (fun i =>
      aOutL.getD i 0 * (1 / tOutL.getD i 0 - 1 / tOutL.getD (i + 1) 0) +
        bOutL.getD i 0 / 2 * (1 / (tOutL.getD i 0) ^ 2 -
          1 / (tOutL.getD (i + 1) 0) ^ 2)) = (129101 / 96000 : ℚ) := by decide +kernel

theorem inner_integrals :
    ∑ i ∈ range 125, ∫ x in tIn i..tIn (i + 1), gIn i x / x ^ 3 =
      322437603634266857629 / 7535670527041937280000 := by
  rw [Finset.sum_congr rfl fun i hi =>
      by
      have hi' := Finset.mem_range.mp hi
      exact integral_lin_div_cube _ _ (tIn_pos i hi'.le) (tIn_mono i hi').le]
  simp only [tIn]
  have certificate := congrArg (fun q : ℚ => (q : ℝ)) inner_integrals_rational
  push_cast at certificate
  exact certificate

theorem outer_integrals :
    ∑ i ∈ range 13, ∫ x in tOut i..tOut (i + 1), gOut i x / x ^ 3 = 129101 / 96000 := by
  rw [Finset.sum_congr rfl fun i hi =>
      by
      have hi' := Finset.mem_range.mp hi
      exact integral_lin_div_cube _ _ (tOut_pos i hi'.le) (tOut_mono i hi').le]
  simp only [tOut]
  have certificate := congrArg (fun q : ℚ => (q : ℝ)) outer_integrals_rational
  push_cast at certificate
  exact certificate

end Zeta5Irrational
