/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Real.StarOrdered

/-! # Upperhalfplane -/


@[expose] public section

open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := im_pnat_div_pos (↑n) z

lemma pos_nat_div_upper (n : ℤ) (hn : 0 < n) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  norm_cast
  rw [div_im, Int.cast_neg, neg_im, intCast_im, neg_zero, zero_mul, zero_div, zero_sub,
    Left.neg_pos_iff, div_neg_iff]
  right
  rw [neg_re, neg_mul, Left.neg_neg_iff, Complex.normSq_pos, ne_eq]
  exact ⟨by apply mul_pos (by simp [hn]) z.2, ne_zero z⟩
