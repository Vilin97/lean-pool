/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.Fraction

namespace FractionEqualities

lemma one_sub_inverse_of_add_one {n : ℝ} (hn : n + 1 ≠ 0) :
    1 - 1 / (n + 1) = n / (n + 1) := by
  field_simp
  ring

lemma frac_cancel {a b c : ℝ} (hb : b ≠ 0) : (a / b) * (b / c) = a / c := by
  field_simp

lemma frac_cancel' {a b c : ℝ} (hb : b ≠ 0) : (b / a) * (c / b) = c / a := by
  rw [mul_comm]
  exact frac_cancel hb

lemma one_sub_frac {a b : ℝ} (hb : b + 1 ≠ 0) : (1 - (a + 1)/(b+1)) = (b - a) / (b + 1) := by
  field_simp
  ring

lemma frac_special {a b c : ℝ} (hbc : b ≠ c) (hc : c + 1 ≠ 0) :
    (a + (b + 1)) / (c + 1) = (1 - (b + 1) / (c + 1)) * (a / (c - b)) + (b + 1) / (c + 1) := by
  have hcb : c - b ≠ 0 := sub_ne_zero_of_ne hbc.symm
  field_simp
  ring

/-- For any `i n : ℕ` with `i > 0` and `i ≤ (n + 1) * i`,
we have that `1 / (n + 1) = i / ((n + 1) * i)`. -/
lemma cancel_common_factor {i n : ℕ} (i_pos : 0 < i)
    (hi_n : (i - 1).succ ≤ ((n + 1) * i - 1).succ) :
    Fraction.ofPos (Nat.succ_pos n) = Fraction (Nat.succ_pos _) hi_n := by
  apply Subtype.coe_inj.mp
  have h1 : (i - 1).succ = i := Nat.succ_pred_eq_of_pos i_pos
  have h2 : ((n + 1) * i - 1).succ = (n + 1) * i :=
    Nat.succ_pred_eq_of_pos (mul_pos (Nat.succ_pos n) i_pos)
  change ((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) =
      (((i - 1).succ : ℕ) : ℝ) / ((((n + 1) * i - 1).succ : ℕ) : ℝ)
  rw [h1, h2]
  push_cast
  have hicast : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp i_pos)
  field_simp

end FractionEqualities
