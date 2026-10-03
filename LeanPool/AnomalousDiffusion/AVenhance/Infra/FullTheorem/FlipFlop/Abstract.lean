/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Abstract real lemmas for the flip-flop

* `abs_log_one_add_le`: `|x| ≤ 1/2 → |log (1+x)| ≤ 2|x|`;
* `const_mul_inv_rpow_le_one`: `K Λ^{-s} ≤ 1` once `Λ ≥ K^{1/s}`;
* `flipflop_unroll`: the alternating telescoping with a tail-summable error sequence. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem.FlipFlop

theorem abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x)| ≤ 2 * |x| := by
  have hx' := abs_le.mp hx
  have hpos : 0 < 1 + x := by linarith [hx'.1]
  have hup : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlow : x / (1 + x) ≤ Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have h2 : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    linarith
  have hlow2 : -(2 * |x|) ≤ x / (1 + x) := by
    rcases le_or_gt 0 x with h | h
    · have : 0 ≤ x / (1 + x) := div_nonneg h hpos.le
      have : 0 ≤ |x| := abs_nonneg x
      linarith
    · rw [abs_of_neg h, le_div_iff₀ hpos]
      nlinarith [hx'.1]
  rw [abs_le]
  constructor
  · linarith
  · have := le_abs_self x
    have := abs_nonneg x
    linarith

theorem const_mul_inv_rpow_le_one {K s Λ : ℝ} (hK : 0 < K) (hs : 0 < s) (hΛ0 : 0 < Λ)
    (hΛ : K ^ (1 / s) ≤ Λ) : K * (Λ⁻¹) ^ s ≤ 1 := by
  have h1 : K ≤ Λ ^ s := by
    calc K = (K ^ (1 / s)) ^ s := by
          rw [← Real.rpow_mul hK.le, one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
      _ ≤ Λ ^ s := Real.rpow_le_rpow (by positivity) hΛ hs.le
  rw [Real.inv_rpow hΛ0.le s]
  have h3 : 0 < Λ ^ s := Real.rpow_pos_of_pos hΛ0 s
  rw [← div_eq_mul_inv, div_le_one h3]
  exact h1

/-- Alternating telescoping. -/
theorem flipflop_unroll (u e : ℕ → ℝ) (L B T : ℝ) (M : ℕ) (hB : 0 ≤ B)
    (htail : ∀ m n : ℕ, ∑ k ∈ Finset.range n, e (m + k) ≤ T * e m)
    (htop : |u (M - 1) - L| ≤ B * e (M - 1))
    (hstep : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ M - 1 → |u n + u (n + 1)| ≤ B * e n) :
    ∀ m : ℕ, 1 ≤ m → m ≤ M - 1 →
      |u m - (-1 : ℝ) ^ (M - 1 - m) * L| ≤ B * T * e m := by
  have P : ∀ k m : ℕ, m + k = M - 1 → 1 ≤ m →
      |u m - (-1 : ℝ) ^ k * L| ≤ B * ∑ j ∈ Finset.range (k + 1), e (m + j) := by
    intro k
    induction k with
    | zero =>
      intro m hm _
      have : m = M - 1 := by omega
      subst this
      simpa using htop
    | succ k ih =>
      intro m hm hm1
      have h1 := ih (m + 1) (by omega) (by omega)
      have h2 := hstep m hm1 (by omega)
      have hsum : ∑ j ∈ Finset.range (k + 1 + 1), e (m + j) =
          e m + ∑ j ∈ Finset.range (k + 1), e (m + 1 + j) := by
        rw [Finset.sum_range_succ' _ (k + 1), add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        omega
      rw [hsum]
      have key : u m - (-1 : ℝ) ^ (k + 1) * L =
          (u m + u (m + 1)) - (u (m + 1) - (-1 : ℝ) ^ k * L) := by ring
      rw [key]
      calc |(u m + u (m + 1)) - (u (m + 1) - (-1 : ℝ) ^ k * L)|
          ≤ |u m + u (m + 1)| + |u (m + 1) - (-1 : ℝ) ^ k * L| := abs_sub _ _
        _ ≤ B * e m + B * ∑ j ∈ Finset.range (k + 1), e (m + 1 + j) := add_le_add h2 h1
        _ = _ := by ring
  intro m hm1 hmM
  have h := P (M - 1 - m) m (by omega) hm1
  refine h.trans ?_
  calc B * ∑ j ∈ Finset.range (M - 1 - m + 1), e (m + j) ≤ B * (T * e m) :=
        mul_le_mul_of_nonneg_left (htail m _) hB
    _ = _ := by ring

end AVenhance.Infra.FullTheorem.FlipFlop
