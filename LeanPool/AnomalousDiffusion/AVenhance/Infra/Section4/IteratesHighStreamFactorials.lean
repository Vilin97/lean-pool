/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingFactorials

/-! The squared geometric kernel from stream coefficient orders at least two. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- Remove orders zero and one without changing any remaining term. -/
theorem iterate_sum_high_orders (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n + 1), if 2 ≤ j then f j else 0) =
      ∑ k ∈ Finset.range (n - 1), f (k + 2) := by
  by_cases hn : n = 0
  · subst n; simp
  have he : n + 1 = 2 + (n - 1) := by omega
  rw [he, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, ↓reduceIte, add_zero, Nat.not_ofNat_le_one,
    le_add_iff_nonneg_right, zero_le, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  simp [Nat.add_comm]

/-- Every high stream jet supplies two radius gains before the remaining
 geometric kernel. The lower scalar energy remains squared in this term. -/
theorem iterate_high_stream_factorial_series_le (n a : ℕ) {r L : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 4) (D : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n + 1), if 2 ≤ j then
      (Nat.choose n j : ℝ) ^ 2 * (2 : ℝ) ^ j *
        ((j.factorial : ℝ) * r ^ j) ^ 2 *
        (((n - j + a).factorial : ℝ) * L ^ (n - j)) ^ 2 * D (n - j) ^ 2 else 0) ≤
      (2 * (r / L) ^ 2) ^ 2 * (((n + a).factorial : ℝ) * L ^ n) ^ 2 *
        ∑ k ∈ Finset.range (n - 1), (1 / (4 : ℝ)) ^ k * D (n - 2 - k) ^ 2 := by
  rw [iterate_sum_high_orders, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hj : k + 2 ≤ n := by have ht := Finset.mem_range.mp hk; omega
  have ht := mul_le_mul_of_nonneg_right
    (iterate_weighted_shifted_factorial_term_le n (k + 2) a hj (b := r) hL)
    (sq_nonneg (D (n - (k + 2))))
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (r / L) ^ 2) hg k
  have hm := mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ (2 * (r / L) ^ 2) ^ 2 *
      (((n + a).factorial : ℝ) * L ^ n) ^ 2 * D (n - (k + 2)) ^ 2)
  have he : n - (k + 2) = n - 2 - k := by omega
  calc
    _ ≤ _ := ht
    _ = (2 * (r / L) ^ 2) ^ 2 * (((n + a).factorial : ℝ) * L ^ n) ^ 2 *
        D (n - (k + 2)) ^ 2 * (2 * (r / L) ^ 2) ^ k := by rw [pow_add]; ring
    _ ≤ _ := hm
    _ = (2 * (r / L) ^ 2) ^ 2 * (((n + a).factorial : ℝ) * L ^ n) ^ 2 *
        ((1 / (4 : ℝ)) ^ k * D (n - 2 - k) ^ 2) := by rw [he]; ring

end AVenhance.Infra.Section4
