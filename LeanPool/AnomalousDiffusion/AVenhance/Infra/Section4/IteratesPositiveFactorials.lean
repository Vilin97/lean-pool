/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingFactorials

/-! Positive velocity orders in actual squared material-error energies. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- Exact positive-order range shift. -/
theorem iterate_sum_positive_orders (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n + 1), if 1 ≤ j then f j else 0) =
      ∑ k ∈ Finset.range n, f (k + 1) := by
  rw [Finset.sum_range_succ']
  simp

/-- Every actual positive velocity order contributes a squared radius gain,
 after exact binomial-factorial cancellation. -/
theorem iterate_positive_factorial_profile_sum_le (n a : ℕ) {r L : ℝ}
    (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2) :
    (∑ j ∈ Finset.range (n + 1), if 1 ≤ j then
      (Nat.choose n j : ℝ) ^ 2 * (2 : ℝ) ^ j * ((j.factorial : ℝ) * r ^ j) ^ 2 *
        (((n - j + a).factorial : ℝ) * L ^ (n - j)) ^ 2 else 0) ≤
      4 * (r / L) ^ 2 * (((n + a).factorial : ℝ) * L ^ n) ^ 2 := by
  have ht : (∑ j ∈ Finset.range (n + 1), if 1 ≤ j then
      (Nat.choose n j : ℝ) ^ 2 * (2 : ℝ) ^ j * ((j.factorial : ℝ) * r ^ j) ^ 2 *
        (((n - j + a).factorial : ℝ) * L ^ (n - j)) ^ 2 else 0) ≤
      (∑ j ∈ Finset.range (n + 1), if 1 ≤ j then (2 * (r / L) ^ 2) ^ j else 0) *
        (((n + a).factorial : ℝ) * L ^ n) ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : 1 ≤ j
    · simp only [h, ite_true]
      exact iterate_weighted_shifted_factorial_term_le n j a
        (by have ht := Finset.mem_range.mp hj; omega) hL
    · simp [h]
  rw [iterate_sum_positive_orders n (fun j => (2 * (r / L) ^ 2) ^ j)] at ht
  have he : (∑ k ∈ Finset.range n, (2 * (r / L) ^ 2) ^ (k + 1)) =
      (2 * (r / L) ^ 2) * (∑ k ∈ Finset.range n, (2 * (r / L) ^ 2) ^ k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [he] at ht
  have hs := mul_le_mul_of_nonneg_left
    (iterate_geometric_kernel_le_two (by positivity : 0 ≤ 2 * (r / L) ^ 2) hg n)
    (by positivity : 0 ≤ 2 * (r / L) ^ 2)
  have hm := mul_le_mul_of_nonneg_right hs
    (sq_nonneg (((n + a).factorial : ℝ) * L ^ n))
  exact ht.trans (by convert hm using 1; ring)

end AVenhance.Infra.Section4
