/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRecursion

/-! # Iterates Stream Budget Kernel

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The three current-order stream contributions, with their actual kernels. -/
def iterateStreamEnergyBudget (n : ℕ) (u v c W : ℝ) (d : ℕ → ℝ) : ℝ :=
  u * W ^ 2 * (if n = 0 then 0 else d (n - 1) ^ 2) +
    v * W ^ 2 * (∑ k ∈ Finset.range (n - 1), (1 / (4 : ℝ)) ^ k * d (n - 2 - k) ^ 2) +
    c * W ^ 2 * ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k * d (n - 1 - k)

/-- Under the lower-order induction bound the two kernels have mass at most
 two; no supremum over derivative orders is required. -/
theorem iterate_stream_budget_unit_profile (n : ℕ) {u v c W : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : 0 ≤ c) :
    iterateStreamEnergyBudget n u v c W (fun _ => 1) ≤ (u + 2 * v + 2 * c) * W ^ 2 := by
  have h4 := iterate_geometric_kernel_le_two (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2) (n - 1)
  have h2 := iterate_geometric_kernel_le_two (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1 / 2) n
  have hv4 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hv (sq_nonneg W))
  have hc2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc (sq_nonneg W))
  have hu1 : u * W ^ 2 * (if n = 0 then (0 : ℝ) else 1) ≤ u * W ^ 2 := by
    split_ifs
    · simp only [mul_zero]; positivity
    · simp only [mul_one, le_refl]
  simp only [iterateStreamEnergyBudget, one_pow, mul_one]
  nlinarith only [hu1, hv4, hc2]

end AVenhance.Infra.Section4
