/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesYoungWeights

/-! Exact binomial-square remainder after allocating dissipation. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- A preceding gradient-energy bound at each scalar order groups the actual
Leibniz remainder with squared, rather than exponential, multiplicities. -/
theorem iterate_weighted_remainder_group_bound {κ : ℝ} (hκ : 0 < κ)
    (w : List (Fin 2)) (D E : ℕ → ℝ)
    (G : List (Fin 2) → ℝ)
    (hG : ∀ p ∈ iterateSpatialSplits w, G p.2 ≤ E p.2.length) :
    ((iterateSpatialSplits w).map (fun p =>
      (D p.1.length) ^ 2 / iterateYoungWeight κ w.length p.1.length * G p.2)).sum ≤
    16 / κ * ∑ j ∈ Finset.range (w.length + 1),
      (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j * (D j) ^ 2 * E (w.length - j) := by
  calc
    _ ≤ ((iterateSpatialSplits w).map (fun p =>
        (D p.1.length) ^ 2 / iterateYoungWeight κ w.length p.1.length * E p.2.length)).sum := by
      apply List.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hG p hp)
        (div_nonneg (sq_nonneg _) (iterateYoungWeight_pos hκ w hp).le)
    _ = _ := by
      have he : ((iterateSpatialSplits w).map (fun p =>
          (D p.1.length) ^ 2 / iterateYoungWeight κ w.length p.1.length * E p.2.length)).sum =
          ((iterateSpatialSplits w).map (fun p =>
          16 / κ * (Nat.choose w.length p.1.length : ℝ) * (2 : ℝ) ^ p.1.length *
            (D p.1.length) ^ 2 * E p.2.length)).sum := by
        congr 1
        apply List.map_congr_left
        intro p hp
        have hs := iterateSpatialSplits_orders w hp
        rw [iterateYoungWeight_reciprocal hκ w.length p.1.length (by omega)]
      rw [he, iterateSpatialSplits_sum_by_two_orders w
        (fun j k => 16 / κ * (Nat.choose w.length j : ℝ) * (2 : ℝ) ^ j *
          (D j) ^ 2 * E k), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end AVenhance.Infra.Section4
