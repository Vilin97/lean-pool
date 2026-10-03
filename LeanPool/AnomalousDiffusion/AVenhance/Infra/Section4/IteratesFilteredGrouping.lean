/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedGrouping

/-! Exact grouping and dissipation allocation for selected coefficient orders. -/

@[expose] public section

namespace AVenhance.Infra.Section4

theorem IteratesFilteredGrouping.filtered_map_sum {α : Type*} (P : List α) (q : α → Bool) (f : α →
    ℝ) :
    ((P.filter q).map f).sum = (P.map (fun p => if q p then f p else 0)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    cases h : q p <;> simp [h, ih]

/-- A cutoff on coefficient order preserves each binomial multiplicity. -/
theorem iterateSpatialSplits_filtered_sum_by_two_orders
    (w : List (Fin 2)) (q : ℕ → Bool) (f : ℕ → ℕ → ℝ) :
    (((iterateSpatialSplits w).filter (fun p => q p.1.length)).map
      (fun p => f p.1.length p.2.length)).sum =
      ∑ j ∈ Finset.range (w.length + 1), (Nat.choose w.length j : ℝ) *
        (if q j then f j (w.length - j) else 0) := by
  rw [IteratesFilteredGrouping.filtered_map_sum]
  exact iterateSpatialSplits_sum_by_two_orders w (fun j k => if q j then f j k else 0)

/-- Any selection of coefficient orders retains the uniform dissipation
 allocation of the full expansion. -/
theorem iterateYoungWeight_filtered_sum_le {κ : ℝ} (hκ : 0 < κ)
    (w : List (Fin 2)) (q : ℕ → Bool) :
    (((iterateSpatialSplits w).filter (fun p => q p.1.length)).map
      (fun p => iterateYoungWeight κ w.length p.1.length)).sum ≤ κ / 8 := by
  rw [IteratesFilteredGrouping.filtered_map_sum]
  apply le_trans _ (iterateYoungWeight_sum_le hκ.le w)
  apply List.sum_le_sum
  intro p hp
  split_ifs
  · exact le_rfl
  · exact (iterateYoungWeight_pos hκ w hp).le

/-- The Young remainder for selected orders has the same exact squared
 binomial weights as the full remainder. -/
theorem iterate_filtered_remainder_group_bound {κ : ℝ} (hκ : 0 < κ)
    (w : List (Fin 2)) (q : ℕ → Bool) (D E : ℕ → ℝ)
    (G : List (Fin 2) → ℝ)
    (hG : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => q p.1.length),
      G p.2 ≤ E p.2.length) :
    (((iterateSpatialSplits w).filter (fun p => q p.1.length)).map (fun p =>
      (D p.1.length) ^ 2 / iterateYoungWeight κ w.length p.1.length * G p.2)).sum ≤
      16 / κ * ∑ j ∈ Finset.range (w.length + 1),
        (if q j then (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j *
          (D j) ^ 2 * E (w.length - j) else 0) := by
  calc
    _ ≤ (((iterateSpatialSplits w).filter (fun p => q p.1.length)).map (fun p =>
        (D p.1.length) ^ 2 / iterateYoungWeight κ w.length p.1.length * E p.2.length)).sum := by
      apply List.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hG p hp)
        (div_nonneg (sq_nonneg _) (iterateYoungWeight_pos hκ w (List.mem_filter.mp hp).1).le)
    _ = _ := by
      have he : (((iterateSpatialSplits w).filter (fun p => q p.1.length)).map (fun p =>
          (D p.1.length) ^ 2 / iterateYoungWeight κ w.length p.1.length * E p.2.length)).sum =
          (((iterateSpatialSplits w).filter (fun p => q p.1.length)).map (fun p =>
          16 / κ * (Nat.choose w.length p.1.length : ℝ) * (2 : ℝ) ^ p.1.length *
            (D p.1.length) ^ 2 * E p.2.length)).sum := by
        congr 1
        apply List.map_congr_left
        intro p hp
        have hs := iterateSpatialSplits_orders w (List.mem_filter.mp hp).1
        rw [iterateYoungWeight_reciprocal hκ w.length p.1.length (by omega)]
      rw [he, iterateSpatialSplits_filtered_sum_by_two_orders w q
        (fun j k => 16 / κ * (Nat.choose w.length j : ℝ) * (2 : ℝ) ^ j * (D j) ^ 2 * E k),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      cases q j <;> simp
      ring

end AVenhance.Infra.Section4
