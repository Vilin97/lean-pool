/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordGrouping
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesYoungWeights

/-! Exact binomial grouping of positive velocity and stream coefficient jets. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- Removing the unique principal split leaves precisely coefficient orders
j+1, with their original binomial multiplicities. -/
theorem iterateSpatialSplits_positive_sum_by_order (w : List (Fin 2)) (f : ℕ → ℝ) :
    (((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)).map (fun p => f p.1.length)).sum =
      ∑ j ∈ Finset.range w.length, (Nat.choose w.length (j + 1) : ℝ) * f (j + 1) := by
  have he := iterate_split_list_sum (iterateSpatialSplits w) (fun p => f p.1.length)
    (fun p => p.1.isEmpty)
  rw [iterateSpatialSplits_nil_left] at he
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil, add_zero]
      at he
  have hg := iterateSpatialSplits_sum_by_order w f
  rw [Finset.sum_range_succ'] at hg
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at hg
  linarith only [he, hg]

/-- Both word orders remain exact after removing the principal split. -/
theorem iterateSpatialSplits_positive_sum_by_two_orders (w : List (Fin 2)) (f : ℕ → ℕ → ℝ) :
    (((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)).map
      (fun p => f p.1.length p.2.length)).sum =
      ∑ j ∈ Finset.range w.length,
        (Nat.choose w.length (j + 1) : ℝ) * f (j + 1) (w.length - (j + 1)) := by
  have he : (((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)).map
      (fun p => f p.1.length p.2.length)) =
      (((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)).map
      (fun p => f p.1.length (w.length - p.1.length))) := by
    apply List.map_congr_left
    intro p hp
    have hs := iterateSpatialSplits_orders w (List.mem_filter.mp hp).1
    congr 1
    omega
  rw [he]
  exact iterateSpatialSplits_positive_sum_by_order w (fun j => f j (w.length - j))

end AVenhance.Infra.Section4
