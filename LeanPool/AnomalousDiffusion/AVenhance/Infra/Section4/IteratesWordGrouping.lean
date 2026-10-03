/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSplitPrincipal

/-! Group the actual Leibniz terms by their coefficient derivative order. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

theorem IteratesWordGrouping.iterate_list_sum_group_orders
    (P : List (List (Fin 2) × List (Fin 2))) (n : ℕ) (f : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.1.length ≤ n) :
    (P.map (fun p => f p.1.length)).sum =
      ∑ j ∈ Finset.range (n + 1), (P.countP (fun p => p.1.length == j) : ℝ) * f j := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp : p.1.length ≤ n := hP p List.mem_cons_self
    have ht : ∀ q ∈ P, q.1.length ≤ n := fun q hq => hP q (List.mem_cons_of_mem p hq)
    have hc (j : ℕ) :
        ((p :: P).countP (fun q => q.1.length == j) : ℝ) =
          (P.countP (fun q => q.1.length == j) : ℝ) +
          (if p.1.length = j then 1 else 0) := by
      by_cases h : p.1.length = j <;> simp [h]
    simp only [List.map_cons, List.sum_cons]
    simp_rw [hc, add_mul]
    rw [Finset.sum_add_distrib, ← ih ht]
    have hs : (∑ j ∈ Finset.range (n + 1),
        (if p.1.length = j then (1 : ℝ) else 0) * f j) = f p.1.length := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range, show p.1.length < n + 1 by omega, ↓reduceIte]
    rw [hs]
    ring

/-- Exact binomial grouping, valid for any real weights and any ordered word. -/
theorem iterateSpatialSplits_sum_by_order (w : List (Fin 2)) (f : ℕ → ℝ) :
    ((iterateSpatialSplits w).map (fun p => f p.1.length)).sum =
      ∑ j ∈ Finset.range (w.length + 1), (Nat.choose w.length j : ℝ) * f j := by
  rw [IteratesWordGrouping.iterate_list_sum_group_orders (iterateSpatialSplits w) w.length f
    (fun p hp => by have h := iterateSpatialSplits_orders w hp; omega)]
  simp only [iterateSpatialSplits_count]

/-- Both factor orders can be grouped: the scalar order is n minus the
coefficient order, by the proved ordered-split identity. -/
theorem iterateSpatialSplits_sum_by_two_orders (w : List (Fin 2)) (f : ℕ → ℕ → ℝ) :
    ((iterateSpatialSplits w).map (fun p => f p.1.length p.2.length)).sum =
      ∑ j ∈ Finset.range (w.length + 1), (Nat.choose w.length j : ℝ) * f j (w.length - j) := by
  have heq : (iterateSpatialSplits w).map (fun p => f p.1.length p.2.length) =
      (iterateSpatialSplits w).map (fun p => f p.1.length (w.length - p.1.length)) := by
    apply List.map_congr_left
    intro p hp
    have hs := iterateSpatialSplits_orders w hp
    congr 1
    omega
  rw [heq]
  exact iterateSpatialSplits_sum_by_order w (fun j => f j (w.length - j))

end AVenhance.Infra.Section4
