/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordLeibniz

/-! Exact binomial multiplicities for ordered Leibniz expansions. -/

@[expose] public section

namespace AVenhance.Infra.Section4

theorem IteratesWordMultiplicity.split_count_sum (P : List (List (Fin 2) × List (Fin 2))) (j : ℕ) :
    (P.map (fun p => if p.1.length = j then 1 else 0)).sum =
      P.countP (fun p => p.1.length == j) := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    split_ifs <;> simp_all [Nat.add_comm]

/-- Grouping splits by coefficient derivative order gives the binomial
coefficient; repeated coordinate letters retain their full multiplicity. -/
theorem iterateSpatialSplits_count (w : List (Fin 2)) (j : ℕ) :
    (iterateSpatialSplits w).countP (fun p => p.1.length == j) =
      Nat.choose w.length j := by
  induction w generalizing j with
  | nil =>
    cases j <;> simp [iterateSpatialSplits]
  | cons i w ih =>
    cases j with
    | zero =>
      simp only [iterateSpatialSplits, List.countP_flatMap]
      have heq : ((iterateSpatialSplits w).map
          (List.countP (fun p => p.1.length == 0) ∘
            (fun p => [(i :: p.1, p.2), (p.1, i :: p.2)]))).sum =
          ((iterateSpatialSplits w).map (fun p => if p.1.length = 0 then 1 else 0)).sum := by
        congr 1
        apply List.map_congr_left
        intro p _
        simp
      rw [heq, IteratesWordMultiplicity.split_count_sum, ih]
      simp
    | succ j =>
      simp only [iterateSpatialSplits, List.countP_flatMap]
      have heq : ((iterateSpatialSplits w).map
          (List.countP (fun p => p.1.length == j + 1) ∘
            (fun p => [(i :: p.1, p.2), (p.1, i :: p.2)]))).sum =
          ((iterateSpatialSplits w).map (fun p =>
            (if p.1.length = j then 1 else 0) +
            (if p.1.length = j + 1 then 1 else 0))).sum := by
        congr 1
        apply List.map_congr_left
        intro p _
        simp [List.countP_cons, Nat.add_comm]
        split_ifs <;> omega
      rw [heq, List.sum_map_add, IteratesWordMultiplicity.split_count_sum,
          IteratesWordMultiplicity.split_count_sum, ih, ih]
      exact (Nat.choose_succ_succ w.length j).symm

end AVenhance.Infra.Section4
