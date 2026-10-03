/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordMultiplicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFlux

/-! Principal and lower-order terms in the ordered Leibniz expansion. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- The two derivative orders in every ordered split add to the original order. -/
theorem iterateSpatialSplits_orders (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ iterateSpatialSplits w) :
    p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil =>
    simp only [iterateSpatialSplits, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    rfl
  | cons i w ih =>
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    obtain rfl | rfl := hp <;> have h := ih hq <;>
      simp only [List.length_cons] at * <;> omega

/-- There is exactly one principal split: all derivatives fall on the scalar. -/
theorem iterateSpatialSplits_nil_left (w : List (Fin 2)) :
    (iterateSpatialSplits w).filter (fun p => p.1.isEmpty) = [([], w)] := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialSplits, List.filter_flatMap]
    have heq (P : List (List (Fin 2) × List (Fin 2))) :
        P.flatMap (fun p => [(i :: p.1, p.2), (p.1, i :: p.2)].filter
          (fun q => q.1.isEmpty)) =
        (P.filter (fun p => p.1.isEmpty)).map (fun p => (p.1, i :: p.2)) := by
      induction P with
      | nil => rfl
      | cons p P ih =>
        simp only [List.filter_cons, List.isEmpty_cons, Bool.false_eq_true,
          ↓reduceIte, List.filter_nil] at ih ⊢
        simp only [List.flatMap_cons, ih]
        cases h : p.1.isEmpty <;>
          simp only [Bool.false_eq_true, ↓reduceIte,
            List.nil_append, List.map_cons, List.singleton_append]
    rw [heq, ih]
    rfl

/-- Splitting a list sum retains the principal and complementary terms exactly. -/
theorem iterate_split_list_sum {α : Type*} (P : List α) (f : α → ℝ) (q : α → Bool) :
    (P.map f).sum = ((P.filter q).map f).sum +
      ((P.filter (fun p => !(q p))).map f).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    cases h : q p <;> simp [h, ih] <;> ring

/-- Every complementary split has strictly fewer scalar derivatives. -/
theorem iterateSpatialSplits_lower_order (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)}
    (hp : p ∈ (iterateSpatialSplits w).filter (fun q => !q.1.isEmpty)) :
    p.2.length < w.length := by
  obtain ⟨hp, hne⟩ := List.mem_filter.mp hp
  have hs := iterateSpatialSplits_orders w hp
  have hn : p.1 ≠ [] := by
    intro he
    simp [he] at hne
  have hl : 0 < p.1.length := List.length_pos_iff.mpr hn
  omega

/-- The strictly lower scalar-order portion of a differentiated matrix flux. -/
def iterateLowerWordFlux (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : Vec 2 → ℝ) (w : List (Fin 2)) (x : Vec 2) : Vec 2 := fun i =>
  ∑ j : Fin 2, (((iterateSpatialSplits w).filter (fun p => !p.1.isEmpty)).map (fun p =>
    iterateSpatialWord p.1 (fun y => A y i j) x *
      spaceGrad (iterateSpatialWord p.2 v) x j)).sum

/-- Separate the unique principal term from the full coefficient expansion. -/
theorem iterateWordFlux_principal
    (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → ℝ)
    (w : List (Fin 2)) (x : Vec 2) :
    iterateWordFlux A v w x =
      (A x).mulVec (spaceGrad (iterateSpatialWord w v) x) +
        iterateLowerWordFlux A v w x := by
  funext i
  unfold iterateWordFlux iterateLowerWordFlux Matrix.mulVec dotProduct
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [iterate_split_list_sum (iterateSpatialSplits w) _ (fun p => p.1.isEmpty),
    iterateSpatialSplits_nil_left]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    iterateSpatialWord]

end AVenhance.Infra.Section4
