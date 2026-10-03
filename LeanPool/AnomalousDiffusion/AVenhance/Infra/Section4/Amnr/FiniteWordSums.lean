/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.AdvectionTerms

/-! Actual ordered derivatives of finite correction sums. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnr_list_sum_contDiff (T : List (AmnrSpace → ℝ))
    (hT : ∀ f ∈ T, ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) T.sum := by
  induction T with
  | nil => exact contDiff_const
  | cons f T ih =>
    exact (hT f (by simp)).add (ih (fun g hg => hT g (by simp [hg])))

/-- Ordered differentiation commutes with a finite sum of actual smooth fields. -/
theorem amnrWord_list_sum_global {b : AmnrSpace → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (T : List (AmnrSpace → ℝ))
    (hT : ∀ f ∈ T, ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Option (Fin 2))) :
    amnrWord b w T.sum = (T.map (amnrWord b w)).sum := by
  induction T with
  | nil => simp only [List.sum_nil, List.map_nil, amnrWord_zero]
  | cons f T ih =>
    have htail := fun g hg => hT g (List.mem_cons_of_mem f hg)
    rw [List.sum_cons, amnrWord_add_global hb (hT f (by simp)) (amnr_list_sum_contDiff T htail) w,
      ih htail, List.map_cons, List.sum_cons]

/-- Evaluation of a finite function sum is the sum of its actual values. -/
theorem amnr_list_sum_apply (T : List (AmnrSpace → ℝ)) (z : AmnrSpace) :
    T.sum z = (T.map (fun f => f z)).sum := by
  induction T with
  | nil => rfl
  | cons f T ih => simp only [List.sum_cons, List.map_cons, Pi.add_apply, ih]

end AVenhance.Infra.Section4
