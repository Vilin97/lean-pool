/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityFirstSpatialSum

/-! Separate spatial and material budgets for actual Leibniz subwords. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A canonical mixed word contains exactly its prescribed material count. -/
theorem amnrMixedWord_count_none (α : List (Fin 2)) (n : ℕ) :
    (amnrMixedWord α n).count none = n := by
  have hzero : (α.map some).count none = 0 := List.count_eq_zero.mpr (by simp)
  simp [amnrMixedWord, List.count_append, hzero]

/-- A Leibniz subword is canonical and never gains spatial or material
budget. The material count is controlled separately for strong induction. -/
theorem amnrMixedWord_subword_normalForm {α : List (Fin 2)} {n : ℕ}
    {v : List (Option (Fin 2))} (hv : v.Sublist (amnrMixedWord α n)) :
    ∃ η : List (Fin 2), ∃ r : ℕ, v = amnrMixedWord η r ∧
      r ≤ n ∧ η.length + 2 * r ≤ α.length + 2 * n := by
  obtain ⟨η, r, heq⟩ := IsAmnrMixedWord.normalForm ((amnrMixedWord_mixed α n).sublist hv)
  have hc := hv.count_le none
  have hb := amnrBudget_sublist hv
  rw [heq, amnrMixedWord_count_none, amnrMixedWord_count_none] at hc
  rw [heq, amnrMixedWord_budget, amnrMixedWord_budget] at hb
  exact ⟨η, r, heq, hc, hb⟩

end AVenhance.Infra.Section4
