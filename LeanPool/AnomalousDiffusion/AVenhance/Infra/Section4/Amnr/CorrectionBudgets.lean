/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialCorrectionExpansion

/-! Strict lower-level budgets for every actual correction factor. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

theorem amnrFactorCount_le_sum (A : List AmnrAdvectionFactor)
    (a : AmnrAdvectionFactor) (ha : a ∈ A) (F : List (Option (Fin 2)) → ℕ) :
    F a.2 ≤ (A.map (fun b => F b.2)).sum := by
  induction A with
  | nil => simp at ha
  | cons b A ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons, List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have hh := ih ha
      omega

/-- The scalar word is nonempty and every scalar and velocity word uses
strictly fewer material derivatives than the current induction level. -/
theorem amnrCorrectionBudgets (α : List (Fin 2)) (n : ℕ)
    (t : AmnrAdvectionTerm) (ht : t ∈ amnrSpatialAdvectionTerms α (amnrMaterialErrorTerms n)) :
    t.scalarWord ≠ [] ∧ amnrMaterialCount t.scalarWord < n ∧
    amnrBudget t.scalarWord + 1 ≤ α.length + 2 * n ∧
    ∀ a ∈ t.factors, amnrMaterialCount a.2 < n ∧
      amnrBudget a.2 + 2 ≤ α.length + 2 * n := by
  obtain ⟨hL, hW, hS, hM⟩ := amnrSpatialMaterialErrorTerms_counts α n t ht
  have hMS : amnrMaterialCount t.scalarWord ≤ amnrTermMaterialCount t := by
    unfold amnrTermMaterialCount
    omega
  have hSS : amnrSpatialCount t.scalarWord ≤ amnrTermSpatialCount t := by
    unfold amnrTermSpatialCount
    omega
  have htotal : amnrTermSpatialCount t + 2 * amnrTermMaterialCount t +
      t.factors.length = α.length + 2 * n := by omega
  refine ⟨?_, by omega, ?_, ?_⟩
  · intro hh
    simp only [hh, amnrSpatialCount] at hW
    omega
  · rw [← amnrCounts_budget]
    omega
  · intro a ha
    have hMa := amnrFactorCount_le_sum t.factors a ha amnrMaterialCount
    have hSa := amnrFactorCount_le_sum t.factors a ha amnrSpatialCount
    dsimp [amnrTermSpatialCount, amnrTermMaterialCount] at hS hM htotal hMS hSS
    rw [← amnrCounts_budget]
    exact ⟨by omega, by omega⟩

end AVenhance.Infra.Section4
