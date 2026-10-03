/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic

/-! Actual classical witnesses for every temperature iterate. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The starting unforced temperature and the iterate construction
supply every classical witness; no energy or differentiated equation is assumed. -/
theorem amnr_tIterates_classical_family {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (i : ℕ) (hi : i ≤ AVenhance.Nstar β) :
    ∃ F : ℝ → Vec 2 → ℝ,
      AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev F θ₀ (T i) := by
  by_cases hz : i = 0
  · subst i
    exact ⟨fun _ _ => 0, by rw [hT.1]; exact hθ⟩
  · exact ⟨I.TForcing hΦ m κm κprev (T (i - 1)), hT.2 i (by omega) hi⟩

end AVenhance.Infra.Section4
