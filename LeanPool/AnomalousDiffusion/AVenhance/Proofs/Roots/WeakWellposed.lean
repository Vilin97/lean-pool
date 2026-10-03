/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitExistence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakUniquenessTheorem
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution

/-!
# Weak well-posedness for bounded periodic drifts

This module assembles existence and uniqueness under the exact root hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Proofs

/-- Existence in the exact weak-solution class, under the weak well-posedness data hypotheses. -/
theorem weak_wellposed_exists (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (κ : ℝ) (hκ : 0 < κ) (θ₀ : Vec 2 → ℝ)
    (hθ₀_L2 : MemL2On unitCube θ₀) :
    ∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ := by
  let P : AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDriftProblem :=
    ⟨b, hb_meas, hb_bdd, hb_per, κ, hκ, θ₀, hθ₀_L2⟩
  obtain ⟨θ, Dθ, hθ⟩ := P.exists_isWeakSolutionGrad
  exact ⟨θ, Dθ, hθ⟩

/-- Exact weak well-posedness weak well-posedness: existence in the class and cell-a.e. uniqueness
    at every
time. -/
theorem weak_wellposed (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (κ : ℝ) (hκ : 0 < κ) (θ₀ : Vec 2 → ℝ)
    (hθ₀_L2 : MemL2On unitCube θ₀) :
    ∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ ∧
      ∀ θ' : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ' →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          θ' t =ᵐ[volume.restrict unitCube] θ t := by
  obtain ⟨θ, hθ⟩ := weak_wellposed_exists b hb_meas hb_bdd hb_per κ hκ θ₀ hθ₀_L2
  rcases hθ with ⟨D, hD⟩
  refine ⟨θ, ⟨D, hD⟩, ?_⟩
  intro θ' hθ' t ht
  rcases hθ' with ⟨E, hE⟩
  exact AVenhance.Infra.Parabolic.WeakUniqueness.weak_solutionGrad_unique
    hθ₀_L2 hE hD hb_meas hb_bdd hκ t ht

end AVenhance.Proofs

end
