/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Roots.WeakWellposed

/-! Statement file: `weak_wellposed` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Weak well-posedness -/
theorem weak_wellposed (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (κ : ℝ) (hκ : 0 < κ) (θ₀ : Vec 2 → ℝ)
    (hθ₀_L2 : MemL2On unitCube θ₀) :
    ∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ ∧
      ∀ θ' : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ' →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, θ' t =ᵐ[volume.restrict unitCube] θ t := by
  exact AVenhance.Proofs.weak_wellposed b hb_meas hb_bdd hb_per κ hκ θ₀ hθ₀_L2

end AVenhance
