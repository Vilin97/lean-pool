/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsTransportWeakSolution

/-! # Phase 2: vanishing-diffusivity limits are transport weak solutions

Source line 10132 (asserted without proof there): a sequence of weak solutions with
diffusivities `κ_j → 0`, uniformly Cauchy in `L²(cell)` over `t ∈ [0,1]`, converges uniformly in
`L²` to a weak solution of the transport equation `∂ₜθ + b·∇θ = 0` with the same initial datum.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Uniform-`L²` limits of weak solutions with vanishing diffusivity are transport weak
solutions. -/
def TransportLimitContract : Prop :=
  ∀ b : ℝ → Vec 2 → Vec 2,
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) →
    (∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B) →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t)) → IsDivFree b →
  ∀ θ₀ : Vec 2 → ℝ, MemL2On unitCube θ₀ →
  ∀ κ : ℕ → ℝ, (∀ j, 0 < κ j) → Tendsto κ atTop (𝓝 0) →
  ∀ θ : ℕ → ℝ → Vec 2 → ℝ, (∀ j, IsWeakSolution b (κ j) θ₀ (θ j)) →
    (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - θ k t x)) ≤ η) →
    ∃ Θ : ℝ → Vec 2 → ℝ, IsTransportWeakSolution b θ₀ Θ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (Θ t)) ∧
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η

end AVenhance.Infra.FullTheorem
