/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsTestFunction

/-! Statement file: `IsWeakSolutionGrad` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- The weak-solution notion with the gradient `Dθ` explicit: weak solution on `[0,1] × 𝕋²` of
`∂ₜθ + b·∇θ − κΔθ = 0`, `θ(0) = θ₀`. The drift term is required to be
integrable on the space-time cell, so no integral in the weak form can take the
Bochner junk value. -/
def IsWeakSolutionGrad (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (θ₀ : Vec 2 → ℝ)
    (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ t) ≤ C) ∧
  MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 (volume.restrict timeCube) ∧
  (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2 (volume.restrict timeCube)) ∧
  (∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), IsPeriodicH1With (θ t) (Dθ t)) ∧
  Integrable (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2)) (volume.restrict timeCube) ∧
  (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc (0 : ℝ) 1)) ∧
  (∀ φ : ℝ → Vec 2 → ℝ, IsTestFunction φ →
    ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
        + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
      = ∫ x in unitCube, θ₀ x * φ 0 x)

end AVenhance
