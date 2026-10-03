/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsTestFunction
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsHolderTimeL2

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance
/-- Weak solution on `[0,1] × 𝕋²` of the transport equation `∂ₜθ + b·∇θ = 0`, `θ(0) = θ₀`
(the `κ = 0` limit, source line 10132), in divergence form `∂ₜθ + ∇·(bθ) = 0`, which is the same
equation for divergence-free `b`.  Same regularity carriers, weak continuity and test class as
`IsWeakSolutionGrad`, minus the `H¹` gradient; the drift integrand is required integrable so no
integral takes the Bochner junk value. -/
def IsTransportWeakSolution (b : ℝ → Vec 2 → Vec 2) (θ₀ : Vec 2 → ℝ)
    (θ : ℝ → Vec 2 → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ t) ≤ C) ∧
  MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 (volume.restrict timeCube) ∧
  (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc (0 : ℝ) 1)) ∧
  (∀ φ : ℝ → Vec 2 → ℝ, IsTestFunction φ →
    Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2))
      (volume.restrict timeCube) ∧
    ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2))
      = ∫ x in unitCube, θ₀ x * φ 0 x)

end AVenhance
