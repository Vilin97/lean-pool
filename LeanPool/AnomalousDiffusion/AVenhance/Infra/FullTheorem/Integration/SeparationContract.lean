/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.GradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsAdmissibleStream
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol

/-! # The short-time separation estimate

Source `l.solutions.no.same` (9713ff), with corrections to the printed argument: two classical
solutions with the same smooth divergence-free drift and diffusivities `κ₁ < κ₂ ∈ [3κ₁, 5κ₁]` have
`L²` norms that separate at short times. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- `∑_{i,j} ∫_{cell} (∂_j ∂_i f)²`. -/
def hessNormSq (f : Vec 2 → ℝ) : ℝ :=
  ∫ x in unitCube, ∑ i : Fin 2, ∑ j : Fin 2,
    (spaceGrad (fun y => spaceGrad f y i) x j) ^ 2

/-- Short-time separation of the `L²` norms of two solutions with the same drift and
diffusivities in ratio `[3,5]`. -/
def SeparationContract : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ Ψ : ℝ → Vec 2 → ℝ, IsAdmissibleStream Ψ →
    ∀ Lu : ℝ, 0 ≤ Lu →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ∀ i j : Fin 2,
        |spaceGrad (fun y => streamVel Ψ t y i) x j| ≤ Lu) →
    ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ →
    ∀ lam : ℝ, 0 ≤ lam →
      gradNormSq (spaceGrad θ₀) = lam * l2NormSq θ₀ →
      hessNormSq θ₀ ≤ lam * gradNormSq (spaceGrad θ₀) →
    ∀ κ₁ κ₂ : ℝ, 0 < κ₁ → 3 * κ₁ ≤ κ₂ → κ₂ ≤ 5 * κ₁ →
    ∀ t : ℝ, 0 < t → t ≤ 1 → Lu * t ≤ c₀ → κ₂ * t * lam ≤ c₀ →
    ∀ θ₁ θ₂ : ℝ → Vec 2 → ℝ,
      IsClassicalSol (streamVel Ψ) κ₁ (fun _ _ => 0) θ₀ θ₁ →
      IsClassicalSol (streamVel Ψ) κ₂ (fun _ _ => 0) θ₀ θ₂ →
      κ₁ * t * lam * Real.sqrt (l2NormSq θ₀) ≤
        2 * (Real.sqrt (l2NormSq (θ₁ t)) - Real.sqrt (l2NormSq (θ₂ t)))

end AVenhance.Infra.FullTheorem
