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
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.HolderTimeL2Le
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsTransportWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.FullTheorem.LebronStep

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance
/-- Remark 5.3 of the paper (`r.LeBron`) (`e.continuous.indeed`, 9041-9051), in the context of
    `p.indystepdown`
(premises exactly those of step-down minus the iterate witness `T`):
`‖θ_m − θ_{m−1}‖_{C^{0,μ}([0,1];L²)} ≤ C ε_{m−1}^{δ/2} ‖θ₀‖_{H¹}` with `μ, C` depending only on `β`
(and the cutoff bound `C₀`). -/
theorem lebron_step (β : ℝ) (C₀ : ℝ) :
    ∃ μ C : ℝ, 0 < μ ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ θm θprev : ℝ → Vec 2 → ℝ,
        IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) θ₀ θm →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        HolderTimeL2Le μ
          (C * epsilon β I.Λ (m - 1) ^ (delta β / 2) *
            Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)))
          (fun t x => θm t x - θprev t x) := by
  exact AVenhance.Proofs.lebron_step β C₀

end AVenhance
