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

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance
/-- Time-Hölder seminorm bound on `[0,1]` with values in `L²(𝕋²)` (unit cell):
`‖θ(t) − θ(s)‖_{L²} ≤ H |t − s|^μ` for all `s, t ∈ [0,1]`. -/
def IsHolderTimeL2 (μ H : ℝ) (θ : ℝ → Vec 2 → ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤ H * |t - s| ^ μ

end AVenhance
