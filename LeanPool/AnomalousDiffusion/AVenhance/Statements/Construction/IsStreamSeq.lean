/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStreamSummable

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Source-characterized sequence `{φ_m}` of `e.phi0def` (1423-1433) and `e.psi.recursion`:
`φ_0 = 0` and `φ_m = nextStream m φ_{m-1}` (with `φ_{m-1}` admissible) for `m ≥ 1`. -/
def IsStreamSeq {β : ℝ} (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  Φ 0 = (fun _ _ => 0) ∧
  ∀ m : ℕ, 1 ≤ m → ∃ h : IsAdmissibleStream (Φ (m - 1)), Φ m = I.nextStream m (Φ (m - 1)) h

end AVenhance
