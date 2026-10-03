/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.NextStreamAdmissible
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

/-- Closure of admissible stream functions under the one-step map of `e.psi.recursion`
(source 1457-1461: "clearly smooth", periodicity 1474-1486). Needs joint
`C^∞` dependence of the flow inverse on `(t,x)`, lattice equivariance and
time-shift periodicity of the flow (`flow_lattice_equivariant`, `flow_time_shift_one`), and the
integrality of `1/τ_m`, `1/τ''_m` with `1/τ_m ≡ 0 mod 4`. -/
theorem IsAdmissibleStream.nextStream_isAdmissible {β : ℝ} (I : Ingredients β) (m : ℕ) (hm : 1 ≤ m)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) :
    IsAdmissibleStream (I.nextStream m φ hφ) := by
  exact AVenhance.Proofs.IsAdmissibleStream.nextStream_isAdmissible I m hm φ hφ

end AVenhance
