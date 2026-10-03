/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.FlowTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialGoalSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition

/-! Material transport commutes with composition by an inverse-flow
coordinate. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Construction

theorem MaterialComposition.iteratedTimeDerivative_contDiff {q : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (ell : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedTimeDerivative ell q) := by
  induction ell with
  | zero => exact hq
  | succ ell ih =>
      exact (contDiff_infty_iff_deriv.mp ih).2

end AVenhance.Infra.Construction
