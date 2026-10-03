/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialFlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialPullback

/-! Temporal material-Jacobian consequences of the source flow package. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Construction

theorem MaterialFlowTime.iteratedTimeDerivative_neg_local
    {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (ell : ℕ) (f : ℝ → α) :
    iteratedTimeDerivative ell (fun t => -f t) =
      fun t => -iteratedTimeDerivative ell f t := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      funext t
      simp [iteratedTimeDerivative, ih]

end AVenhance.Infra.Construction

end
