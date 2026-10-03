/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.FlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.StartTimeDerivative

/-! Differential identities for the inverse flow of a construction stream. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance

/-- The inverse flow satisfies the backwards transport equation. This is the
source identity `e.PDE.backwards`, derived from the initial-time derivative of
the forward flow. -/
theorem constructionFlowInv_hasDerivAt
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (t s : ℝ) (x : Vec 2) :
    HasDerivAt (fun r : ℝ => constructionFlowInv hseq m r x s)
      (-(constructionFlowInvJacobian hseq m (t - s) s x)
        (streamVel (Φ m) t x)) t := by
  let hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField (streamVel (Φ m)) :=
    Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow (streamVel (Φ m)) (constructionFlow hseq m) := by
    dsimp [constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hstart := Infra.Flow.flow_initialTime_hasDerivAt hb hX x t s
  simpa [constructionFlowInv, constructionFlowInvJacobian, constructionFlow,
    flowInv, sub_add_cancel] using hstart

end AVenhance
