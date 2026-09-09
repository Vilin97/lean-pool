/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalPrimaryFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudgetTimeChange

/-! The literal compact terminal wave initializes the mean-time packet budget. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (hR : wordRadius (Fin 4) δ ≤ L.R)
  (W : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))

include hδ1 hα hR W

theorem joinedTerminalPrimary_budget (S : Scales (Icc (0 : ℝ) M.T))
    (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile) :
    ProfileBudget (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs)) S L.R 1 := by
  have hg : (S.changeTime hTime).growth=α • L.fullProfile :=
    (S.growth_changeTime hTime).trans hgrowth
  have hD := primary_profile_budget H NB δ hδ hδ1 ξ hs α hα hR W
    (joinedSourceOperators period M D τ hτ hτT B) rfl (S.changeTime hTime) hg
  have hM := hD.changeTime hTime.symm M.T_pos.le
  simpa only [Scales.changeTime_roundtrip, joinedTerminalPrimaryWitness, joinedTerminalPrimary]
      using hM

end EulerPacketTerminalDatum
