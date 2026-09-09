/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceOperators
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedProvider

@[expose] public section

/-! Literal source operators with the complete positive-history-time high inverse. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))

def joinedSourceOperators : Operators where
  interval := Icc (0 : ℝ) M.T
  period := P
  inverseFrame z := D.FInv.field (D.clamp z.1) z.2.1
  strain := D.strain
  normal := D.normalField
  meanSolve := EulerMeanPacketProvider.meanSolve M
  highSolve := EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B
  curlCorrector := D.curlCorrector P

def joinedSourceCoefficientData (hT : M.T = D.T) :
    CoefficientData P M.T (joinedSourceOperators P M D τ hτ hτT B) where
  period_eq := rfl
  interval_eq := rfl
  inverse := (sourceCoefficientData P M D (EulerTransversePacketProvider.InitialData.zero P D)
    hT).inverse
  strain := (sourceCoefficientData P M D (EulerTransversePacketProvider.InitialData.zero P D)
    hT).strain
  normal := (sourceCoefficientData P M D (EulerTransversePacketProvider.InitialData.zero P D)
    hT).normal

end EulerPacketCylinderField
