/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailActual
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceResidual

/-! Actual tail-grade and full residual fields for the source construction.
The full residual is identified with its finite tail by the equations of the
constructed mean and forward solutions. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

/-- Source tail grade field, constructed using `ProfileRegularity.tailGradeField`. -/
def sourceTailGradeField (N n : ℕ) (hn : N + 1 ≤ n) :
    Field P M.T (fun z => recursiveGrade (sourceOperators P M D I) N
      (sourceProfiles P M D I Iprimary) z n) :=
  ProfileRegularity.tailGradeField M.T_pos
    (fun i _ => sourceProfileWitness P M D hT I Iprimary i)
    (sourceCoefficientData P M D I hT) (profiles_zero _ _) n hn

/-- Source literal tail grade field, constructed using
`ProfileRegularity.literalTailGradeField`. -/
def sourceLiteralTailGradeField (N n : ℕ) (hn : N + 1 ≤ n) :
    Field P M.T (fun z => slicedMomentumGrade (Icc (0 : ℝ) M.T) (N+1)
      ((sourceOperators P M D I).inverseFrame z)
      ((sourceOperators P M D I).strain z)
      ((sourceOperators P M D I).normal z)
      (assembledVelocity N (sourceProfiles P M D I Iprimary))
      (assembledPressure N (sourceProfiles P M D I Iprimary)) z n) :=
  ProfileRegularity.literalTailGradeField M.T_pos
    (fun i _ => sourceProfileWitness P M D hT I Iprimary i)
    (sourceCoefficientData P M D I hT) (profiles_zero _ _) n hn

theorem sourceLiteralTailGradeField_path (N n : ℕ) (hn : N + 1 ≤ n) :
    (sourceLiteralTailGradeField P M D hT I Iprimary N n hn).path =
      (sourceTailGradeField P M D hT I Iprimary N n hn).path := rfl

/-- Source tail sum field, constructed using `ProfileRegularity.tailSumField`. -/
def sourceTailSumField (N : ℕ) (κ : ℝ) :
    Field P M.T (fun z => ∑ n ∈ Ico (N+1) (2*N+3), κ^n •
      recursiveGrade (sourceOperators P M D I) N (sourceProfiles P M D I Iprimary) z n) :=
  ProfileRegularity.tailSumField M.T_pos
    (fun i _ => sourceProfileWitness P M D hT I Iprimary i)
    (sourceCoefficientData P M D I hT) (profiles_zero _ _) κ

/-- Source residual field, given by `(sourceTailSumField P M D hT I Iprimary N κ).congr
(source_residual_tail P M D hT I Iprimary Cagree N hN κ hκ)`. -/
def sourceResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) :
    Field P M.T (fun z => slicedMomentumResidual (Icc (0 : ℝ) M.T) κ
      ((sourceOperators P M D I).inverseFrame z)
      ((sourceOperators P M D I).strain z)
      ((sourceOperators P M D I).normal z)
      (fieldSum (N+1) κ (assembledVelocity N (sourceProfiles P M D I Iprimary)))
      (fieldSum (N+1) κ (assembledPressure N (sourceProfiles P M D I Iprimary))) z) :=
  (sourceTailSumField P M D hT I Iprimary N κ).congr
    (source_residual_tail P M D hT I Iprimary Cagree N hN κ hκ)

end EulerPacketCylinderField
