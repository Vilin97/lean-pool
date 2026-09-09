/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailActual
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceResidual

@[expose] public section

/-! Actual tail-grade and full residual fields for the joined source construction. -/

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

def joinedTailGradeField (N n : ℕ) (hn : N+1 ≤ n) :
    Field P M.T (fun z => recursiveGrade (joinedSourceOperators P M D τ hτ hτT B) N
      (joinedSourceProfiles P M D τ hτ hτT B primary) z n) :=
  ProfileRegularity.tailGradeField M.T_pos
    (fun i _ => joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary i)
    (joinedSourceCoefficientData P M D τ hτ hτT B hT) (profiles_zero _ _) n hn

def joinedLiteralTailGradeField (N n : ℕ) (hn : N+1 ≤ n) :
    Field P M.T (fun z => slicedMomentumGrade (Icc (0 : ℝ) M.T) (N+1)
      ((joinedSourceOperators P M D τ hτ hτT B).inverseFrame z)
      ((joinedSourceOperators P M D τ hτ hτT B).strain z)
      ((joinedSourceOperators P M D τ hτ hτT B).normal z)
      (assembledVelocity N (joinedSourceProfiles P M D τ hτ hτT B primary))
      (assembledPressure N (joinedSourceProfiles P M D τ hτ hτT B primary)) z n) :=
  ProfileRegularity.literalTailGradeField M.T_pos
    (fun i _ => joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary i)
    (joinedSourceCoefficientData P M D τ hτ hτT B hT) (profiles_zero _ _) n hn

theorem joinedLiteralTailGradeField_path (N n : ℕ) (hn : N+1 ≤ n) :
    (joinedLiteralTailGradeField P M D hT τ hτ hτT B primary hprimary N n hn).path =
      (joinedTailGradeField P M D hT τ hτ hτT B primary hprimary N n hn).path := rfl

def joinedTailSumField (N : ℕ) (κ : ℝ) :
    Field P M.T (fun z => ∑ n ∈ Ico (N+1) (2*N+3), κ^n •
      recursiveGrade (joinedSourceOperators P M D τ hτ hτT B) N
        (joinedSourceProfiles P M D τ hτ hτT B primary) z n) :=
  ProfileRegularity.tailSumField M.T_pos
    (fun i _ => joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary i)
    (joinedSourceCoefficientData P M D τ hτ hτT B hT) (profiles_zero _ _) κ

omit primary hprimary in
def joinedResidualField (A : VectorField) (π : ScalarField)
    (hprimary : ProfileRegularity P M.T M.T_pos.le D.support
      (primaryProfile (joinedSourceOperators P M D τ hτ hτT B) A π))
    (hπ : ∀ t : Icc (0 : ℝ) M.T, ContDiff ℝ ∞ (fun y : Space × ℝ => π (t,y)))
    (htan : ∀ (t : Icc (0 : ℝ) M.T) x θ, inner ℝ (D.normalField (t,(x,θ))) (A (t,(x,θ))) = 0)
    (hprimaryEquation : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) M.T) A (t,(x,θ))) +
        fastPressure (D.normalField (t,(x,θ))) (pressureJet π (t,(x,θ))) = 0)
    (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) :
    Field P M.T (fun z => slicedMomentumResidual (Icc (0 : ℝ) M.T) κ
      ((joinedSourceOperators P M D τ hτ hτT B).inverseFrame z)
      ((joinedSourceOperators P M D τ hτ hτT B).strain z)
      ((joinedSourceOperators P M D τ hτ hτT B).normal z)
      (fieldSum (N+1) κ (assembledVelocity N (joinedPrimaryProfiles P M D τ hτ hτT B A π)))
      (fieldSum (N+1) κ (assembledPressure N (joinedPrimaryProfiles P M D τ hτ hτT B A π))) z) :=
  (joinedTailSumField P M D hT τ hτ hτT B
    (primaryProfile (joinedSourceOperators P M D τ hτ hτT B) A π) hprimary N κ).congr
    (joinedSource_residual_tail P M D hT τ hτ hτT B A π hprimary hπ htan hprimaryEquation Cagree N
      hN κ hκ)

end EulerPacketCylinderField
