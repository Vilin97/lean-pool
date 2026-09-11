/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailActual
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceEquations
import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveResidual
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceRegularity

/-! Actual tail-grade and full residual fields for the source construction.
The full residual is identified with its finite tail by the equations of the
constructed mean and forward solutions. -/

section

/-!
# The actual constructed source packet has only the uncancelled residual tail

All profile regularity, tangency, and defining equations in the generic
algebraic expansion are discharged by the actual recursive source solves.
-/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

include hT in
theorem source_residual_tail (A : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    slicedMomentumResidual (Icc (0 : ℝ) M.T) κ
        ((sourceOperators P M D I).inverseFrame (t,(x,θ)))
        ((sourceOperators P M D I).strain (t,(x,θ)))
        ((sourceOperators P M D I).normal (t,(x,θ)))
        (fieldSum (N+1) κ (assembledVelocity N (sourceProfiles P M D I Iprimary)))
        (fieldSum (N+1) κ (assembledPressure N (sourceProfiles P M D I Iprimary))) (t,(x,θ)) =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n •
        recursiveGrade (sourceOperators P M D I) N (sourceProfiles P M D I Iprimary) (t,(x,θ)) n :=
            by
  apply recursive_residual_tail (sourceOperators P M D I)
    ((homogeneousForcing (P := P) D).vector Iprimary)
    ((homogeneousForcing (P := P) D).scalar Iprimary) N hN κ hκ (t,(x,θ))
  · exact (uniqueDiffOn_Icc M.T_pos) _ t.property
  · intro p
    exact source_high_slice P M D hT I Iprimary p t x θ
  · intro p
    exact source_mean_slice P M D hT I Iprimary p t x θ
  · intro p
    exact source_corrector_slice P M D hT I Iprimary p t x θ
  · intro p
    exact (source_meanPressure_smooth P M D hT I Iprimary p t).differentiable (by simp) (x,θ)
  · intro p
    exact (source_highPressure_smooth P M D hT I Iprimary p t).differentiable (by simp) (x,θ)
  · intro p _
    change (pressureJet (sourceProfiles P M D I Iprimary p).meanPressure (t,(x,θ))).2
      angleDirection • ((sourceOperators P M D I).normal (t,(x,θ))) = (0 : Space)
    rw [source_meanPressure_angle P M D hT I Iprimary p t x θ,zero_smul]
  · exact (homogeneousForcing (P := P) D).vector_tangent Iprimary t x θ
  · exact source_primary_equation P M D hT I Iprimary t x θ
  · intro p _ _
    exact source_high_tangent P M D hT I Iprimary p t x θ
  · intro p hp _
    exact source_mean_equation P M D hT I Iprimary A p hp t x θ
  · intro p hp _
    exact source_high_equation P M D hT I Iprimary p hp t x θ

end EulerPacketCylinderField

end
end

end

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
