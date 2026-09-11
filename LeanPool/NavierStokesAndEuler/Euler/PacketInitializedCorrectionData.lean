/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionConstants
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalPrimaryFields
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalPrimaryBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketApproximationBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedUniformProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketNormalDriftBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketTailBase
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileTailEstimates
public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailActual
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceEquations
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceEquations
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveResidual
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceConstraints
public import LeanPool.NavierStokesAndEuler.Euler.PacketJetAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePiola
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPiolaPair

/-! The fully initialized finite packet supplies the actual all-order data
of the correction equation, with its derived word estimates. -/

section

/-! The literal terminal wave yields the actual finite packet, its small normal
drift, and its exponentially small residual.  Primary bounds and the primary
equation are supplied by the construction itself. -/

section

/-! The actual finite joined packet, including its terminal corrector, satisfies the lifted
constraint. -/

section

/-! Every joined high/corrector pair lies in the actual lifted solenoidal space. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerLpCylinderPaths
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

/-- Joined pair field used in packet joined source piola. -/
def joinedPairField (κ : ℝ) (p : ℕ) :
    Field P M.T (fun z => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame z
      (κ^p • (joinedSourceProfiles P M D τ hτ hτT B primary p).high z +
        κ^(p+1) • (joinedSourceProfiles P M D τ hτ hτT B primary p).corrector z)) :=
  (joinedSourceCoefficientData P M D τ hτ hτT B hT).inverse.multiply
    (((joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p).high.smul (κ^p)).add
      ((joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p).corrector.smul
          (κ^(p+1))))

theorem joinedPairField_mem
    (hc : primary.corrector = D.curlCorrector P primary.high)
    (hm : ∀ (t : Icc (0 : ℝ) M.T) x, (∫ θ in (0 : ℝ)..P, primary.high (t, (x, θ))) = 0)
    (ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)
    (κ : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hT t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hT t) x)).det = 1) :
    (joinedPairField P M D hT τ hτ hτT B primary hprimary κ p).path t ∈
      divergenceFreeSpace P κ D.m₀ := by
  let W := joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p
  let G := W.high.changeTime hT
  let C := (W.corrector.congr (fun _ _ _ => by
    rw [joinedSource_corrector_eq P M D τ hτ hτT B primary hc p hp])).changeTime hT
  let V := piolaPairField D G C κ p
  have hs : G.path (sourceTime M D hT t) ∈ Supported P Space D.support D.support_measurable :=
    G.supported_of_raw_zero D.support D.support_measurable
      (raw_zero_changeTime hT D.support W.high_zero) _
  have hm' : ∀ x, (∫ θ in (0 : ℝ)..P,
      (joinedSourceProfiles P M D τ hτ hτT B primary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    joinedSource_high_mean_zero P M D hT τ hτ hτT B primary hprimary hm p hp t
  have ht' : ∀ x θ, inner ℝ (D.normalField (sourceTime M D hT t,(x,θ)))
      ((joinedSourceProfiles P M D τ hτ hτT B primary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    joinedSource_high_tangent_all P M D hT τ hτ hτT B primary hprimary ht p hp t
  have hV : V.path (sourceTime M D hT t) ∈ divergenceFreeSpace P κ D.m₀ :=
    piolaPairField_mem D G C κ p (sourceTime M D hT t) Ξ hΞ hF hdet hs hm' ht'
  let H := joinedPairField P M D hT τ hτ hτT B primary hprimary κ p
  have he : (H.changeTime hT).path = V.path := by
    apply Field.path_eq_of_raw_eq
    intro r x θ
    change D.FInv.field (D.clamp r) x
        (κ^p • (joinedSourceProfiles P M D τ hτ hτT B primary p).high (r,(x,θ)) +
          κ^(p+1) • D.curlCorrector P (joinedSourceProfiles P M D τ hτ hτT B primary p).high
              (r,(x,θ))) =
      D.FInv.field (D.clamp r) x
        (κ^p • (joinedSourceProfiles P M D τ hτ hτT B primary p).high (r,(x,θ)) +
          κ^(p+1) • (joinedSourceProfiles P M D τ hτ hτT B primary p).corrector (r,(x,θ)))
    rw [joinedSource_corrector_eq P M D τ hτ hτT B primary hc p hp]
  have hev : H.path t = V.path (sourceTime M D hT t) :=
    (H.changeTime_apply hT t).symm.trans (congrArg (fun q => q (sourceTime M D hT t)) he)
  rw [hev]
  exact hV

end EulerPacketCylinderField

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory Finset EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerFiniteGrades
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

/-- Joined packet pullback field used in packet joined source solenoidal. -/
def joinedPacketPullbackField (N : ℕ) (κ : ℝ) :
    Field P M.T (fun z => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame z
      (fieldSum (N+1) κ (assembledVelocity N (joinedSourceProfiles P M D τ hτ hτT B primary)) z))
          := by
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  let term := fun i : ℕ =>
    (joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).add
      ((joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).smul (κ^(i+1)))
  let total := Field.finsetSum (range N) _ term
  refine total.congr ?_
  intro t x θ
  have ha0 : a 0 = 0 := profiles_zero _ _
  have hu0 : (a 0).high+(a 0).mean = (0 : VectorField) := by rw [ha0]; simp
  have hc0 : (a 0).corrector = (0 : VectorField) := by rw [ha0]; rfl
  have he := fieldSum_assemble_from_one N κ (fun i => (a i).high+(a i).mean)
    (fun i => (a i).corrector) hu0 hc0 (t,(x,θ))
  change (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
    (fieldSum (N+1) κ (assemble N (fun i => (a i).high+(a i).mean)
      (fun i => (a i).corrector)) (t,(x,θ))) = _
  rw [he,map_sum,Finset.sum_apply]
  apply sum_congr rfl
  intro i _
  change (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
      (κ^(i+1) • ((a (i+1)).high (t,(x,θ))+(a (i+1)).mean (t,(x,θ))) +
        κ^(i+2) • (a (i+1)).corrector (t,(x,θ))) =
    (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
      (κ^(i+1) • (a (i+1)).high (t,(x,θ)) + κ^(i+2) • (a (i+1)).corrector (t,(x,θ))) +
      κ^(i+1) • (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ)) ((a (i+1)).mean
          (t,(x,θ)))
  simp only [map_add,map_smul,smul_add]
  abel

theorem joinedPacketPullbackField_path (N : ℕ) (κ : ℝ) :
    (joinedPacketPullbackField P M D hT τ hτ hτT B primary hprimary N κ).path =
      ∑ i ∈ range N, ((joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).path +
        κ^(i+1) • (joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).path) := rfl

theorem joinedPacketPullbackField_mem
    (hmean : primary.mean = 0)
    (hc : primary.corrector = D.curlCorrector P primary.high)
    (hm : ∀ (t : Icc (0 : ℝ) M.T) x, (∫ θ in (0 : ℝ)..P, primary.high (t, (x, θ))) = 0)
    (ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)
    (A : SourceCoefficientAgreement M D) (N : ℕ) (κ : ℝ) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hT t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hT t) x)).det = 1) :
    (joinedPacketPullbackField P M D hT τ hτ hτT B primary hprimary N κ).path t ∈
      divergenceFreeSpace P κ D.m₀ := by
  rw [joinedPacketPullbackField_path]
  have he : (∑ i ∈ range N, ((joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).path +
        κ^(i+1) • (joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).path)) t =
      ∑ i ∈ range N, ((joinedPairField P M D hT τ hτ hτT B primary hprimary κ (i+1)).path t +
        κ^(i+1) • (joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary (i+1)).path t) :=
    map_sum (ContinuousMap.evalCLM ℝ t) _ (range N)
  rw [he]
  apply (divergenceFreeSpace P κ D.m₀).sum_mem
  intro i _
  apply (divergenceFreeSpace P κ D.m₀).add_mem
  · exact joinedPairField_mem P M D hT τ hτ hτT B primary hprimary hc hm ht κ (i+1) (by
      omega) t Ξ hΞ hF hdet
  · exact (divergenceFreeSpace P κ D.m₀).smul_mem (κ^(i+1))
      (joinedMeanPullbackField_mem P M D hT τ hτ hτT B primary hprimary hmean A κ D.m₀ (i+1) t)

end EulerPacketCylinderField

end
end

end

section

/-! Actual tail-grade and full residual fields for the joined source construction. -/

section

/-!
The actual finite packet built by the complete joined inverse has precisely
the uncancelled tail.  The primary field and its homogeneous equation are
inputs; every nonprimary regularity and equation is discharged by construction.
-/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (A : VectorField) (π : ScalarField)

/-- Joined primary profiles: an abbreviation for `joinedSourceProfiles P M D τ hτ hτT B
(primaryProfile (joinedSourceOperators P M D τ hτ hτT B) A π)`. -/
abbrev joinedPrimaryProfiles : ℕ → Profile :=
  joinedSourceProfiles P M D τ hτ hτT B
    (primaryProfile (joinedSourceOperators P M D τ hτ hτT B) A π)

include hT in
theorem joinedSource_residual_tail
    (hprimary : ProfileRegularity P M.T M.T_pos.le D.support
      (primaryProfile (joinedSourceOperators P M D τ hτ hτT B) A π))
    (hπ : ∀ t : Icc (0 : ℝ) M.T, ContDiff ℝ ∞ (fun y : Space × ℝ => π (t,y)))
    (htan : ∀ (t : Icc (0 : ℝ) M.T) x θ, inner ℝ (D.normalField (t,(x,θ))) (A (t,(x,θ))) = 0)
    (hprimaryEquation : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) M.T) A (t,(x,θ))) +
        fastPressure (D.normalField (t,(x,θ))) (pressureJet π (t,(x,θ))) = 0)
    (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    slicedMomentumResidual (Icc (0 : ℝ) M.T) κ
        ((joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ)))
        ((joinedSourceOperators P M D τ hτ hτT B).strain (t,(x,θ)))
        ((joinedSourceOperators P M D τ hτ hτT B).normal (t,(x,θ)))
        (fieldSum (N+1) κ (assembledVelocity N (joinedPrimaryProfiles P M D τ hτ hτT B A π)))
        (fieldSum (N+1) κ (assembledPressure N (joinedPrimaryProfiles P M D τ hτ hτT B A π)))
            (t,(x,θ)) =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n •
        recursiveGrade (joinedSourceOperators P M D τ hτ hτT B) N
          (joinedPrimaryProfiles P M D τ hτ hτT B A π) (t,(x,θ)) n := by
  apply recursive_residual_tail (joinedSourceOperators P M D τ hτ hτT B) A π N hN κ hκ (t,(x,θ))
  · exact (uniqueDiffOn_Icc M.T_pos) _ t.property
  · intro p
    exact joinedSource_high_slice P M D hT τ hτ hτT B _ hprimary p t x θ
  · intro p
    exact joinedSource_mean_slice P M D hT τ hτ hτT B _ hprimary p t x θ
  · intro p
    exact joinedSource_corrector_slice P M D hT τ hτ hτT B _ hprimary p t x θ
  · intro p
    exact (joinedSource_meanPressure_smooth_all P M D hT τ hτ hτT B _ hprimary rfl p
        t).differentiable
      (by simp) (x,θ)
  · intro p
    exact (joinedSource_highPressure_smooth_all P M D hT τ hτ hτT B _ hprimary hπ p
        t).differentiable
      (by simp) (x,θ)
  · intro p _
    change (pressureJet (joinedPrimaryProfiles P M D τ hτ hτT B A π p).meanPressure (t,(x,θ))).2
      angleDirection • ((joinedSourceOperators P M D τ hτ hτT B).normal (t,(x,θ))) = (0 : Space)
    rw [joinedSource_meanPressure_angle_all P M D hT τ hτ hτT B _ hprimary rfl p t x θ,zero_smul]
  · exact htan t x θ
  · exact hprimaryEquation t x θ
  · intro p hp _
    exact joinedSource_high_tangent P M D hT τ hτ hτT B _ hprimary p hp t x θ
  · intro p hp _
    exact joinedSource_mean_equation P M D hT τ hτ hτT B _ hprimary Cagree p hp t x θ
  · intro p hp _
    exact joinedSource_high_equation P M D hT τ hτ hτT B _ hprimary p hp t x θ

end EulerPacketCylinderField

end
end

end

@[expose] public section

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

/-- Joined tail grade field, constructed using `ProfileRegularity.tailGradeField`. -/
def joinedTailGradeField (N n : ℕ) (hn : N + 1 ≤ n) :
    Field P M.T (fun z => recursiveGrade (joinedSourceOperators P M D τ hτ hτT B) N
      (joinedSourceProfiles P M D τ hτ hτT B primary) z n) :=
  ProfileRegularity.tailGradeField M.T_pos
    (fun i _ => joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary i)
    (joinedSourceCoefficientData P M D τ hτ hτT B hT) (profiles_zero _ _) n hn

/-- Joined literal tail grade field, constructed using
`ProfileRegularity.literalTailGradeField`. -/
def joinedLiteralTailGradeField (N n : ℕ) (hn : N + 1 ≤ n) :
    Field P M.T (fun z => slicedMomentumGrade (Icc (0 : ℝ) M.T) (N+1)
      ((joinedSourceOperators P M D τ hτ hτT B).inverseFrame z)
      ((joinedSourceOperators P M D τ hτ hτT B).strain z)
      ((joinedSourceOperators P M D τ hτ hτT B).normal z)
      (assembledVelocity N (joinedSourceProfiles P M D τ hτ hτT B primary))
      (assembledPressure N (joinedSourceProfiles P M D τ hτ hτT B primary)) z n) :=
  ProfileRegularity.literalTailGradeField M.T_pos
    (fun i _ => joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary i)
    (joinedSourceCoefficientData P M D τ hτ hτT B hT) (profiles_zero _ _) n hn

theorem joinedLiteralTailGradeField_path (N n : ℕ) (hn : N + 1 ≤ n) :
    (joinedLiteralTailGradeField P M D hT τ hτ hτT B primary hprimary N n hn).path =
      (joinedTailGradeField P M D hT τ hτ hτT B primary hprimary N n hn).path := rfl

/-- Joined tail sum field, constructed using `ProfileRegularity.tailSumField`. -/
def joinedTailSumField (N : ℕ) (κ : ℝ) :
    Field P M.T (fun z => ∑ n ∈ Ico (N+1) (2*N+3), κ^n •
      recursiveGrade (joinedSourceOperators P M D τ hτ hτT B) N
        (joinedSourceProfiles P M D τ hτ hτT B primary) z n) :=
  ProfileRegularity.tailSumField M.T_pos
    (fun i _ => joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary i)
    (joinedSourceCoefficientData P M D τ hτ hτT B hT) (profiles_zero _ _) κ

omit primary hprimary in
/-- Joined residual field used in packet joined residual fields. -/
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

end
end

end

section

/-! Exponential residual bounds for the actual recursively solved joined packet. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey EulerPacketCoarseMajorant
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := P) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData P M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (S : Scales (Icc (0 : ℝ) M.T)) (α : ℝ) (hα : 0 < α)
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (hprimaryBudget : ProfileBudget hprimary S L.R 1)
  (hprimaryMean : primary.mean = 0)
  (hprimaryTangent : ∀ (t : Icc (0 : ℝ) M.T) x θ,
    inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)

include NB W LM WM BC hRc hcost hα hgrowth hprimaryBudget hprimaryMean hprimaryTangent

theorem joinedTailSum_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ))
    (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ)) :
    (((joinedSourceCoefficientData P M D τ hτ hτT B hTime).inverse.multiply
      (joinedTailSumField P M D hTime τ hτ hτT B primary hprimary N k⁻¹)).smul k).WordBound
        6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 := by
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => joinedSource_profile_budgets P M D hTime τ hτ hτT B L NB W LM WM BC
      hRc hcost S α hα hgrowth primary hprimary hprimaryBudget hprimaryMean hprimaryTangent i hi
  have ha : a 0=0 := profiles_zero _ _
  have hb : (a 1).mean=0 := by
    simpa only [a,joinedSourceProfiles,profiles_one] using hprimaryMean
  exact ProfileRegularity.normalized_tail_bound M.T_pos G BC hG hN L.radius_bounds.1 hRc ha hb
    k X hk hbase hcoef hX hNX

omit primary hprimary hprimaryBudget hprimaryMean hprimaryTangent in
/-- All later-grade bounds and equations are proved by the actual source
recursion. The remaining hypotheses are the fixed source and primary data,
and the explicit scalar frequency guards. -/
theorem joinedResidual_normalized_bound (A : VectorField) (π : ScalarField)
    (hp : ProfileRegularity P M.T M.T_pos.le D.support
      (primaryProfile (joinedSourceOperators P M D τ hτ hτT B) A π))
    (hpBudget : ProfileBudget hp S L.R 1)
    (hπ : ∀ t : Icc (0 : ℝ) M.T, ContDiff ℝ ∞ (fun y : Space × ℝ => π (t,y)))
    (htan : ∀ (t : Icc (0 : ℝ) M.T) x θ, inner ℝ (D.normalField (t,(x,θ))) (A (t,(x,θ))) = 0)
    (hpEquation : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) M.T) A (t,(x,θ))) +
        fastPressure (D.normalField (t,(x,θ))) (pressureJet π (t,(x,θ)))=0)
    (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k^(1/100 : ℝ))
    (hX : 6 ≤ X) (hNX : X-1 ≤ (N : ℝ)) :
    (((joinedSourceCoefficientData P M D τ hτ hτT B hTime).inverse.multiply
      (joinedResidualField P M D hTime τ hτ hτT B A π hp hπ htan hpEquation Cagree N hN
        k⁻¹ (inv_ne_zero (by linarith)))).smul k).WordBound
          6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 := by
  have h := joinedTailSum_normalized_bound P M D hTime τ hτ hτT B L NB W LM WM BC
    hRc hcost S α hα hgrowth
    (primaryProfile (joinedSourceOperators P M D τ hτ hτT B) A π) hp hpBudget rfl htan
    N hN k X hk hbase hcoef hX hNX
  exact h.of_path_eq _ rfl

end EulerPacketCylinderField

end
end

end

section

/-! The actual joined packet has a bounded normalized velocity and a small normal drift. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey EulerPacketCoarseMajorant

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := P) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData P M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (S : Scales (Icc (0 : ℝ) M.T)) (α : ℝ) (hα : 0 < α)
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (hprimaryBudget : ProfileBudget hprimary S L.R 1)
  (hprimaryMean : primary.mean = 0)
  (hprimaryTangent : ∀ (t : Icc (0 : ℝ) M.T) x θ,
    inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)

include NB W LM WM BC hRc hcost hα hgrowth hprimaryBudget hprimaryMean hprimaryTangent

theorem joinedPacket_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((joinedPacketPullbackField P M D hTime τ hτ hτT B primary hprimary N k⁻¹).smul k).WordBound
      6 (4*L.R) (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 1 +
        fixedVelocityGradeCost L.R S.H0 2+1)) 0 := by
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => joinedSource_profile_budgets P M D hTime τ hτ hτT B L NB W LM WM BC
      hRc hcost S α hα hgrowth primary hprimary hprimaryBudget hprimaryMean hprimaryTangent i hi
  have h := ProfileRegularity.normalizedVelocity_bound M.T_pos G hG L.radius_bounds.1
    (profiles_zero _ _) hN BC hRc k hk hbase
  exact h.ofRawEq _ (fun _ _ _ => rfl)

theorem joinedPacket_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (((joinedPacketPullbackField P M D hTime τ hτ hτT B primary hprimary N k⁻¹).smul k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R)
        (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 2+2)/k) 0 := by
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => joinedSource_profile_budgets P M D hTime τ hτ hτT B L NB W LM WM BC
      hRc hcost S α hα hgrowth primary hprimary hprimaryBudget hprimaryMean hprimaryTangent i hi
  have hb : (a 1).mean=0 := by
    simpa only [a,joinedSourceProfiles,profiles_one] using hprimaryMean
  have ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ D.m₀ ((joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
        ((a 1).high (t,(x,θ))))=0 := by
    intro t x θ
    have h := hprimaryTangent t x θ
    change inner ℝ ((D.FInv.field (D.clamp t) x).adjoint D.m₀) (primary.high (t,(x,θ)))=0 at h
    rw [ContinuousLinearMap.adjoint_inner_left] at h
    change inner ℝ D.m₀ (D.FInv.field (D.clamp t) x ((a 1).high (t,(x,θ))))=0
    simpa only [a,joinedSourceProfiles,profiles_one] using h
  have h := ProfileRegularity.normalizedNormal_bound M.T_pos G hG L.radius_bounds.1
    (profiles_zero _ _) hb hN BC hRc D.m₀ D.m₀_unit.le ht k hk hbase
  exact h.ofRawEq _ (fun _ _ _ => rfl)

end EulerPacketCylinderField

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Initialized packet field, constructed using `joinedPacketPullbackField`. -/
def initializedPacketField (N : ℕ) (κ : ℝ) :=
  joinedPacketPullbackField period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) N κ

/-- Initialized residual field, constructed using `joinedResidualField`. -/
def initializedResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) :=
  joinedResidualField period M D hTime τ hτ hτT B
    (EulerTransversePacketPrimary.vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (EulerTransversePacketPrimary.scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (fun t => joinedTerminalPrimary_pressure_smooth period M D τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) t.val)
    (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_equation period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    Cagree N hN κ hκ

variable
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedPacket_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).smul k).WordBound
      6 (4*L.R) (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 1 +
        fixedVelocityGradeCost L.R S.H0 2+1)) 0 :=
  joinedPacket_normalized_bound period M D hTime τ hτ hτT B L NB W LM WM BC hRc hcost S α hα hgrowth
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_budget M D hTime τ hτ hτT B L H NB δ hδ hδ1 ξ hs α hα hR WP S hgrowth)
    rfl (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs)) N hN k hk hbase

theorem initializedPacket_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).smul k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R)
        (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 2+2)/k) 0 :=
  joinedPacket_normal_bound period M D hTime τ hτ hτT B L NB W LM WM BC hRc hcost S α hα hgrowth
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_budget M D hTime τ hτ hτT B L H NB δ hδ hδ1 ξ hs α hα hR WP S hgrowth)
    rfl (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs)) N hN k hk hbase

theorem initializedResidual_normalized_bound (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ)) (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ)) :
    (((joinedSourceCoefficientData period M D τ hτ hτT B hTime).inverse.multiply
      (initializedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k⁻¹
        (inv_ne_zero (by linarith)))).smul k).WordBound
          6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 :=
  joinedResidual_normalized_bound period M D hTime τ hτ hτT B L NB W LM WM BC hRc hcost S α hα
      hgrowth
    (EulerTransversePacketPrimary.vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (EulerTransversePacketPrimary.scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_budget M D hTime τ hτ hτT B L H NB δ hδ hδ1 ξ hs α hα hR WP S hgrowth)
    (fun t => joinedTerminalPrimary_pressure_smooth period M D τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) t.val)
    (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_equation period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    Cagree N hN k X hk hbase hcoef hX hNX

end EulerPacketTerminalDatum

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Initialized normalized field, given by `((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ
hs α N k⁻¹).smul k).changeTime hTime`. -/
def initializedNormalizedField (N : ℕ) (k : ℝ) :=
  ((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).smul k).changeTime hTime

/-- Initialized normalized residual field used in packet initialized correction data. -/
def initializedNormalizedResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :=
  (((joinedSourceCoefficientData period M D τ hτ hτT B hTime).inverse.multiply
    (initializedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k⁻¹
      (inv_ne_zero (by linarith)))).smul k).changeTime hTime

/-- Initialized correction data, constructed using
`EulerPacketCorrectionCoefficients.correctionDataOfFields`. -/
def initializedCorrectionData (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    EulerAllOrderCorrectionData.Data period D.T :=
  EulerPacketCorrectionCoefficients.correctionDataOfFields D period k⁻¹
    (by rw [abs_of_pos (inv_pos.mpr (by linarith : 0 < k))]
        exact inv_le_one_of_one_le₀ (by linarith))
    (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k)
    (initializedNormalizedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk)

variable
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedNormalizedField_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).WordBound
      6 (4*L.R) (velocity L.R S.H0 BC.multiplierCost) 0 :=
  (initializedPacket_normalized_bound M D hTime τ hτ hτT B δ hδ ξ hs α L H NB W LM WM BC
    hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).changeTime hTime

theorem initializedNormalizedField_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R) (normal L.R S.H0 BC.multiplierCost/k) 0 := by
  have hh := (initializedPacket_normal_bound M D hTime τ hτ hτT B δ hδ ξ hs α L H NB W LM WM BC
    hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).changeTime hTime
  exact hh.ofRawEq _ (fun _ _ _ => rfl)

theorem initializedNormalizedResidualField_bound (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ)) (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ)) :
    (initializedNormalizedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk).WordBound
      6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 :=
  (initializedResidual_normalized_bound M D hTime τ hτ hτT B δ hδ ξ hs α L H NB W LM WM BC
    hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k X hk hbase hcoef hX hNX).changeTime hTime

end EulerPacketTerminalDatum
