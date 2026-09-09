/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveResidual

@[expose] public section

/-!
The actual finite packet built by the complete joined inverse has precisely
the uncancelled tail.  The primary field and its homogeneous equation are
inputs; every nonprimary regularity and equation is discharged by construction.
-/

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
