/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceEquations

@[expose] public section

/-! Actual equations, tangency and pressure regularity at every solved joined grade. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

theorem joinedInverse_eq_mean (A : SourceCoefficientAgreement M D)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ)) = M.inverseFrame (t,(x,θ)) := by
  change D.FInv.field (D.clamp t) x = M.FInv (M.clamp t) x
  rw [EulerMeanPacketProvider.Data.clamp_coe]
  exact (A.inverse t x).symm

theorem joinedStrain_eq_mean (A : SourceCoefficientAgreement M D)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    (joinedSourceOperators P M D τ hτ hτT B).strain (t,(x,θ)) = M.strain (t,(x,θ)) := by
  change D.M.field (D.clamp t) x = M.M.field (M.clamp t) x
  rw [EulerMeanPacketProvider.Data.clamp_coe]
  exact (A.strain t x).symm

include hT hprimary in
theorem joinedSource_mean_equation (A : SourceCoefficientAgreement M D) (p : ℕ) (hp : 2 ≤ p)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    linearPart ((joinedSourceOperators P M D τ hτ hτT B).strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) M.T) (joinedSourceProfiles P M D τ hτ hτT B primary p).mean
          (t,(x,θ))) +
      slowPressure ((joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ)))
        (pressureJet (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure (t,(x,θ))) =
      meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) (t,(x,θ)) := by
  rw [joinedStrain_eq_mean P M D τ hτ hτT B A t x θ,
    joinedInverse_eq_mean P M D τ hτ hτT B A t x θ]
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      EulerPacketProfileRecursion.step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp
  rw [he]
  exact EulerMeanPacketProvider.meanSolve_jet_equation M _
    ⟨joinedSource_meanForcing P M D hT τ hτ hτT B primary hprimary p hp⟩ t x θ

include hT hprimary in
theorem joinedSource_high_equation (p : ℕ) (hp : 2 ≤ p)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    linearPart ((joinedSourceOperators P M D τ hτ hτT B).strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) M.T) (joinedSourceProfiles P M D τ hτ hτT B primary p).high
          (t,(x,θ))) +
      fastPressure ((joinedSourceOperators P M D τ hτ hτT B).normal (t,(x,θ)))
        (pressureJet (joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure (t,(x,θ))) =
      highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) (t,(x,θ)) := by
  let ops := joinedSourceOperators P M D τ hτ hτT B
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  have he : a p = EulerPacketProfileRecursion.step ops p a := profiles_step _ _ p hp
  change linearPart (ops.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) M.T) (a p).high (t,(x,θ))) +
    fastPressure (ops.normal (t,(x,θ))) (pressureJet (a p).highPressure (t,(x,θ))) = _
  rw [he]
  let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
  have h := EulerTransversePacketJoin.highSolve_equation τ hτ hτT B
    ⟨joinedSource_highForcing P M D hT τ hτ hτT B primary hprimary p hp⟩ td x θ
  change linearPart (D.strain (t,(x,θ)))
      (slicedJet (Icc (0 : ℝ) M.T)
        (EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B (highForce ops p a)).1 (t,(x,θ))) +
      fastPressure (D.normalField (t,(x,θ)))
        (pressureJet (EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B (highForce ops p
          a)).2 (t,(x,θ))) = _
  have hs : Icc (0 : ℝ) M.T = Icc (0 : ℝ) D.T := congrArg (Icc (0 : ℝ)) hT
  have hj := congrArg (fun s : Set ℝ => slicedJet s
    (EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B (highForce ops p a)).1 (t,(x,θ))) hs
  rw [hj]
  exact h

include hT hprimary in
theorem joinedSource_high_tangent (p : ℕ) (hp : 2 ≤ p)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    inner ℝ (D.normalField (t,(x,θ)))
      ((joinedSourceProfiles P M D τ hτ hτT B primary p).high (t,(x,θ))) = 0 := by
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSource_highForcing P M D hT τ hτ hτT B primary hprimary p hp⟩
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      EulerPacketProfileRecursion.step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp
  rw [he]
  change inner ℝ (D.normalField (t,(x,θ)))
    ((EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B _).1 (t,(x,θ))) = 0
  rw [EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B h]
  let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
  exact EulerTransversePacketJoin.vector_tangent τ hτ hτT B (Classical.choice h) td x θ

include hT hprimary in
theorem joinedSource_highPressure_smooth (p : ℕ) (hp : 2 ≤ p) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ =>
      (joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure (t,y)) := by
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSource_highForcing P M D hT τ hτ hτT B primary hprimary p hp⟩
  unfold joinedSourceProfiles
  rw [profiles_step _ _ p hp]
  change ContDiff ℝ ∞ (fun y : Space × ℝ =>
    (EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))).2 (t,y))
  rw [EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B h]
  exact EulerTransversePacketJoin.scalar_smooth τ hτ hτT B (Classical.choice h) t

include hT hprimary in
theorem joinedSource_meanPressure_smooth (p : ℕ) (hp : 2 ≤ p) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ =>
      (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure (t,y)) := by
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSource_meanForcing P M D hT τ hτ hτT B primary hprimary p hp⟩
  unfold joinedSourceProfiles
  rw [profiles_step _ _ p hp]
  change ContDiff ℝ ∞ (fun y : Space × ℝ => (EulerMeanPacketProvider.meanSolve M
    (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
      (joinedSourceProfiles P M D τ hτ hτT B primary))).2 (t,y))
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).scalar_spatial_smooth t

include hT hprimary in
theorem joinedSource_meanPressure_angle (p : ℕ) (hp : 2 ≤ p) (t : ℝ) (x : Space) (θ : ℝ) :
    (pressureJet (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure (t,(x,θ))).2
      angleDirection = 0 := by
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSource_meanForcing P M D hT τ hτ hτT B primary hprimary p hp⟩
  unfold joinedSourceProfiles
  rw [profiles_step _ _ p hp]
  change (pressureJet (EulerMeanPacketProvider.meanSolve M
    (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
      (joinedSourceProfiles P M D τ hτ hτT B primary))).2 (t,(x,θ))).2 angleDirection = 0
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).scalar_angle_jet t x θ

end EulerPacketCylinderField
