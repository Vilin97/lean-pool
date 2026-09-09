/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceEquations
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceRegularity

@[expose] public section

/-! Classical spatial slices and true within-time derivatives of the joined recursive family. -/

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

include hT hprimary in
theorem joinedSource_high_slice (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    SliceDifferentiable (Icc (0 : ℝ) M.T)
      (joinedSourceProfiles P M D τ hτ hτT B primary p).high (t,(x,θ)) := by
  let W := joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p
  exact W.high.sliceDifferentiable W.highDerivative M.T_pos.le W.high_time t x θ

include hT hprimary in
theorem joinedSource_mean_slice (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    SliceDifferentiable (Icc (0 : ℝ) M.T)
      (joinedSourceProfiles P M D τ hτ hτT B primary p).mean (t,(x,θ)) := by
  let W := joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p
  exact W.mean.sliceDifferentiable W.meanDerivative M.T_pos.le W.mean_time t x θ

include hT hprimary in
theorem joinedSource_corrector_slice (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    SliceDifferentiable (Icc (0 : ℝ) M.T)
      (joinedSourceProfiles P M D τ hτ hτT B primary p).corrector (t,(x,θ)) := by
  let W := joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p
  exact W.corrector.sliceDifferentiable W.correctorDerivative M.T_pos.le W.corrector_time t x θ

include hT hprimary in
theorem joinedSource_highPressure_smooth_all
    (hπ : ∀ t : Icc (0 : ℝ) M.T, ContDiff ℝ ∞ (fun y : Space × ℝ => primary.highPressure (t,y)))
    (p : ℕ) (t : Icc (0 : ℝ) M.T) :
    ContDiff ℝ ∞ (fun y : Space × ℝ =>
      (joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure (t,y)) := by
  by_cases hp0 : p = 0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    change ContDiff ℝ ∞ (fun _ : Space × ℝ => (0 : ℝ))
    exact contDiff_const
  by_cases hp1 : p = 1
  · subst p
    simpa only [joinedSourceProfiles,profiles_one] using hπ t
  exact joinedSource_highPressure_smooth P M D hT τ hτ hτT B primary hprimary p (by omega) t

include hT hprimary in
theorem joinedSource_meanPressure_smooth_all (hm : primary.meanPressure = 0)
    (p : ℕ) (t : Icc (0 : ℝ) M.T) :
    ContDiff ℝ ∞ (fun y : Space × ℝ =>
      (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure (t,y)) := by
  by_cases hp0 : p = 0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    change ContDiff ℝ ∞ (fun _ : Space × ℝ => (0 : ℝ))
    exact contDiff_const
  by_cases hp1 : p = 1
  · subst p
    simp only [joinedSourceProfiles,profiles_one,hm,Pi.zero_apply]
    exact contDiff_const
  exact joinedSource_meanPressure_smooth P M D hT τ hτ hτT B primary hprimary p (by omega) t

include hT hprimary in
theorem joinedSource_meanPressure_angle_all (hm : primary.meanPressure = 0)
    (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    (pressureJet (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure (t,(x,θ))).2
      angleDirection = 0 := by
  by_cases hp0 : p = 0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    change (pressureJet (0 : ScalarField) (t,(x,θ))).2 angleDirection = 0
    rw [pressureJet_zero]
    rfl
  by_cases hp1 : p = 1
  · subst p
    simp only [joinedSourceProfiles,profiles_one,hm]
    rw [pressureJet_zero]
    rfl
  exact joinedSource_meanPressure_angle P M D hT τ hτ hτT B primary hprimary p (by omega) t x θ

end EulerPacketCylinderField
