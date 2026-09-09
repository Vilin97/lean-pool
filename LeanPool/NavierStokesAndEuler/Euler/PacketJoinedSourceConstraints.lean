/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceEquations
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketContract
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderMeanSolenoidal
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceEquations
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport

/-! Genuine mean and high constraints for the joined recursively constructed family. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerVectorCalculus

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

theorem joinedSource_corrector_eq
    (hc : primary.corrector = D.curlCorrector P primary.high)
    (p : ℕ) (hp : 1 ≤ p) :
    (joinedSourceProfiles P M D τ hτ hτT B primary p).corrector =
      D.curlCorrector P (joinedSourceProfiles P M D τ hτ hτT B primary p).high := by
  by_cases hp1 : p = 1
  · subst p
    simpa only [joinedSourceProfiles,profiles_one] using hc
  exact profiles_corrector (joinedSourceOperators P M D τ hτ hτT B) primary p (by omega)

include hT hprimary in
theorem joinedSource_high_mean_zero
    (hm : ∀ (t : Icc (0 : ℝ) M.T) x, (∫ θ in (0 : ℝ)..P, primary.high (t, (x, θ))) = 0)
    (p : ℕ) (hp : 1 ≤ p) (t : Icc (0 : ℝ) M.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, (joinedSourceProfiles P M D τ hτ hτT B primary p).high (t,(x,θ))) = 0 := by
  by_cases hp1 : p = 1
  · subst p
    simpa only [joinedSourceProfiles,profiles_one] using hm t x
  have hp2 : 2 ≤ p := by omega
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSourceHighForcing P M D hT τ hτ hτT B primary hprimary p hp2⟩
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      EulerPacketProfileRecursion.step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp2
  rw [he]
  change (∫ θ in (0 : ℝ)..P,
    (EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B _).1 (t,(x,θ))) = 0
  rw [EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B h]
  exact EulerTransversePacketJoin.vector_mean_zero τ hτ hτT B (Classical.choice h) t x

include hT hprimary in
theorem joinedSource_high_tangent_all
    (ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)
    (p : ℕ) (hp : 1 ≤ p) (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    inner ℝ (D.normalField (t,(x,θ)))
      ((joinedSourceProfiles P M D τ hτ hτT B primary p).high (t,(x,θ))) = 0 := by
  by_cases hp1 : p = 1
  · subst p
    simpa only [joinedSourceProfiles,profiles_one] using ht t x θ
  exact joinedSource_high_tangent P M D hT τ hτ hτT B primary hprimary p (by omega) t x θ

/-- Joined mean pullback field as an element of `Field P M.T (fun z => (joinedSourceOperators P
M D τ hτ hτT B).inverseFrame z ((joinedSourceProfiles P M D τ hτ hτT B primary p).mean z))`. -/
def joinedMeanPullbackField (p : ℕ) :
    Field P M.T (fun z => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame z
      ((joinedSourceProfiles P M D τ hτ hτT B primary p).mean z)) :=
  (joinedSourceCoefficientData P M D τ hτ hτT B hT).inverse.multiply
    (joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p).mean

include hT hprimary in
theorem joinedMeanPullback_divergence (hmean : primary.mean = 0)
    (A : SourceCoefficientAgreement M D) (p : ℕ) (t : Icc (0 : ℝ) M.T) (x : Space) :
    divergence (fun y : Space => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(y,0))
      ((joinedSourceProfiles P M D τ hτ hτT B primary p).mean (t,(y,0)))) x = 0 := by
  by_cases hp0 : p = 0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    change divergence (fun y : Space => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame
        (t,(y,0)) 0) x = 0
    simp [divergence]
  by_cases hp1 : p = 1
  · subst p
    simp only [joinedSourceProfiles,profiles_one,hmean,Pi.zero_apply]
    simp [divergence]
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSourceMeanForcing P M D hT τ hτ hτT B primary hprimary p hp⟩
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      EulerPacketProfileRecursion.step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp
  have hf : (fun y : Space => (joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(y,0))
      ((joinedSourceProfiles P M D τ hτ hτT B primary p).mean (t,(y,0)))) =
      fun y => M.inverseFrame (t,(y,0))
        ((EulerMeanPacketProvider.meanSolve M (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
          (joinedSourceProfiles P M D τ hτ hτT B primary))).1 (t,(y,0))) := by
    funext y
    rw [joinedInverse_eq_mean P M D τ hτ hτT B A t y 0,he]
    rfl
  rw [hf]
  exact EulerMeanPacketProvider.meanSolve_divergence M _ h t x 0

theorem joinedMeanPullbackField_mem (hmean : primary.mean = 0)
    (A : SourceCoefficientAgreement M D) (κ : ℝ) (m : Space)
    (p : ℕ) (t : Icc (0 : ℝ) M.T) :
    (joinedMeanPullbackField P M D hT τ hτ hτT B primary hprimary p).path t ∈
      divergenceFreeSpace P κ m := by
  apply Field.mem_divergenceFree_of_angleIndependent _ κ m t
  · intro x θ
    change D.FInv.field (D.clamp t) x ((joinedSourceProfiles P M D τ hτ hτT B primary p).mean
        (t,(x,θ))) =
      D.FInv.field (D.clamp t) x ((joinedSourceProfiles P M D τ hτ hτT B primary p).mean (t,(x,0)))
    rw [(joinedSourceProfileWitness P M D hT τ hτ hτT B primary hprimary p).mean_angle t x θ]
  · exact joinedMeanPullback_divergence P M D hT τ hτ hτT B primary hprimary hmean A p t

end EulerPacketCylinderField
