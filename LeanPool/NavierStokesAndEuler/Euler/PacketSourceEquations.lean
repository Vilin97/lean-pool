/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketJets
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJets

/-! Actual defining equations of the generated mean and high profiles. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- The two source inverses use the same prescribed inverse deformation and strain. -/
structure SourceCoefficientAgreement (M : EulerMeanPacketProvider.Data)
    (D : EulerTransversePacketProvider.Data U) : Prop where
  inverse : ∀ (t : Icc (0 : ℝ) M.T) x, M.FInv t x = D.FInv.field (D.clamp t) x
  strain : ∀ (t : Icc (0 : ℝ) M.T) x, M.M.field t x = D.M.field (D.clamp t) x

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

theorem sourceInverse_eq_mean (A : SourceCoefficientAgreement M D)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    (sourceOperators P M D I).inverseFrame (t,(x,θ)) = M.inverseFrame (t,(x,θ)) := by
  change D.FInv.field (D.clamp t) x = M.FInv (M.clamp t) x
  rw [EulerMeanPacketProvider.Data.clamp_coe]
  exact (A.inverse t x).symm

theorem sourceStrain_eq_mean (A : SourceCoefficientAgreement M D)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    (sourceOperators P M D I).strain (t,(x,θ)) = M.strain (t,(x,θ)) := by
  change D.M.field (D.clamp t) x = M.M.field (M.clamp t) x
  rw [EulerMeanPacketProvider.Data.clamp_coe]
  exact (A.strain t x).symm

include hT in
theorem source_mean_equation (A : SourceCoefficientAgreement M D) (p : ℕ) (hp : 2 ≤ p)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    linearPart ((sourceOperators P M D I).strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) M.T) (sourceProfiles P M D I Iprimary p).mean (t,(x,θ))) +
      slowPressure ((sourceOperators P M D I).inverseFrame (t,(x,θ)))
        (pressureJet (sourceProfiles P M D I Iprimary p).meanPressure (t,(x,θ))) =
      meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary) (t,(x,θ)) := by
  rw [sourceStrain_eq_mean P M D I A t x θ,sourceInverse_eq_mean P M D I A t x θ]
  have he : sourceProfiles P M D I Iprimary p =
      EulerPacketProfileRecursion.step (sourceOperators P M D I) p (sourceProfiles P M D I
          Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  exact EulerMeanPacketProvider.meanSolve_jet_equation M _
    ⟨sourceMeanForcing P M D hT I Iprimary p hp⟩ t x θ

include hT in
theorem source_high_equation (p : ℕ) (hp : 2 ≤ p)
    (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    linearPart ((sourceOperators P M D I).strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) M.T) (sourceProfiles P M D I Iprimary p).high (t,(x,θ))) +
      fastPressure ((sourceOperators P M D I).normal (t,(x,θ)))
        (pressureJet (sourceProfiles P M D I Iprimary p).highPressure (t,(x,θ))) =
      highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary) (t,(x,θ)) := by
  have he : sourceProfiles P M D I Iprimary p =
      EulerPacketProfileRecursion.step (sourceOperators P M D I) p (sourceProfiles P M D I
          Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
  have h := EulerTransversePacketProvider.highSolve_jet_equation D I _
    ⟨sourceHighForcing P M D hT I Iprimary p hp⟩ td x θ
  change linearPart (D.strain (t,(x,θ)))
      (slicedJet (Icc (0 : ℝ) M.T)
        (EulerTransversePacketProvider.highSolve P D I
          (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).1 (t,(x,θ))) +
      fastPressure (D.normalField (t,(x,θ)))
        (pressureJet (EulerTransversePacketProvider.highSolve P D I
          (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).2 (t,(x,θ))) =
              _
  have hs : Icc (0 : ℝ) M.T = Icc (0 : ℝ) D.T := congrArg (Icc (0 : ℝ)) hT
  have hj := congrArg (fun s : Set ℝ => slicedJet s
    (EulerTransversePacketProvider.highSolve P D I
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).1 (t,(x,θ))) hs
  rw [hj]
  exact h

include hT in
theorem source_primary_equation (t : Icc (0 : ℝ) M.T) (x : Space) (θ : ℝ) :
    linearPart ((sourceOperators P M D I).strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) M.T) ((homogeneousForcing (P := P) D).vector Iprimary) (t,(x,θ))) +
      fastPressure ((sourceOperators P M D I).normal (t,(x,θ)))
        (pressureJet ((homogeneousForcing (P := P) D).scalar Iprimary) (t,(x,θ))) = 0 := by
  let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
  have h := (homogeneousForcing (P := P) D).jet_equation Iprimary td x θ
  change linearPart (D.strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) M.T) ((homogeneousForcing (P := P) D).vector Iprimary) (t,(x,θ))) +
      fastPressure (D.normalField (t,(x,θ)))
        (pressureJet ((homogeneousForcing (P := P) D).scalar Iprimary) (t,(x,θ))) = 0
  have hs : Icc (0 : ℝ) M.T = Icc (0 : ℝ) D.T := congrArg (Icc (0 : ℝ)) hT
  have hj := congrArg (fun s : Set ℝ => slicedJet s
    ((homogeneousForcing (P := P) D).vector Iprimary) (t,(x,θ))) hs
  rw [hj]
  exact h

end EulerPacketCylinderField
