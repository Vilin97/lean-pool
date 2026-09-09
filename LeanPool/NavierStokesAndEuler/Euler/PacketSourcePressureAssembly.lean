/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradient

@[expose] public section

/-! The actual direct-forward source packet has a lifted pressure gradient.
Every component is constructed from its mean or oscillatory inverse. -/

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerPacketPressure

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : EulerPacketProfileRecursion.VectorField}
  (G : Forcing P D raw) (I : InitialData P D)

def pressureGradientWitness (κ : ℝ) (m : Space) :
    GradientWitness P D.T κ m (G.scalar I) :=
  GradientWitness.compact (G.scalar I) (G.pressurePath I) (G.pressurePath_orbit I)
    (G.scalar_eq_pointField I) D.support D.support_compact
    (fun t => G.scalar_zero_outside I t)

end EulerTransversePacketProvider.Forcing

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerPacketPressure
  EulerTransversePacketProvider

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (I Iprimary : InitialData P D)
  (κ : ℝ) (m : Space)

def source_highPressureWitness_step (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m (sourceProfiles P M D I Iprimary p).highPressure := by
  let h : Nonempty (Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨source_highForcing P M D hTime I Iprimary p hp⟩
  have he : sourceProfiles P M D I Iprimary p =
      step (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerTransversePacketProvider.highSolve P D I _).2
  rw [EulerTransversePacketProvider.highSolve_of_admissible D I _ h]
  exact ((Classical.choice h).pressureGradientWitness I κ m).changeTime hTime.symm

def source_meanPressureWitness_step (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m (sourceProfiles P M D I Iprimary p).meanPressure := by
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨source_meanForcing P M D hTime I Iprimary p hp⟩
  have he : sourceProfiles P M D I Iprimary p =
      step (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerMeanPacketProvider.meanSolve M _).2
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).pressureGradientWitness P κ m

def source_highPressureWitness (p : ℕ) :
    GradientWitness P M.T κ m (sourceProfiles P M D I Iprimary p).highPressure := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    exact GradientWitness.zero P M.T κ m
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    exact ((homogeneousForcing (P := P) D).pressureGradientWitness Iprimary κ m).changeTime
      hTime.symm
  exact source_highPressureWitness_step P M D hTime I Iprimary κ m p (by omega)

def source_meanPressureWitness (p : ℕ) :
    GradientWitness P M.T κ m (sourceProfiles P M D I Iprimary p).meanPressure := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    exact GradientWitness.zero P M.T κ m
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    exact GradientWitness.zero P M.T κ m
  exact source_meanPressureWitness_step P M D hTime I Iprimary κ m p (by omega)

def sourcePressureWitness (N : ℕ) (r : ℝ) :
    GradientWitness P M.T κ m (fieldSum (N+1) r
      (assembledPressure N (sourceProfiles P M D I Iprimary))) :=
  GradientWitness.evaluateFamily (N+1) r _ (GradientWitness.assembleFamily N _ _
    (fun i _ => source_meanPressureWitness P M D hTime I Iprimary κ m i)
    (fun i _ => source_highPressureWitness P M D hTime I Iprimary κ m i))

end EulerPacketCylinderField
