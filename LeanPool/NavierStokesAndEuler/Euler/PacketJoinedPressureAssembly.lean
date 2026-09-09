/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceResidual
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport

@[expose] public section

/-! The literal initialized finite packet has a genuine pressure-gradient
Field in the closed lifted gradient space.  Both the mean and oscillatory
pieces come from the actual source inverses. -/

noncomputable section

namespace EulerTransversePacketPrimary

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketPressure

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

def pressureGradientWitness (κ : ℝ) (m : Space) :
    GradientWitness P D.T κ m (scalar τ hτ hτT B Y) :=
  GradientWitness.compact (scalar τ hτ hτT B Y)
    (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y)
    (scalar_eq_pointField τ hτ hτT B Y) D.support D.support_compact
    (fun t => scalar_zero_outside τ hτ hτT B Y t)

end EulerTransversePacketPrimary

namespace EulerTransversePacketJoin

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketPressure
  EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

def pressureGradientWitness (κ : ℝ) (m : Space) :
    GradientWitness P D.T κ m (scalar τ hτ hτT B G) :=
  GradientWitness.compact (scalar τ hτ hτT B G)
    (pressurePath τ hτ hτT B G) (pressurePath_orbit τ hτ hτT B G)
    (scalar_eq_pointField τ hτ hτT B G) D.support D.support_compact
    (scalar_zero_outside τ hτ hτT B G)

end EulerTransversePacketJoin

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerPacketPressure

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (κ : ℝ) (m : Space)

def joinedSource_highPressureWitness_step (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m
      (joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure := by
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSource_highForcing P M D hTime τ hτ hτT B primary hprimary p hp⟩
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerTransversePacketJoin.highSolve
    (P := P) τ hτ hτT B _).2
  rw [EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B h]
  exact (EulerTransversePacketJoin.pressureGradientWitness τ hτ hτT B
    (Classical.choice h) κ m).changeTime hTime.symm

def joinedSource_meanPressureWitness_step (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m
      (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure := by
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSource_meanForcing P M D hTime τ hτ hτT B primary hprimary p hp⟩
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerMeanPacketProvider.meanSolve M _).2
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).pressureGradientWitness P κ m

def joinedSource_highPressureWitness
    (hπ : GradientWitness P M.T κ m primary.highPressure) (p : ℕ) :
    GradientWitness P M.T κ m
      (joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure := by
  by_cases hp0 : p = 0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    exact GradientWitness.zero P M.T κ m
  by_cases hp1 : p = 1
  · subst p
    simpa only [joinedSourceProfiles,profiles_one] using hπ
  exact joinedSource_highPressureWitness_step P M D hTime τ hτ hτT B
    primary hprimary κ m p (by omega)

def joinedSource_meanPressureWitness
    (hq : GradientWitness P M.T κ m primary.meanPressure) (p : ℕ) :
    GradientWitness P M.T κ m
      (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure := by
  by_cases hp0 : p = 0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    exact GradientWitness.zero P M.T κ m
  by_cases hp1 : p = 1
  · subst p
    simpa only [joinedSourceProfiles,profiles_one] using hq
  exact joinedSource_meanPressureWitness_step P M D hTime τ hτ hτT B
    primary hprimary κ m p (by omega)

def joinedPressureWitness
    (hq : GradientWitness P M.T κ m primary.meanPressure)
    (hπ : GradientWitness P M.T κ m primary.highPressure) (N : ℕ) (r : ℝ) :
    GradientWitness P M.T κ m (fieldSum (N+1) r (assembledPressure N
      (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
  GradientWitness.evaluateFamily (N+1) r _ (GradientWitness.assembleFamily N _ _
    (fun i _ => joinedSource_meanPressureWitness P M D hTime τ hτ hτT B
      primary hprimary κ m hq i)
    (fun i _ => joinedSource_highPressureWitness P M D hTime τ hτ hτT B
      primary hprimary κ m hπ i))

end EulerPacketCylinderField

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketPressure EulerPacketCoordinates EulerLiftedGradientSpace

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def initializedPressure (N : ℕ) (κ : ℝ) : ScalarField :=
  fieldSum (N+1) κ (assembledPressure N (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α))

/-- Every pressure component is supplied by its actual inverse, including the
literal compact terminal primary at grade one. -/
def initializedPressureWitness (N : ℕ) (κ : ℝ) :
    GradientWitness period M.T κ D.m₀ (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N κ) :=
  joinedPressureWitness period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    κ D.m₀ (GradientWitness.zero period M.T κ D.m₀)
    ((EulerTransversePacketPrimary.pressureGradientWitness τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) κ D.m₀).changeTime hTime.symm) N κ

/-- The actual pressure-gradient input Pa for the normalized coordinate
equation. The factor k² is the same as in the literal residual identity. -/
def initializedCoordinatePressureField (N : ℕ) (k : ℝ) (hk : k ≠ 0) :
    Field period D.T (coordinatePressure D k
      (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)) :=
  pressureField D k hk
    ((initializedPressureWitness M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).changeTime hTime)

theorem initializedCoordinatePressureField_mem (N : ℕ) (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) :
    (initializedCoordinatePressureField M D hTime τ hτ hτT B δ hδ ξ hs α N k hk).path t ∈
      gradientSpace period k⁻¹ D.m₀ :=
  pressureField_mem D k hk _ t

end EulerPacketTerminalDatum
