/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileFields
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftEquation
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport

/-! The literal initialized packet supplies the all-order approximation
residual identity, including its actual pressure gradient.  Its velocity,
time derivative and residual are the fields already constructed from the
source profiles, not additional approximation hypotheses. -/

section

/-! The literal initialized finite packet has a genuine pressure-gradient
Field in the closed lifted gradient space.  Both the mean and oscillatory
pieces come from the actual source inverses. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketPressure

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

/-- Pressure gradient witness, constructed using `GradientWitness.compact`. -/
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

/-- Pressure gradient witness, constructed using `GradientWitness.compact`. -/
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

/-- Joined source high pressure witness step as an element of `GradientWitness P M.T κ m
(joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure`. -/
def joinedSourceHighPressureWitnessStep (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m
      (joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure := by
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSourceHighForcing P M D hTime τ hτ hτT B primary hprimary p hp⟩
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerTransversePacketJoin.highSolve
    (P := P) τ hτ hτT B _).2
  rw [EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B h]
  exact (EulerTransversePacketJoin.pressureGradientWitness τ hτ hτT B
    (Classical.choice h) κ m).changeTime hTime.symm

/-- Joined source mean pressure witness step as an element of `GradientWitness P M.T κ m
(joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure`. -/
def joinedSourceMeanPressureWitnessStep (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m
      (joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure := by
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSourceMeanForcing P M D hTime τ hτ hτT B primary hprimary p hp⟩
  have he : joinedSourceProfiles P M D τ hτ hτT B primary p =
      step (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary) := profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerMeanPacketProvider.meanSolve M _).2
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).pressureGradientWitness P κ m

/-- Joined source high pressure witness as an element of `GradientWitness P M.T κ m
(joinedSourceProfiles P M D τ hτ hτT B primary p).highPressure`. -/
def joinedSourceHighPressureWitness
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
  exact joinedSourceHighPressureWitnessStep P M D hTime τ hτ hτT B
    primary hprimary κ m p (by omega)

/-- Joined source mean pressure witness as an element of `GradientWitness P M.T κ m
(joinedSourceProfiles P M D τ hτ hτT B primary p).meanPressure`. -/
def joinedSourceMeanPressureWitness
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
  exact joinedSourceMeanPressureWitnessStep P M D hTime τ hτ hτT B
    primary hprimary κ m p (by omega)

/-- Joined pressure witness, constructed using `GradientWitness.evaluateFamily`. -/
def joinedPressureWitness
    (hq : GradientWitness P M.T κ m primary.meanPressure)
    (hπ : GradientWitness P M.T κ m primary.highPressure) (N : ℕ) (r : ℝ) :
    GradientWitness P M.T κ m (fieldSum (N+1) r (assembledPressure N
      (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
  GradientWitness.evaluateFamily (N+1) r _ (GradientWitness.assembleFamily N _ _
    (fun i _ => joinedSourceMeanPressureWitness P M D hTime τ hτ hτT B
      primary hprimary κ m hq i)
    (fun i _ => joinedSourceHighPressureWitness P M D hTime τ hτ hτT B
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

/-- Initialized pressure, given by `fieldSum (N+1) κ (assembledPressure N (initializedProfiles M
D τ hτ hτT B δ hδ ξ hs α))`. -/
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.Field

open EulerPacketProfileRecursion

theorem toFieldTower_eq_of_path_eq {P T : ℝ} [Fact (0 < P)]
    {raw raw' : VectorField} (G : Field P T raw) (H : Field P T raw')
    (h : G.path = H.path) : G.toFieldTower = H.toFieldTower := by
  cases G
  cases H
  dsimp only at h
  cases h
  rfl

end EulerPacketCylinderField.Field

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketPressure EulerPacketCoordinates EulerLiftedGradientSpace
  EulerPacketCorrectionCoefficients EulerAllOrderDriftCorrection

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Initialized velocity, given by `fieldSum (N+1) κ (assembledVelocity N (initializedProfiles M
D τ hτ hτT B δ hδ ξ hs α))`. -/
def initializedVelocity (N : ℕ) (κ : ℝ) : VectorField :=
  fieldSum (N+1) κ (assembledVelocity N (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α))

/-- Initialized velocity field as an element of `Field period D.T (initializedVelocity M D τ hτ
hτT B δ hδ ξ hs α N κ)`. -/
def initializedVelocityField (N : ℕ) (κ : ℝ) :
    Field period D.T (initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N κ) :=
  (ProfileRegularity.velocityField M.T_pos
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
        κ).changeTime hTime

/-- Initialized velocity derivative, constructed using `fieldSum`. -/
def initializedVelocityDerivative (N : ℕ) (κ : ℝ) : VectorField :=
  fieldSum (N+1) κ (ProfileRegularity.velocityTimeCoefficients (T := M.T) (N := N)
    (a := initializedProfiles M D τ hτ hτT B δ hδ ξ hs α))

/-- Initialized velocity derivative field as an element of `Field period D.T
(initializedVelocityDerivative M D τ hτ hτT B δ hδ ξ hs α N κ)`. -/
def initializedVelocityDerivativeField (N : ℕ) (κ : ℝ) :
    Field period D.T (initializedVelocityDerivative M D τ hτ hτT B δ hδ ξ hs α N κ) :=
  (ProfileRegularity.velocityDerivativeField M.T_pos
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
        κ).changeTime hTime

theorem initializedVelocityField_time (N : ℕ) (κ : ℝ) :
    TimeDerivative D.T_pos.le
      (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N κ)
      (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N κ) :=
  Field.changeTime_derivative _ _ hTime M.T_pos.le D.T_pos.le
    (ProfileRegularity.velocityField_time M.T_pos
      (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i) κ)

/-- The pairwise curl construction and the literal velocity sum represent
the same normalized coordinate field. -/
theorem initializedNormalizedField_path_eq (N : ℕ) (k : ℝ) :
    (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).path =
      (coordinateField D (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹) k).path
          :=
  Field.path_eq_of_raw_eq _ _ (fun _ _ _ => rfl)

theorem initializedNormalizedField_tower_eq (N : ℕ) (k : ℝ) :
    (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).toFieldTower =
      (coordinateField D (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
          k).toFieldTower :=
  Field.toFieldTower_eq_of_path_eq _ _
    (initializedNormalizedField_path_eq M D hTime τ hτ hτT B δ hδ ξ hs α N k)

/-- Initialized coordinate residual field used in packet initialized residual equation. -/
def initializedCoordinateResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    Field period D.T (normalizedResidual D k
      (initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)
      (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)) :=
  (initializedNormalizedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk).congr
    (fun t x θ => by
      change k • rawInverse D (t,(x,θ))
          (slicedMomentumResidual (Icc (0 : ℝ) D.T) k⁻¹
            (rawInverse D (t,(x,θ))) (D.strain (t,(x,θ))) (D.normalField (t,(x,θ)))
            (initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)
            (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹) (t,(x,θ))) =
        k • rawInverse D (t,(x,θ))
          (slicedMomentumResidual (Icc (0 : ℝ) M.T) k⁻¹
            (rawInverse D (t,(x,θ))) (D.strain (t,(x,θ))) (D.normalField (t,(x,θ)))
            (initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)
            (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹) (t,(x,θ)))
      rw [hTime])

/-- This is the exact initialized correction data used by the quantitative
budget, after identifying the two genuine realizations of its fields. -/
theorem initializedCorrectionData_eq_coordinate (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) (hκ : |k⁻¹| ≤ 1) :
    initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk =
      coordinateData D k hκ
        (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
        (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)
        (initializedCoordinateResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk) := by
  unfold initializedCorrectionData coordinateData correctionDataOfFields
  rw [initializedNormalizedField_tower_eq M D hTime τ hτ hτT B δ hδ ξ hs α N k]
  rfl

/-- The actual finite pressure and every-order residual identity, with no
assumed pressure field, approximation derivative or residual cancellation. -/
def initializedApproximationResidual (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ApproximationResidual period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk) := by
  have hk0 : k ≠ 0 := by linarith
  have hκ : |k⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (by linarith : 0 < k))]
    exact inv_le_one_of_one_le₀ (by linarith)
  let Pa := initializedCoordinatePressureField M D hTime τ hτ hτT B δ hδ ξ hs α N k hk0
  refine { pressure := Pa.toFieldTower, gradient := ?_, equation := ?_ }
  · intro t
    exact initializedCoordinatePressureField_mem M D hTime τ hτ hτT B δ hδ ξ hs α N k hk0 t
  · intro q hq t ht
    rw [initializedCorrectionData_eq_coordinate M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk
        hκ]
    exact approximation_hasDerivAt D k hk0 hκ
      (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
      (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
      (initializedVelocityField_time M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
      (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)
      (initializedCoordinateResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk)
      Pa q hq t ht

end EulerPacketTerminalDatum
