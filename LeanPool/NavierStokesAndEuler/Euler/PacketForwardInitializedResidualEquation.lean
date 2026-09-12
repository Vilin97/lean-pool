/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileFields
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftEquation
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles

/-! The literal zero-history initialized packet supplies the all-order approximation
residual identity, including its actual pressure gradient.  Its velocity,
time derivative and residual are the fields already constructed from the
source profiles, not additional approximation hypotheses. -/

section

/-! The actual direct-forward source packet has a lifted pressure gradient.
Every component is constructed from its mean or oscillatory inverse. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerPacketPressure

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : EulerPacketProfileRecursion.VectorField}
  (G : Forcing P D raw) (I : InitialData P D)

/-- Pressure gradient witness, constructed using `GradientWitness.compact`. -/
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

/-- Source high pressure witness step as an element of `GradientWitness P M.T κ m
(sourceProfiles P M D I Iprimary p).highPressure`. -/
def sourceHighPressureWitnessStep (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m (sourceProfiles P M D I Iprimary p).highPressure := by
  let h : Nonempty (Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨sourceHighForcing P M D hTime I Iprimary p hp⟩
  have he : sourceProfiles P M D I Iprimary p =
      step (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerTransversePacketProvider.highSolve P D I _).2
  rw [EulerTransversePacketProvider.highSolve_of_admissible D I _ h]
  exact ((Classical.choice h).pressureGradientWitness I κ m).changeTime hTime.symm

/-- Source mean pressure witness step as an element of `GradientWitness P M.T κ m
(sourceProfiles P M D I Iprimary p).meanPressure`. -/
def sourceMeanPressureWitnessStep (p : ℕ) (hp : 2 ≤ p) :
    GradientWitness P M.T κ m (sourceProfiles P M D I Iprimary p).meanPressure := by
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨sourceMeanForcing P M D hTime I Iprimary p hp⟩
  have he : sourceProfiles P M D I Iprimary p =
      step (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  change GradientWitness P M.T κ m (EulerMeanPacketProvider.meanSolve M _).2
  rw [EulerMeanPacketProvider.meanSolve_of_admissible M _ h]
  exact (Classical.choice h).pressureGradientWitness P κ m

/-- Source high pressure witness as an element of `GradientWitness P M.T κ m (sourceProfiles P M
D I Iprimary p).highPressure`. -/
def sourceHighPressureWitness (p : ℕ) :
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
  exact sourceHighPressureWitnessStep P M D hTime I Iprimary κ m p (by omega)

/-- Source mean pressure witness as an element of `GradientWitness P M.T κ m (sourceProfiles P M
D I Iprimary p).meanPressure`. -/
def sourceMeanPressureWitness (p : ℕ) :
    GradientWitness P M.T κ m (sourceProfiles P M D I Iprimary p).meanPressure := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    exact GradientWitness.zero P M.T κ m
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    exact GradientWitness.zero P M.T κ m
  exact sourceMeanPressureWitnessStep P M D hTime I Iprimary κ m p (by omega)

/-- Source pressure witness, constructed using `GradientWitness.evaluateFamily`. -/
def sourcePressureWitness (N : ℕ) (r : ℝ) :
    GradientWitness P M.T κ m (fieldSum (N+1) r
      (assembledPressure N (sourceProfiles P M D I Iprimary))) :=
  GradientWitness.evaluateFamily (N+1) r _ (GradientWitness.assembleFamily N _ _
    (fun i _ => sourceMeanPressureWitness P M D hTime I Iprimary κ m i)
    (fun i _ => sourceHighPressureWitness P M D hTime I Iprimary κ m i))

end EulerPacketCylinderField

end
end

end

section

/-! The finite zero-history pressure and its actual lifted gradient. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketPressure EulerPacketCoordinates EulerLiftedGradientSpace

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Forward initialized pressure, given by `fieldSum (N+1) κ (assembledPressure N
(forwardInitializedProfiles M D δ hδ ξ hs α))`. -/
def forwardInitializedPressure (N : ℕ) (κ : ℝ) : ScalarField :=
  fieldSum (N+1) κ (assembledPressure N (forwardInitializedProfiles M D δ hδ ξ hs α))

/-- Forward initialized pressure witness, given by `sourcePressureWitness period M D hTime
(InitialData.zero period D) (initialData D δ hδ (α • ξ) hs) κ D.m₀ N κ`. -/
def forwardInitializedPressureWitness (N : ℕ) (κ : ℝ) :
    GradientWitness period M.T κ D.m₀ (forwardInitializedPressure M D δ hδ ξ hs α N κ) :=
  sourcePressureWitness period M D hTime (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) κ D.m₀ N κ

/-- Forward initialized coordinate pressure field, given by `pressureField D k hk
((forwardInitializedPressureWitness M D hTime δ hδ ξ hs α N k⁻¹).changeTime hTime)`. -/
def forwardInitializedCoordinatePressureField (N : ℕ) (k : ℝ) (hk : k ≠ 0) :
    Field period D.T (coordinatePressure D k
      (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)) :=
  pressureField D k hk
    ((forwardInitializedPressureWitness M D hTime δ hδ ξ hs α N k⁻¹).changeTime hTime)

theorem forwardInitializedCoordinatePressureField_mem (N : ℕ) (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) :
    (forwardInitializedCoordinatePressureField M D hTime δ hδ ξ hs α N k hk).path t ∈
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

theorem toFieldTower_eq_of_path_eq_forward {P T : ℝ} [Fact (0 < P)]
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
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Forward initialized velocity, given by `fieldSum (N+1) κ (assembledVelocity N
(forwardInitializedProfiles M D δ hδ ξ hs α))`. -/
def forwardInitializedVelocity (N : ℕ) (κ : ℝ) : VectorField :=
  fieldSum (N+1) κ (assembledVelocity N (forwardInitializedProfiles M D δ hδ ξ hs α))

/-- Forward initialized velocity field as an element of `Field period D.T
(forwardInitializedVelocity M D δ hδ ξ hs α N κ)`. -/
def forwardInitializedVelocityField (N : ℕ) (κ : ℝ) :
    Field period D.T (forwardInitializedVelocity M D δ hδ ξ hs α N κ) :=
  (ProfileRegularity.velocityField M.T_pos
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i) κ).changeTime
        hTime

/-- Forward initialized velocity derivative, constructed using `fieldSum`. -/
def forwardInitializedVelocityDerivative (N : ℕ) (κ : ℝ) : VectorField :=
  fieldSum (N+1) κ (ProfileRegularity.velocityTimeCoefficients (T := M.T) (N := N)
    (a := forwardInitializedProfiles M D δ hδ ξ hs α))

/-- Forward initialized velocity derivative field as an element of `Field period D.T
(forwardInitializedVelocityDerivative M D δ hδ ξ hs α N κ)`. -/
def forwardInitializedVelocityDerivativeField (N : ℕ) (κ : ℝ) :
    Field period D.T (forwardInitializedVelocityDerivative M D δ hδ ξ hs α N κ) :=
  (ProfileRegularity.velocityDerivativeField M.T_pos
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i) κ).changeTime
        hTime

theorem forwardInitializedVelocityField_time (N : ℕ) (κ : ℝ) :
    TimeDerivative D.T_pos.le
      (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N κ)
      (forwardInitializedVelocityDerivativeField M D hTime δ hδ ξ hs α N κ) :=
  Field.changeTime_derivative _ _ hTime M.T_pos.le D.T_pos.le
    (ProfileRegularity.velocityField_time M.T_pos
      (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i) κ)

/-- The pairwise curl construction and the literal velocity sum represent
the same normalized coordinate field. -/
theorem forwardInitializedNormalizedField_path_eq (N : ℕ) (k : ℝ) :
    (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α N k).path =
      (coordinateField D (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹) k).path :=
  Field.path_eq_of_raw_eq _ _ (fun _ _ _ => rfl)

theorem forwardInitializedNormalizedField_tower_eq (N : ℕ) (k : ℝ) :
    (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α N k).toFieldTower =
      (coordinateField D (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
          k).toFieldTower :=
  Field.toFieldTower_eq_of_path_eq_forward _ _
    (forwardInitializedNormalizedField_path_eq M D hTime δ hδ ξ hs α N k)

/-- Forward initialized coordinate residual field used in packet forward initialized residual
equation. -/
def forwardInitializedCoordinateResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    Field period D.T (normalizedResidual D k
      (forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹)
      (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)) :=
  (forwardInitializedNormalizedResidualField M D hTime δ hδ ξ hs α Cagree N hN k hk).congr
    (fun t x θ => by
      change k • rawInverse D (t,(x,θ))
          (slicedMomentumResidual (Icc (0 : ℝ) D.T) k⁻¹
            (rawInverse D (t,(x,θ))) (D.strain (t,(x,θ))) (D.normalField (t,(x,θ)))
            (forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹)
            (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹) (t,(x,θ))) =
        k • rawInverse D (t,(x,θ))
          (slicedMomentumResidual (Icc (0 : ℝ) M.T) k⁻¹
            (rawInverse D (t,(x,θ))) (D.strain (t,(x,θ))) (D.normalField (t,(x,θ)))
            (forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹)
            (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹) (t,(x,θ)))
      rw [hTime])

/-- This is the exact initialized correction data used by the quantitative
budget, after identifying the two genuine realizations of its fields. -/
theorem forwardInitializedCorrectionData_eq_coordinate (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) (hκ : |k⁻¹| ≤ 1) :
    forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk =
      coordinateData D k hκ
        (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
        (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)
        (forwardInitializedCoordinateResidualField M D hTime δ hδ ξ hs α Cagree N hN k hk) := by
  unfold forwardInitializedCorrectionData coordinateData correctionDataOfFields
  rw [forwardInitializedNormalizedField_tower_eq M D hTime δ hδ ξ hs α N k]
  rfl

/-- The actual finite pressure and every-order residual identity, with no
assumed pressure field, approximation derivative or residual cancellation. -/
def forwardInitializedApproximationResidual (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ApproximationResidual period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk) := by
  have hk0 : k ≠ 0 := by linarith
  have hκ : |k⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (by linarith : 0 < k))]
    exact inv_le_one_of_one_le₀ (by linarith)
  let Pa := forwardInitializedCoordinatePressureField M D hTime δ hδ ξ hs α N k hk0
  refine { pressure := Pa.toFieldTower, gradient := ?_, equation := ?_ }
  · intro t
    exact forwardInitializedCoordinatePressureField_mem M D hTime δ hδ ξ hs α N k hk0 t
  · intro q hq t ht
    rw [forwardInitializedCorrectionData_eq_coordinate M D hTime δ hδ ξ hs α Cagree N hN k hk hκ]
    exact approximation_hasDerivAt D k hk0 hκ
      (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
      (forwardInitializedVelocityDerivativeField M D hTime δ hδ ξ hs α N k⁻¹)
      (forwardInitializedVelocityField_time M D hTime δ hδ ξ hs α N k⁻¹)
      (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)
      (forwardInitializedCoordinateResidualField M D hTime δ hδ ξ hs α Cagree N hN k hk)
      Pa q hq t ht

end EulerPacketTerminalDatum
