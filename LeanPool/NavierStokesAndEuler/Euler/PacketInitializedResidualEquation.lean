/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedPressureAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCoordinateSobolev
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileFields
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftEquation
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique

/-! The literal initialized packet supplies the all-order approximation
residual identity, including its actual pressure gradient.  Its velocity,
time derivative and residual are the fields already constructed from the
source profiles, not additional approximation hypotheses. -/

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
