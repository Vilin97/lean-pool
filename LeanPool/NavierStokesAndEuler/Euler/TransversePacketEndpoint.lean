/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointData
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointEquation
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointSupport
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory

/-!
The actual source history with prescribed compact terminal displacement.
`Y.value` is an L² field of reference-plane coordinates. It is passed to
the constructed affine-endpoint inverse, not imposed as a solution law.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketEndpoint

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderAngleAverage
  EulerVolterraConvolution EulerTransversePacketProvider EulerCylinderSmoothOrbit
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) (Y : InitialData P D)

/-- Displacement path, given by `B.coefficients.endpointDisplacement P (Y.value : CylinderL2 P
U)`. -/
def displacementPath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.endpointDisplacement P (Y.value : CylinderL2 P U)

/-- Coordinate path, given by `B.coefficients.endpointCoordinate P (Y.value : CylinderL2 P U)`. -/
def coordinatePath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.endpointCoordinate P (Y.value : CylinderL2 P U)

/-- Coordinate derivative path, given by `B.coefficients.endpointAcceleration P (Y.value :
CylinderL2 P U)`. -/
def coordinateDerivativePath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.endpointAcceleration P (Y.value : CylinderL2 P U)

/-- Velocity path, given by `B.coefficients.endpointVelocity P (Y.value : CylinderL2 P U)`. -/
def velocityPath : C(Icc (0 : ℝ) D.T,CylinderL2 P Space) :=
  B.coefficients.endpointVelocity P (Y.value : CylinderL2 P U)

/-- Derivative path, given by `B.coefficients.endpointDerivative P (Y.value : CylinderL2 P U)`. -/
def derivativePath : C(Icc (0 : ℝ) D.T,CylinderL2 P Space) :=
  B.coefficients.endpointDerivative P (Y.value : CylinderL2 P U)

theorem displacement_initial : displacementPath B Y ⟨0,le_rfl,D.T_pos.le⟩ = 0 :=
  B.coefficients.endpointDisplacement_initial P Y.value

theorem displacement_terminal : displacementPath B Y ⟨D.T,D.T_pos.le,le_rfl⟩ = Y.value :=
  B.coefficients.endpointDisplacement_terminal P Y.value

theorem coordinatePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (coordinatePath B Y)) :=
  B.coefficients.endpointCoordinate_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit

theorem coordinateDerivativePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (coordinateDerivativePath B Y)) :=
  B.coefficients.endpointAcceleration_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit

theorem velocityPath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (velocityPath B Y)) :=
  B.coefficients.endpointVelocity_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit

theorem derivativePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (derivativePath B Y)) :=
  B.coefficients.endpointDerivative_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit

theorem displacementPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (displacementPath B Y))
      (coordinatePath B Y t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.endpointDisplacement_hasDerivWithinAt P Y.value t

theorem coordinatePath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (coordinatePath B Y))
      (coordinateDerivativePath B Y t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.endpointCoordinate_hasDerivWithinAt P Y.value t

theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (velocityPath B Y))
      (derivativePath B Y t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.endpointVelocity_hasDerivWithinAt P Y.value t

theorem coordinatePath_supported (t : Icc (0 : ℝ) D.T) :
    coordinatePath B Y t ∈ Supported P U D.support D.support_measurable :=
  B.coefficients.endpointCoordinate_supported P D.support D.support_measurable
    Y.value Y.value.property t

theorem velocityPath_supported (t : Icc (0 : ℝ) D.T) :
    velocityPath B Y t ∈ Supported P Space D.support D.support_measurable :=
  B.coefficients.endpointVelocity_supported P D.support D.support_measurable
    Y.value Y.value.property t

theorem derivativePath_supported (t : Icc (0 : ℝ) D.T) :
    derivativePath B Y t ∈ Supported P Space D.support D.support_measurable :=
  B.coefficients.endpointDerivative_supported P D.support D.support_measurable
    Y.value Y.value.property t

theorem coordinatePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (coordinatePath B Y t) = 0 :=
  B.coefficients.endpointCoordinate_mean_zero P Y.value Y.mean_zero t

theorem velocityPath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (velocityPath B Y t) = 0 :=
  B.coefficients.endpointVelocity_mean_zero P Y.value Y.mean_zero t

theorem derivativePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (derivativePath B Y t) = 0 :=
  B.coefficients.endpointDerivative_mean_zero P Y.value Y.mean_zero t

/-- Terminal initial, bundling `value`, `orbit`, `mean_zero`. -/
def terminalInitial : InitialData P D where
  value := ⟨coordinatePath B Y ⟨D.T,D.T_pos.le,le_rfl⟩,
    coordinatePath_supported B Y _⟩
  orbit := (ContinuousMap.evalCLM ℝ ⟨D.T,D.T_pos.le,le_rfl⟩ :
    C(Icc (0 : ℝ) D.T,CylinderL2 P U) →L[ℝ] CylinderL2 P U).contDiff.comp
      (coordinatePath_orbit B Y)
  mean_zero := coordinatePath_mean_zero B Y _

theorem velocityPath_ae (t : Icc (0 : ℝ) D.T) :
    velocityPath B Y t =ᵐ[liftMeasure P] fun x => D.frame.field t x.1 (coordinatePath B Y t x) :=
  B.coefficients.endpointVelocity_ae P Y.value t

theorem balance_ae (t : Icc (0 : ℝ) D.T) :
    ∀ᵐ x ∂liftMeasure P,
      derivativePath B Y t x+D.M.field t x.1 (velocityPath B Y t x) +
        (-(2*⟪D.normal.field t x.1,D.M.field t x.1 (velocityPath B Y t x)⟫_ℝ)/
          ‖D.normal.field t x.1‖^2) • D.normal.field t x.1 = 0 :=
  B.coefficients.endpoint_physical_balance_ae P Y.value
    (fun t x => D.M.field t x) (fun t x => D.normal.field t x)
    (HistoryData.normal_ne_zero (D := D)) D.frame_tangent D.frame_range D.frame_strain t

end EulerTransversePacketEndpoint
