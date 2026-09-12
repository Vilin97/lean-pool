/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRecursion
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureField

/-!
# Actual forcing and initial data for the transverse forward provider

Admissibility identifies the prescribed raw forcing with a genuine supported
continuous cylinder L² path whose mixed translation orbit is smooth. No
regularity or equation for an output field is assumed.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerCylinderSmoothOrbit EulerCylinderAngleAverage EulerPacketProfileRecursion
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Forcing data, collecting `path`, `path_orbit`, `raw_eq`, `mean_zero`. -/
structure Forcing (D : Data U) (raw : VectorField) where
  /-- Time-dependent path of `Forcing`, of type `C(Icc (0 : ℝ) D.T,Supported P Space D.support
  D.support_measurable)`. -/
  path : C(Icc (0 : ℝ) D.T,Supported P Space D.support D.support_measurable)
  path_orbit : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a
    (includePath P D.support D.support_measurable path))
  raw_eq : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(x,θ)) =
    pointField P (includePath P D.support D.support_measurable path) path_orbit t (x,(θ : AddCircle
        P))
  mean_zero : ∀ t, average P (path t : CylinderL2 P Space) = 0

/-- Initial data, collecting `value`, `orbit`, `mean_zero`. -/
structure InitialData (D : Data U) where
  /-- Value of `InitialData`, of type `Supported P U D.support D.support_measurable`. -/
  value : Supported P U D.support D.support_measurable
  orbit : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (value : CylinderL2 P U))
  mean_zero : average P (value : CylinderL2 P U) = 0

/-- Zero, bundling `value`, `orbit`, `mean_zero`. -/
def InitialData.zero (D : Data U) : InitialData P D where
  value := 0
  orbit := by
    simpa only [Submodule.coe_zero, map_zero] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : CylinderL2 P U)))
  mean_zero := map_zero _

namespace Data

/-- Clamp, given by `projIcc 0 D.T D.T_pos.le t`. -/
def clamp (D : Data U) (t : ℝ) : Icc (0 : ℝ) D.T := projIcc 0 D.T D.T_pos.le t

omit [CompleteSpace U] in
@[simp] theorem clamp_coe (D : Data U) (t : Icc (0 : ℝ) D.T) : D.clamp t = t :=
  projIcc_of_mem D.T_pos.le t.property

/-- Strain, given by `D.M.field (D.clamp z.1) z.2.1`. -/
def strain (D : Data U) (z : EulerPacketPointJets.Domain) : Space →L[ℝ] Space :=
  D.M.field (D.clamp z.1) z.2.1

/-- Normal field, given by `D.normal.field (D.clamp z.1) z.2.1`. -/
def normalField (D : Data U) (z : EulerPacketPointJets.Domain) : Space :=
  D.normal.field (D.clamp z.1) z.2.1

end Data

namespace Forcing

variable {P} {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

/-- Coordinate path type used in transverse packet forcing. -/
abbrev coordinatePath := EulerSourceCylinderEquation.coordinates P D.support D.support_measurable
  D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path
      I.value

/-- Velocity path type used in transverse packet forcing. -/
abbrev velocityPath := EulerSourceCylinderEquation.velocity P D.support D.support_measurable
  D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path
      I.value

/-- Derivative path type used in transverse packet forcing. -/
abbrev derivativePath := EulerSourceCylinderEquation.velocityDerivative P D.support
    D.support_measurable
  D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path
      I.value

/-- Pressure path type used in transverse packet forcing. -/
abbrev pressurePath := EulerSourceCylinderEquation.pressurePath P D.support D.support_measurable
  D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path
      I.value
  D.M D.normal D.normalLower D.normalLower_pos D.normal_lower

theorem velocityPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a
      (includePath P D.support D.support_measurable (G.velocityPath I))) :=
  EulerSourceCylinderEquation.velocity_contDiff P D.support D.support_measurable D.support_compact
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value G.path_orbit I.orbit

theorem derivativePath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a
      (includePath P D.support D.support_measurable (G.derivativePath I))) :=
  EulerSourceCylinderEquation.velocityDerivative_contDiff P D.support D.support_measurable
      D.support_compact
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value G.path_orbit I.orbit

theorem pressurePath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.pressurePath I)) :=
  EulerSourceCylinderEquation.pressurePath_contDiff P D.support D.support_measurable
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    D.support_compact G.path_orbit I.orbit

theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (EulerVolterraConvolution.extendPath D.T D.T_pos.le (G.velocityPath I))
      (G.derivativePath I t) (Icc (0 : ℝ) D.T) t :=
  EulerSourceCylinderEquation.velocity_hasDerivWithinAt P D.support D.support_measurable
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value D.frame_derivative t

end Forcing

end EulerTransversePacketProvider
