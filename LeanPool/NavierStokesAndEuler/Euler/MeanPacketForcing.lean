/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketData
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRecursion
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPressure
import LeanPool.NavierStokesAndEuler.Euler.ContinuousForcingTimeLp
import LeanPool.NavierStokesAndEuler.Euler.ContinuousForcingTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalSpatialTime
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.MeanConcreteTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
import LeanPool.NavierStokesAndEuler.Euler.MeanForcingTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanPhysicalTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSpatialRegularity
import LeanPool.NavierStokesAndEuler.Euler.MeanStrongGevrey

/-!
# Admissible raw mean forcing and its actual solved continuous paths

Admissibility consists of literal smooth spatial L² slices and continuity of
their L² spatial jets. All translation regularity below is derived. The
solution paths are obtained by the concrete source inverse in MeanPacketData.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanSourceInverse EulerMeanVariationalInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerTimeLp EulerVolterraConvolution EulerPacketProfileRecursion
open scoped ContDiff

/-- Literal raw-field regularity, with no hypothesis on a solved field. -/
structure Forcing (D : Data) (raw : VectorField) where
  /-- Slices of `Forcing`, of type `ℝ → EulerLpTranslation.SmoothL2Field Space`. -/
  slices : ℝ → EulerLpTranslation.SmoothL2Field Space
  jets_continuous : ∀ n, Continuous (fun t : Icc (0 : ℝ) D.T => (slices t).jetLp n)
  /-- Time-dependent path of `Forcing`, of type `C(Icc (0 : ℝ) D.T,L2)`. -/
  path : C(Icc (0 : ℝ) D.T,L2)
  path_eq : ∀ t, path t = (slices t).toLp
  raw_eq : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(x,θ)) = (slices t).field x

namespace Data

variable (D : Data)

theorem opF_orbit : ContDiff ℝ ∞ (fun a : Space => translatePath D.T a D.opF) := by
  simpa only [opF, translatePath_operatorPath] using operatorPathTranslation_contDiff D.T D.F

theorem opF₁_orbit : ContDiff ℝ ∞ (fun a : Space => translatePath D.T a D.opF₁) := by
  simpa only [opF₁, translatePath_operatorPath] using operatorPathTranslation_contDiff D.T D.F₁

theorem opF_initial : D.opF ⟨0, le_rfl, D.T_pos.le⟩ = ContinuousLinearMap.id ℝ L2 := by
  apply ContinuousLinearMap.ext
  intro v
  have hi := D.opInv_left ⟨0, le_rfl, D.T_pos.le⟩ v
  rw [D.opInv_initial] at hi
  exact hi

end Data

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

/-- The genuine Bochner L² class of the prescribed forcing. -/
def lp : TimeLp D.T L2 := pathLp D.T D.T_pos.le G.path

theorem lp_rep : (G.lp : ℝ → L2) =ᵐ[timeMeasure D.T] extendPath D.T D.T_pos.le G.path :=
  pathLp_ae D.T D.T_pos.le G.path

theorem lp_orbit : ContDiff ℝ ∞ (fun a : Space => timeTranslation D.T a G.lp) :=
  EulerMeanForcing.forcing_translation_contDiff D.T G.slices
    (EulerContinuousForcing.spatialJets_memLp D.T D.T_pos.le G.slices G.jets_continuous) G.lp
    (EulerContinuousForcing.forcing_representation D.T D.T_pos.le G.slices G.path G.path_eq G.lp
        G.lp_rep)

theorem path_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a G.path) :=
  EulerContinuousForcing.forcing_translation_contDiff
    (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous G.path G.path_eq

/-- Solution: an abbreviation for `D.evolution G.lp`. -/
abbrev solution := D.evolution G.lp

/-- Spatial smoothness of the actually solved coordinate velocity. -/
theorem coordinate_orbit : ContDiff ℝ ∞
    (fun a : Space => timeSolenoidalTranslation D.T a G.solution.velocityLp) :=
  EulerMeanSourceSpatialRegularity.velocity_translation_contDiff
    D.T D.T_pos.le D.ℓ D.ℓ_pos D.F D.F₁ D.H D.M0 D.opInv D.Be D.Bc D.L D.r
    D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter D.exterior_lower D.core_lower
    D.opInv_left D.opF_time D.opInv_right D.K D.K_nonneg D.opInv_initial D.curvature_upper D.small
    G.lp G.solution G.lp_orbit

theorem acceleration_orbit : ContDiff ℝ ∞
    (fun a : Space => timeSolenoidalTranslation D.T a G.solution.acceleration) :=
  G.solution.acceleration_orbit_contDiff D.frameLower D.frameLower_pos D.frame_lower
    D.opF_orbit D.opF₁_orbit G.coordinate_orbit G.lp_orbit

theorem coordinatePath_orbit : ContDiff ℝ ∞
    (fun a : Space => coordinatePathTranslation D.T a G.solution.coordinateVelocityPath) :=
  G.solution.coordinateVelocityPath_translation_contDiff D.T_pos G.coordinate_orbit
      G.acceleration_orbit

/-- Velocity path: an abbreviation for `G.solution.continuousVelocity`. -/
abbrev velocityPath := G.solution.continuousVelocity
/-- Acceleration path: an abbreviation for `G.solution.classicalAcceleration D.frameLower
D.frameLower_pos D.frame_lower G.path`. -/
abbrev accelerationPath := G.solution.classicalAcceleration D.frameLower D.frameLower_pos
    D.frame_lower G.path
/-- Derivative path: an abbreviation for `G.solution.classicalPhysicalDerivative D.frameLower
D.frameLower_pos D.frame_lower G.path`. -/
abbrev derivativePath := G.solution.classicalPhysicalDerivative D.frameLower D.frameLower_pos
    D.frame_lower G.path
/-- Pressure force path: an abbreviation for `G.solution.pressurePath D.frameLower
D.frameLower_pos D.frame_lower G.path`. -/
abbrev pressureForcePath := G.solution.pressurePath D.frameLower D.frameLower_pos D.frame_lower
    G.path

theorem velocityPath_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a G.velocityPath) :=
  G.solution.continuousVelocity_translation_contDiff
    (G.solution.velocityField_translation_contDiff D.opF_orbit G.coordinate_orbit)
    (G.solution.velocityDerivative_translation_contDiff D.opF_orbit D.opF₁_orbit
      G.coordinate_orbit G.acceleration_orbit)

theorem accelerationPath_orbit : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation D.T a
    G.accelerationPath) :=
  G.solution.classicalAcceleration_translation_contDiff D.frameLower D.frameLower_pos D.frame_lower
      G.path
    D.opF_orbit D.opF₁_orbit G.coordinatePath_orbit G.path_orbit

theorem derivativePath_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a
    G.derivativePath) :=
  G.solution.classicalPhysicalDerivative_translation_contDiff D.frameLower D.frameLower_pos
      D.frame_lower G.path
    D.opF_orbit D.opF₁_orbit G.coordinatePath_orbit G.path_orbit

theorem pressureForcePath_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a
    G.pressureForcePath) :=
  G.solution.pressurePath_translation_contDiff D.frameLower D.frameLower_pos D.frame_lower G.path
    D.opF_orbit D.opF₁_orbit G.coordinatePath_orbit G.accelerationPath_orbit G.path_orbit

theorem velocityPath_time : ∀ t : Icc (0 : ℝ) D.T,
    HasDerivWithinAt (extendPath D.T D.T_pos.le G.velocityPath) (G.derivativePath t) (Icc (0 : ℝ)
        D.T) t :=
  G.solution.continuousVelocity_hasDerivWithinAt D.frameLower D.frameLower_pos D.frame_lower G.path
    D.T_pos G.lp_rep D.opF_time

end Forcing

end EulerMeanPacketProvider
