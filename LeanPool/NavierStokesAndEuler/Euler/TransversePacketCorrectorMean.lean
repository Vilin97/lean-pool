/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime
import LeanPool.NavierStokesAndEuler.Euler.CylinderCorrectorMeanZero
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero

/-! Zero angular mean of the actual transverse potential, corrector, and time derivatives. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerCylinderAngleAverage
  EulerCylinderCorrectorMeanZero EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem fullVelocityPath_average_zero : pathAverage P (G.fullVelocityPath I) = 0 :=
  (pathAverage_eq_zero_iff P (G.fullVelocityPath I) (G.velocityPath_orbit I)).mpr
    (G.fullVelocityPath_mean_zero I)

theorem fullDerivativePath_average_zero : pathAverage P (G.fullDerivativePath I) = 0 := by
  apply ContinuousMap.ext
  intro t
  exact EulerSourceCylinderEquation.velocityDerivative_average_zero P D.support D.support_measurable
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value G.mean_zero I.mean_zero t

theorem potentialPath_average_zero : pathAverage P (G.potentialPath I) = 0 :=
  potentialPath_mean_zero P (G.fullVelocityPath I) D.potentialCoefficientPath
    (G.fullVelocityPath_average_zero I)

theorem potentialTimePath_average_zero : pathAverage P (G.potentialTimePath I) = 0 := by
  rw [potentialTimePath, EulerCylinderPotential.potentialDerivative, map_add,
    potentialPath_mean_zero P (G.fullVelocityPath I) D.potentialDerivative
        (G.fullVelocityPath_average_zero I),
    potentialPath_mean_zero P (G.fullDerivativePath I) D.potentialCoefficientPath
        (G.fullDerivativePath_average_zero I),
    add_zero]

theorem correctorPath_average_zero : pathAverage P (G.correctorPath I) = 0 :=
  slowCurl_mean_zero P (G.potentialPath I) (G.potentialPath_orbit I) D.FInv.field
    (G.potentialPath_average_zero I)

theorem correctorTimePath_average_zero : pathAverage P (G.correctorTimePath I) = 0 := by
  rw [correctorTimePath, EulerCylinderSlowCurl.derivative, map_add,
    slowCurl_mean_zero P (G.potentialPath I) (G.potentialPath_orbit I) D.inverseDerivative
      (G.potentialPath_average_zero I),
    slowCurl_mean_zero P (G.potentialTimePath I) (G.potentialTimePath_orbit I) D.FInv.field
      (G.potentialTimePath_average_zero I), add_zero]

theorem corrector_mean_zero (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, G.corrector I (t,(x,θ))) = 0 :=
  (pathAverage_eq_zero_iff P (G.correctorPath I) (G.correctorPath_orbit I)).mp
    (G.correctorPath_average_zero I) (D.clamp t) x

theorem correctorDerivative_mean_zero (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, G.correctorDerivative I (t,(x,θ))) = 0 :=
  (pathAverage_eq_zero_iff P (G.correctorTimePath I) (G.correctorTimePath_orbit I)).mp
    (G.correctorTimePath_average_zero I) (D.clamp t) x

end EulerTransversePacketProvider.Forcing
