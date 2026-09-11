/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCylinderFields
import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime
import LeanPool.NavierStokesAndEuler.Euler.CylinderCorrectorMeanZero
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero

/-! The literal raw-field corrector operator used by the recursive packet definition. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerPacketCylinderField EulerCylinderSmoothOrbit EulerSourcePotentialCoefficient
  EulerMetricTransport

namespace Data

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

/-- The specified mean-zero angular primitive, applied directly to a raw field. -/
def rawPotential (P : ℝ) (A : VectorField) : VectorField := fun z =>
  EulerPacketAngularPotential.potential P (D.normal.field (D.clamp z.1) z.2.1)
    (fun θ => A (z.1,(z.2.1,θ))) z.2.2

/-- The actual slow curl in deformation coordinates; this defines a total raw-field operator. -/
def curlCorrector (P : ℝ) (A : VectorField) : VectorField := fun z =>
  EulerMeanBoundary.curlMatrix
    ((fderiv ℝ (fun y : LiftTangent => D.rawPotential P A (z.1,y)) z.2).comp
      ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field (D.clamp z.1) z.2.1)))

end Data

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem rawPotential_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.rawPotential P (G.vector I) (t,(x,θ)) =
      pointField P (G.potentialPath I) (G.potentialPath_orbit I) t (x,(θ : AddCircle P)) := by
  have he : (fun s : ℝ => G.vector I (t,(x,s))) = fun s : ℝ =>
      pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I) t (x,(s : AddCircle P)) :=
    funext (fun s => (G.vectorField I).raw_eq t x s)
  rw [Data.rawPotential, Data.clamp_coe, he]
  exact (EulerCylinderPotential.potentialField_source_formula P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit (G.fullVelocityPath I) (G.velocityPath_orbit I)
    (G.fullVelocityPath_mean_zero I) (fun t x => D.normal.field t x)
    (potentialCoefficient_apply D.normal D.normalLower D.normalLower_pos D.normal_lower) t x θ).symm

theorem curlCorrector_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.curlCorrector P (G.vector I) (t,(x,θ)) = G.corrector I (t,(x,θ)) := by
  have he : (fun y : LiftTangent => D.rawPotential P (G.vector I) (t,y)) =
      fun y : LiftTangent => pointField P (G.potentialPath I) (G.potentialPath_orbit I)
        t (y.1,(y.2 : AddCircle P)) := funext (fun y => G.rawPotential_eq I t y.1 y.2)
  rw [Data.curlCorrector, Data.clamp_coe, he, coverField_fderiv, G.corrector_formula I t x θ]

/-- The literal recursion operator has the already-constructed continuous L² witness. -/
def curlCorrectorField : Field P D.T (D.curlCorrector P (G.vector I)) where
  path := G.correctorPath I
  orbit := G.correctorPath_orbit I
  raw_eq t x θ := (G.curlCorrector_eq I t x θ).trans ((G.correctorField I).raw_eq t x θ)

theorem curlCorrectorField_time :
    TimeDerivative D.T_pos.le (G.curlCorrectorField I) (G.correctorDerivativeField I) :=
  G.correctorPath_time I

theorem curlCorrector_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, D.curlCorrector P (G.vector I) (t,(x,θ))) = 0 := by
  have he : (fun θ => D.curlCorrector P (G.vector I) (t,(x,θ))) =
      fun θ => G.corrector I (t,(x,θ)) := funext (fun θ => G.curlCorrector_eq I t x θ)
  rw [he]
  exact G.corrector_mean_zero I t x

end Forcing
end EulerTransversePacketProvider
