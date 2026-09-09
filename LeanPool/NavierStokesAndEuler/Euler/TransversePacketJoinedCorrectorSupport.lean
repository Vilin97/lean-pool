/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedCorrector
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime
import LeanPool.NavierStokesAndEuler.Euler.CylinderCorrectorMeanZero
import LeanPool.NavierStokesAndEuler.Euler.CylinderLocalSupport
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport

/-! Support and zero angular mean of the literal joined corrector and its actual time derivative. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerCylinderLocalSupport
  EulerCylinderAngleAverage EulerCylinderCorrectorMeanZero EulerPacketProfileRecursion
  EulerTransversePacketProvider EulerElapsedTimePathGluing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

theorem derivativePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (derivativePath τ hτ hτT B G t) = 0 := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B G)
    {u | average P u = 0} _ _ t
  · exact B.derivativePath_mean_zero (G.initial τ hτ hτT.le)
  · intro s
    exact EulerSourceCylinderEquation.velocityDerivative_average_zero P D.support
        D.support_measurable
      (D.T-τ) (sub_pos.mpr hτT).le
      (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
      (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos
      (D.tail τ hτ.le hτT).frame_lower (G.tail τ hτ.le hτT).path
      (forwardInitial τ hτ hτT B G).value (G.tail τ hτ.le hτT).mean_zero
      (forwardInitial τ hτ hτT B G).mean_zero s

theorem potentialPath_supported (t : Icc (0 : ℝ) D.T) :
    potentialPath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable :=
  EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
    (velocityPath τ hτ hτT B G) D.potentialCoefficientPath (velocityPath_supported τ hτ hτT B G) t

theorem potentialTimePath_supported (t : Icc (0 : ℝ) D.T) :
    potentialTimePath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable := by
  apply (Supported P Space D.support D.support_measurable).add_mem
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (velocityPath τ hτ hτT B G) D.potentialDerivative (velocityPath_supported τ hτ hτT B G) t
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (derivativePath τ hτ hτT B G) D.potentialCoefficientPath (derivativePath_supported τ hτ hτT B
          G) t

theorem correctorPath_supported (t : Icc (0 : ℝ) D.T) :
    correctorPath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable :=
  slowCurlPath_supported P D.support D.support_measurable (potentialPath τ hτ hτT B G)
    (potentialPath_orbit τ hτ hτT B G) D.FInv.field D.support_compact.isClosed
    (potentialPath_supported τ hτ hτT B G) t

theorem correctorTimePath_supported (t : Icc (0 : ℝ) D.T) :
    correctorTimePath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable := by
  apply (Supported P Space D.support D.support_measurable).add_mem
  · exact slowCurlPath_supported P D.support D.support_measurable (potentialPath τ hτ hτT B G)
      (potentialPath_orbit τ hτ hτT B G) D.inverseDerivative D.support_compact.isClosed
      (potentialPath_supported τ hτ hτT B G) t
  · exact slowCurlPath_supported P D.support D.support_measurable (potentialTimePath τ hτ hτT B G)
      (potentialTimePath_orbit τ hτ hτT B G) D.FInv.field D.support_compact.isClosed
      (potentialTimePath_supported τ hτ hτT B G) t

theorem potentialPath_average_zero : pathAverage P (potentialPath τ hτ hτT B G) = 0 :=
  potentialPath_mean_zero P (velocityPath τ hτ hτT B G) D.potentialCoefficientPath
    (ContinuousMap.ext (velocityPath_mean_zero τ hτ hτT B G))

theorem potentialTimePath_average_zero : pathAverage P (potentialTimePath τ hτ hτT B G) = 0 := by
  rw [potentialTimePath,EulerCylinderPotential.potentialDerivative,map_add,
    potentialPath_mean_zero P (velocityPath τ hτ hτT B G) D.potentialDerivative
      (ContinuousMap.ext (velocityPath_mean_zero τ hτ hτT B G)),
    potentialPath_mean_zero P (derivativePath τ hτ hτT B G) D.potentialCoefficientPath
      (ContinuousMap.ext (derivativePath_mean_zero τ hτ hτT B G)),add_zero]

theorem correctorPath_average_zero : pathAverage P (correctorPath τ hτ hτT B G) = 0 :=
  slowCurl_mean_zero P (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G)
    D.FInv.field (potentialPath_average_zero τ hτ hτT B G)

theorem correctorTimePath_average_zero : pathAverage P (correctorTimePath τ hτ hτT B G) = 0 := by
  rw [correctorTimePath,EulerCylinderSlowCurl.derivative,map_add,
    slowCurl_mean_zero P (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G)
      D.inverseDerivative (potentialPath_average_zero τ hτ hτT B G),
    slowCurl_mean_zero P (potentialTimePath τ hτ hτT B G) (potentialTimePath_orbit τ hτ hτT B G)
      D.FInv.field (potentialTimePath_average_zero τ hτ hτT B G),add_zero]

theorem corrector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    corrector τ hτ hτT B G (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (correctorPath τ hτ hτT B G)
    (correctorPath_orbit τ hτ hτT B G) D.support_compact.isClosed
    (correctorPath_supported τ hτ hτT B G) (D.clamp t) (x,(θ : AddCircle P)) hx

theorem correctorDerivative_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    correctorDerivative τ hτ hτT B G (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (correctorTimePath τ hτ hτT B G)
    (correctorTimePath_orbit τ hτ hτT B G) D.support_compact.isClosed
    (correctorTimePath_supported τ hτ hτT B G) (D.clamp t) (x,(θ : AddCircle P)) hx

theorem curlCorrector_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, D.curlCorrector P (vector τ hτ hτT B G) (t,(x,θ))) = 0 := by
  have he : (fun θ => D.curlCorrector P (vector τ hτ hτT B G) (t,(x,θ))) =
      fun θ => corrector τ hτ hτT B G (t,(x,θ)) := funext (curlCorrector_eq τ hτ hτT B G t x)
  rw [he]
  exact (pathAverage_eq_zero_iff P (correctorPath τ hτ hτT B G) (correctorPath_orbit τ hτ hτT B
      G)).mp
    (correctorPath_average_zero τ hτ hτT B G) (D.clamp t) x

end EulerTransversePacketJoin
