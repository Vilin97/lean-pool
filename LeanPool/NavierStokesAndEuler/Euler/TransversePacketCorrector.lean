/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlTime
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTime
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider

/-! The potential and slow curl of the actual transverse solution, with their genuine time
derivatives. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
      EulerSourcePotentialCoefficient
  EulerPacketProfileRecursion EulerVolterraConvolution EulerMetricTransport
open scoped ContDiff BoundedContinuousFunction

namespace Data

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector3 : NormedAddCommGroup PotentialField := inferInstance
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector4 : NormedSpace ℝ PotentialField := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,PotentialField)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketCorrector5 : NormedAddCommGroup C(Icc (0 : ℝ)
    D.T,PotentialField) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,PotentialField)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCorrector6 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,PotentialField) :=
    inferInstance

/-- Potential coefficient path: an abbreviation for `potentialCoefficient D.normal D.normalLower
D.normalLower_pos D.normal_lower`. -/
abbrev potentialCoefficientPath :=
  potentialCoefficient D.normal D.normalLower D.normalLower_pos D.normal_lower

theorem potentialCoefficientPath_orbit :
    ContDiff ℝ ∞ (translateCoefficientPath D.potentialCoefficientPath) :=
  potentialCoefficient_translation_contDiff D.normal D.normalLower D.normalLower_pos D.normal_lower

theorem potentialCoefficientPath_time (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.potentialCoefficientPath r x)
      (extendPath D.T D.T_pos.le D.potentialDerivative t x) (Icc (0 : ℝ) D.T) t := by
  exact (D.potential_hasDerivWithinAt ⟨t, ht⟩ x).congr_deriv
    (congrArg (fun s : Icc (0 : ℝ) D.T => D.potentialDerivative s x)
      (projIcc_of_mem D.T_pos.le ht).symm)

end Data

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector7 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector8 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported P Space D.support D.support_measurable)`
instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector9 : NormedAddCommGroup (Supported P Space D.support
    D.support_measurable) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported P Space D.support D.support_measurable)`
instance to shorten typeclass synthesis. -/
local instance instTransversePacketCorrector10 : NormedSpace ℝ (Supported P Space D.support
    D.support_measurable) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,LiftL2 P)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketCorrector11 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,LiftL2 P) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketCorrector12 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,LiftL2 P) :=
    inferInstance

/-- Full velocity path: an abbreviation for `includePath P D.support D.support_measurable
(G.velocityPath I)`. -/
abbrev fullVelocityPath := includePath P D.support D.support_measurable (G.velocityPath I)
/-- Full derivative path: an abbreviation for `includePath P D.support D.support_measurable
(G.derivativePath I)`. -/
abbrev fullDerivativePath := includePath P D.support D.support_measurable (G.derivativePath I)

theorem fullVelocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (G.fullVelocityPath I))
      (G.fullDerivativePath I t) (Icc (0 : ℝ) D.T) t :=
  (Supported P Space D.support D.support_measurable).subtypeL.hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) (G.velocityPath_time I t)

/-- Potential path, given by `EulerCylinderPotential.potentialPath P D.potentialCoefficientPath
(G.fullVelocityPath I)`. -/
def potentialPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialPath P D.potentialCoefficientPath (G.fullVelocityPath I)

/-- Potential time path, constructed using `EulerCylinderPotential.potentialDerivative`. -/
def potentialTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialDerivative P D.T D.potentialCoefficientPath D.potentialDerivative
    (G.fullVelocityPath I) (G.fullDerivativePath I)

theorem potentialPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.potentialPath I)) :=
  EulerCylinderPotential.potentialPath_orbit P D.potentialCoefficientPath
      D.potentialCoefficientPath_orbit
    (G.fullVelocityPath I) (G.velocityPath_orbit I)

theorem potentialTimePath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.potentialTimePath I)) :=
  EulerCylinderPotential.potentialDerivative_orbit P D.T D.potentialCoefficientPath
      D.potentialDerivative
    D.potentialCoefficientPath_orbit D.potentialDerivative_orbit
    (G.fullVelocityPath I) (G.fullDerivativePath I) (G.velocityPath_orbit I)
        (G.derivativePath_orbit I)

theorem potentialPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (G.potentialPath I))
      (G.potentialTimePath I t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderPotential.potentialPath_hasDerivWithinAt P D.T D.T_pos.le
    D.potentialCoefficientPath D.potentialDerivative (G.fullVelocityPath I) (G.fullDerivativePath I)
    D.potentialCoefficientPath_time (G.fullVelocityPath_time I) t

/-- Corrector path, given by `EulerCylinderSlowCurl.path P D.FInv.field (G.potentialPath I)`. -/
def correctorPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.path P D.FInv.field (G.potentialPath I)

/-- Corrector time path, given by `EulerCylinderSlowCurl.derivative P D.T D.FInv.field
D.inverseDerivative (G.potentialPath I) (G.potentialTimePath I)`. -/
def correctorTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.derivative P D.T D.FInv.field D.inverseDerivative
    (G.potentialPath I) (G.potentialTimePath I)

theorem correctorPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.correctorPath I)) :=
  EulerCylinderSlowCurl.path_orbit P D.FInv.field D.FInv.translation_contDiff
    (G.potentialPath I) (G.potentialPath_orbit I)

theorem correctorTimePath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (G.correctorTimePath I)) :=
  EulerCylinderSlowCurl.derivative_orbit P D.T D.FInv.field D.inverseDerivative
    D.FInv.translation_contDiff D.inverseDerivative_orbit (G.potentialPath I) (G.potentialTimePath
        I)
    (G.potentialPath_orbit I) (G.potentialTimePath_orbit I)

theorem correctorPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (G.correctorPath I))
      (G.correctorTimePath I t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderSlowCurl.path_hasDerivWithinAt P D.T D.T_pos.le D.FInv.field D.inverseDerivative
    (G.potentialPath I) (G.potentialTimePath I) (G.potentialPath_orbit I)
        (G.potentialTimePath_orbit I)
    D.inverse_hasDerivWithinAt (G.potentialPath_time I) t

/-- Corrector, defined pointwise by `pointField P (G.correctorPath I) (G.correctorPath_orbit I)
(D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def corrector : VectorField := fun z =>
  pointField P (G.correctorPath I) (G.correctorPath_orbit I)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

/-- Corrector derivative, defined pointwise by `pointField P (G.correctorTimePath I)
(G.correctorTimePath_orbit I) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def correctorDerivative : VectorField := fun z =>
  pointField P (G.correctorTimePath I) (G.correctorTimePath_orbit I)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

theorem corrector_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun r => G.corrector I (r,(x,θ)))
      (G.correctorDerivative I (t,(x,θ))) (Icc (0 : ℝ) D.T) t := by
  have h := pointField_hasDerivWithinAt P D.T D.T_pos.le (G.correctorPath I) (G.correctorTimePath I)
    (G.correctorPath_orbit I) (G.correctorTimePath_orbit I) (G.correctorPath_time I) t (x,(θ :
        AddCircle P))
  simpa only [corrector, correctorDerivative, Data.clamp, projIcc_of_mem D.T_pos.le t.property]
      using h

theorem fullVelocityPath_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I)
      t (x,(θ : AddCircle P))) = 0 := by
  simpa only [vector, EulerSourceCylinderClassical.field, Data.clamp_coe] using G.vector_mean_zero
      I t x

/-- This potential is exactly the manuscript's normalized angular integral of −m×A/|m|². -/
theorem potentialPath_eq_periodic (t : Icc (0 : ℝ) D.T) :
    pointField P (G.potentialPath I) (G.potentialPath_orbit I) t =
      EulerPacketPeriodicPotential.field P (fun x => D.normal.field t x)
        (pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I) t) :=
  EulerCylinderPotential.potentialField_eq_periodic P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit (G.fullVelocityPath I) (G.velocityPath_orbit I)
    (G.fullVelocityPath_mean_zero I) (fun t x => D.normal.field t x)
    (potentialCoefficient_apply D.normal D.normalLower D.normalLower_pos D.normal_lower) t

/-- The stored corrector is the literal slow curl with the actual inverse deformation. -/
theorem corrector_formula (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.corrector I (t,(x,θ)) =
      EulerMeanBoundary.curlMatrix
        ((EulerLiftedWeakDerivative.fieldFDeriv P
          (pointField P (G.potentialPath I) (G.potentialPath_orbit I) t) (x,(θ : AddCircle P))).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field t x))) := by
  change EulerCylinderSlowCurl.field P D.FInv.field D.FInv.translation_contDiff
    (G.potentialPath I) (G.potentialPath_orbit I) (D.clamp t) (x,(θ : AddCircle P)) = _
  rw [Data.clamp_coe]
  exact EulerCylinderSlowCurl.field_formula P D.FInv.field D.FInv.translation_contDiff
    (G.potentialPath I) (G.potentialPath_orbit I) t (x,(θ : AddCircle P))

end Forcing
end EulerTransversePacketProvider
