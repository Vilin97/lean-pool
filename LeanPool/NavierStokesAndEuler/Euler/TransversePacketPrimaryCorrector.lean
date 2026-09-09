/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryField
public import LeanPool.NavierStokesAndEuler.Euler.CylinderLocalSupport
public import LeanPool.NavierStokesAndEuler.Euler.CylinderCorrectorMeanZero
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorParity

@[expose] public section

/-!
# The literal corrector of the terminal-data primary solution

The actual global velocity and its true time derivative construct Q, Q_t,
C and C_t. The returned Field is for the literal raw curlCorrector used by
the recursion, including at the history/forward junction.
-/

noncomputable section

namespace EulerTransversePacketPrimary

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
    EulerSourcePotentialCoefficient
  EulerPacketProfileRecursion EulerVolterraConvolution EulerMetricTransport
  EulerTransversePacketProvider EulerPacketCylinderField
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

def potentialPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialPath P D.potentialCoefficientPath (velocityPath τ hτ hτT B Y)

def potentialTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialDerivative P D.T D.potentialCoefficientPath D.potentialDerivative
    (velocityPath τ hτ hτT B Y) (derivativePath τ hτ hτT B Y)

theorem potentialPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (potentialPath τ hτ hτT B
  Y)) :=
  EulerCylinderPotential.potentialPath_orbit P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit
    (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y)

theorem potentialTimePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (potentialTimePath τ hτ
  hτT B Y)) :=
  EulerCylinderPotential.potentialDerivative_orbit P D.T D.potentialCoefficientPath
    D.potentialDerivative
    D.potentialCoefficientPath_orbit D.potentialDerivative_orbit
    (velocityPath τ hτ hτT B Y) (derivativePath τ hτ hτT B Y)
    (velocityPath_orbit τ hτ hτT B Y) (derivativePath_orbit τ hτ hτT B Y)

theorem potentialPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (potentialPath τ hτ hτT B Y))
      (potentialTimePath τ hτ hτT B Y t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderPotential.potentialPath_hasDerivWithinAt P D.T D.T_pos.le
    D.potentialCoefficientPath D.potentialDerivative (velocityPath τ hτ hτT B Y) (derivativePath τ
      hτ hτT B Y)
    D.potentialCoefficientPath_time (velocityPath_time τ hτ hτT B Y) t

def correctorPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.path P D.FInv.field (potentialPath τ hτ hτT B Y)

def correctorTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.derivative P D.T D.FInv.field D.inverseDerivative
    (potentialPath τ hτ hτT B Y) (potentialTimePath τ hτ hτT B Y)

theorem correctorPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (correctorPath τ hτ hτT B
  Y)) :=
  EulerCylinderSlowCurl.path_orbit P D.FInv.field D.FInv.translation_contDiff
    (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y)

theorem correctorTimePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (correctorTimePath τ hτ
  hτT B Y)) :=
  EulerCylinderSlowCurl.derivative_orbit P D.T D.FInv.field D.inverseDerivative
    D.FInv.translation_contDiff D.inverseDerivative_orbit
    (potentialPath τ hτ hτT B Y) (potentialTimePath τ hτ hτT B Y)
    (potentialPath_orbit τ hτ hτT B Y) (potentialTimePath_orbit τ hτ hτT B Y)

theorem correctorPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (correctorPath τ hτ hτT B Y))
      (correctorTimePath τ hτ hτT B Y t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderSlowCurl.path_hasDerivWithinAt P D.T D.T_pos.le D.FInv.field D.inverseDerivative
    (potentialPath τ hτ hτT B Y) (potentialTimePath τ hτ hτT B Y)
    (potentialPath_orbit τ hτ hτT B Y) (potentialTimePath_orbit τ hτ hτT B Y)
    D.inverse_hasDerivWithinAt (potentialPath_time τ hτ hτT B Y) t

def corrector : VectorField := fun z =>
  pointField P (correctorPath τ hτ hτT B Y) (correctorPath_orbit τ hτ hτT B Y)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

def correctorDerivative : VectorField := fun z =>
  pointField P (correctorTimePath τ hτ hτT B Y) (correctorTimePath_orbit τ hτ hτT B Y)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

theorem velocityPath_raw_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, pointField P (velocityPath τ hτ hτT B Y)
      (velocityPath_orbit τ hτ hτT B Y) t (x,(θ : AddCircle P))) = 0 := by
  simpa only [vector,Data.clamp_coe] using vector_mean_zero τ hτ hτT B Y t x

theorem rawPotential_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.rawPotential P (vector τ hτ hτT B Y) (t,(x,θ)) =
      pointField P (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y) t (x,(θ :
        AddCircle P)) := by
  have he : (fun s : ℝ => vector τ hτ hτT B Y (t,(x,s))) = fun s : ℝ =>
      pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t (x,(s :
        AddCircle P)) :=
    funext (fun s => (vectorField τ hτ hτT B Y).raw_eq t x s)
  rw [Data.rawPotential,Data.clamp_coe,he]
  exact (EulerCylinderPotential.potentialField_source_formula P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y)
    (velocityPath_raw_mean_zero τ hτ hτT B Y) (fun t x => D.normal.field t x)
    (potentialCoefficient_apply D.normal D.normalLower D.normalLower_pos D.normal_lower) t x θ).symm

theorem corrector_formula (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    corrector τ hτ hτT B Y (t,(x,θ)) =
      EulerMeanBoundary.curlMatrix
        ((EulerLiftedWeakDerivative.fieldFDeriv P
          (pointField P (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y) t) (x,(θ :
            AddCircle P))).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field t x))) := by
  change EulerCylinderSlowCurl.field P D.FInv.field D.FInv.translation_contDiff
    (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y) (D.clamp t) (x,(θ : AddCircle
      P)) = _
  rw [Data.clamp_coe]
  exact EulerCylinderSlowCurl.field_formula P D.FInv.field D.FInv.translation_contDiff
    (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y) t (x,(θ : AddCircle P))

theorem curlCorrector_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.curlCorrector P (vector τ hτ hτT B Y) (t,(x,θ)) = corrector τ hτ hτT B Y (t,(x,θ)) := by
  have he : (fun y : LiftTangent => D.rawPotential P (vector τ hτ hτT B Y) (t,y)) =
      fun y : LiftTangent => pointField P (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ
        hτT B Y)
        t (y.1,(y.2 : AddCircle P)) := funext (fun y => rawPotential_eq τ hτ hτT B Y t y.1 y.2)
  rw [Data.curlCorrector,Data.clamp_coe,he,coverField_fderiv,corrector_formula τ hτ hτT B Y t x θ]

def correctorField : Field P D.T (D.curlCorrector P (vector τ hτ hτT B Y)) where
  path := correctorPath τ hτ hτT B Y
  orbit := correctorPath_orbit τ hτ hτT B Y
  raw_eq t x θ := (curlCorrector_eq τ hτ hτT B Y t x θ).trans (by simp only
    [corrector,Data.clamp_coe])

def correctorDerivativeField : Field P D.T (correctorDerivative τ hτ hτT B Y) where
  path := correctorTimePath τ hτ hτT B Y
  orbit := correctorTimePath_orbit τ hτ hτT B Y
  raw_eq t x θ := by simp only [correctorDerivative,Data.clamp_coe]

theorem correctorField_time : TimeDerivative D.T_pos.le
    (correctorField τ hτ hτT B Y) (correctorDerivativeField τ hτ hτT B Y) :=
  correctorPath_time τ hτ hτT B Y

end EulerTransversePacketPrimary

namespace EulerTransversePacketPrimary

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerCylinderLocalSupport
  EulerCylinderAngleAverage EulerCylinderCorrectorMeanZero EulerPacketProfileRecursion
  EulerTransversePacketProvider EulerElapsedTimePathGluing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)

theorem potentialPath_supported (t : Icc (0 : ℝ) D.T) :
    potentialPath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable :=
  EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
    (velocityPath τ hτ hτT B Y) D.potentialCoefficientPath (velocityPath_supported τ hτ hτT B Y) t

theorem potentialTimePath_supported (t : Icc (0 : ℝ) D.T) :
    potentialTimePath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable := by
  apply (Supported P Space D.support D.support_measurable).add_mem
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (velocityPath τ hτ hτT B Y) D.potentialDerivative (velocityPath_supported τ hτ hτT B Y) t
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (derivativePath τ hτ hτT B Y) D.potentialCoefficientPath (derivativePath_supported τ hτ hτT B
        Y) t

theorem correctorPath_supported (t : Icc (0 : ℝ) D.T) :
    correctorPath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable :=
  slowCurlPath_supported P D.support D.support_measurable (potentialPath τ hτ hτT B Y)
    (potentialPath_orbit τ hτ hτT B Y) D.FInv.field D.support_compact.isClosed
    (potentialPath_supported τ hτ hτT B Y) t

theorem correctorTimePath_supported (t : Icc (0 : ℝ) D.T) :
    correctorTimePath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable := by
  apply (Supported P Space D.support D.support_measurable).add_mem
  · exact slowCurlPath_supported P D.support D.support_measurable (potentialPath τ hτ hτT B Y)
      (potentialPath_orbit τ hτ hτT B Y) D.inverseDerivative D.support_compact.isClosed
      (potentialPath_supported τ hτ hτT B Y) t
  · exact slowCurlPath_supported P D.support D.support_measurable (potentialTimePath τ hτ hτT B Y)
      (potentialTimePath_orbit τ hτ hτT B Y) D.FInv.field D.support_compact.isClosed
      (potentialTimePath_supported τ hτ hτT B Y) t

theorem potentialPath_average_zero : pathAverage P (potentialPath τ hτ hτT B Y) = 0 :=
  potentialPath_mean_zero P (velocityPath τ hτ hτT B Y) D.potentialCoefficientPath
    (ContinuousMap.ext (velocityPath_mean_zero τ hτ hτT B Y))

theorem potentialTimePath_average_zero : pathAverage P (potentialTimePath τ hτ hτT B Y) = 0 := by
  rw [potentialTimePath,EulerCylinderPotential.potentialDerivative,map_add,
    potentialPath_mean_zero P (velocityPath τ hτ hτT B Y) D.potentialDerivative
      (ContinuousMap.ext (velocityPath_mean_zero τ hτ hτT B Y)),
    potentialPath_mean_zero P (derivativePath τ hτ hτT B Y) D.potentialCoefficientPath
      (ContinuousMap.ext (derivativePath_mean_zero τ hτ hτT B Y)),add_zero]

theorem correctorPath_average_zero : pathAverage P (correctorPath τ hτ hτT B Y) = 0 :=
  slowCurl_mean_zero P (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y)
    D.FInv.field (potentialPath_average_zero τ hτ hτT B Y)

theorem correctorTimePath_average_zero : pathAverage P (correctorTimePath τ hτ hτT B Y) = 0 := by
  rw [correctorTimePath,EulerCylinderSlowCurl.derivative,map_add,
    slowCurl_mean_zero P (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y)
      D.inverseDerivative (potentialPath_average_zero τ hτ hτT B Y),
    slowCurl_mean_zero P (potentialTimePath τ hτ hτT B Y) (potentialTimePath_orbit τ hτ hτT B Y)
      D.FInv.field (potentialTimePath_average_zero τ hτ hτT B Y),add_zero]

theorem corrector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    corrector τ hτ hτT B Y (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (correctorPath τ hτ hτT B Y)
    (correctorPath_orbit τ hτ hτT B Y) D.support_compact.isClosed
    (correctorPath_supported τ hτ hτT B Y) (D.clamp t) (x,(θ : AddCircle P)) hx

theorem correctorDerivative_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    correctorDerivative τ hτ hτT B Y (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (correctorTimePath τ hτ hτT B Y)
    (correctorTimePath_orbit τ hτ hτT B Y) D.support_compact.isClosed
    (correctorTimePath_supported τ hτ hτT B Y) (D.clamp t) (x,(θ : AddCircle P)) hx

theorem curlCorrector_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, D.curlCorrector P (vector τ hτ hτT B Y) (t,(x,θ))) = 0 := by
  have he : (fun θ => D.curlCorrector P (vector τ hτ hτT B Y) (t,(x,θ))) =
      fun θ => corrector τ hτ hτT B Y (t,(x,θ)) := funext (curlCorrector_eq τ hτ hτT B Y t x)
  rw [he]
  exact (pathAverage_eq_zero_iff P (correctorPath τ hτ hτT B Y) (correctorPath_orbit τ hτ hτT B
    Y)).mp
    (correctorPath_average_zero τ hτ hτT B Y) (D.clamp t) x

end EulerTransversePacketPrimary


namespace EulerTransversePacketPrimary

open Set EulerSmoothLimit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerTransversePacketProvider EulerPacketCylinderField EulerCylinderFieldReflection

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))

include hSym hF hM hH hY

theorem curlCorrector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.curlCorrector P (vector τ hτ hτT B Y) (t,(-x,-θ)) =
      -D.curlCorrector P (vector τ hτ hτT B Y) (t,(x,θ)) := by
  apply D.curlCorrector_odd P (vector τ hτ hτT B Y) t
  · simpa only [Data.clamp_coe] using D.inverse_even hF t
  · exact (vectorField τ hτ hτT B Y).raw_smooth t
  · exact vector_periodic τ hτ hτT B Y t
  · exact vector_mean_zero τ hτ hτT B Y t
  · exact vector_odd τ hτ hτT B Y hSym hF hM hH hY t

theorem correctorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    correctorDerivative τ hτ hτT B Y (t,(-x,-θ)) =
      -correctorDerivative τ hτ hτT B Y (t,(x,θ)) :=
  (correctorField τ hτ hτT B Y).timeDerivative_odd (correctorDerivativeField τ hτ hτT B Y)
    D.T_pos (correctorField_time τ hτ hτT B Y)
    (curlCorrector_odd τ hτ hτT B Y hSym hF hM hH hY) t x θ

end EulerTransversePacketPrimary
