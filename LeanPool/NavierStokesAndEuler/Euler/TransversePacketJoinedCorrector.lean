/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator

@[expose] public section

/-!
# The literal corrector of the joined high solution

The actual global velocity and its true time derivative construct Q, Q_t,
C and C_t. The returned Field is for the literal raw curlCorrector used by
the recursion, including at the history/forward junction.
-/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
    EulerSourcePotentialCoefficient
  EulerPacketProfileRecursion EulerVolterraConvolution EulerMetricTransport
  EulerTransversePacketProvider EulerPacketCylinderField
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

def potentialPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialPath P D.potentialCoefficientPath (velocityPath τ hτ hτT B G)

def potentialTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialDerivative P D.T D.potentialCoefficientPath D.potentialDerivative
    (velocityPath τ hτ hτT B G) (derivativePath τ hτ hτT B G)

theorem potentialPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (potentialPath τ hτ hτT B
  G)) :=
  EulerCylinderPotential.potentialPath_orbit P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit
    (velocityPath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)

theorem potentialTimePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (potentialTimePath τ hτ
  hτT B G)) :=
  EulerCylinderPotential.potentialDerivative_orbit P D.T D.potentialCoefficientPath
    D.potentialDerivative
    D.potentialCoefficientPath_orbit D.potentialDerivative_orbit
    (velocityPath τ hτ hτT B G) (derivativePath τ hτ hτT B G)
    (velocityPath_orbit τ hτ hτT B G) (derivativePath_orbit τ hτ hτT B G)

theorem potentialPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (potentialPath τ hτ hτT B G))
      (potentialTimePath τ hτ hτT B G t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderPotential.potentialPath_hasDerivWithinAt P D.T D.T_pos.le
    D.potentialCoefficientPath D.potentialDerivative (velocityPath τ hτ hτT B G) (derivativePath τ
      hτ hτT B G)
    D.potentialCoefficientPath_time (velocityPath_time τ hτ hτT B G) t

def correctorPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.path P D.FInv.field (potentialPath τ hτ hτT B G)

def correctorTimePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.derivative P D.T D.FInv.field D.inverseDerivative
    (potentialPath τ hτ hτT B G) (potentialTimePath τ hτ hτT B G)

theorem correctorPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (correctorPath τ hτ hτT B
  G)) :=
  EulerCylinderSlowCurl.path_orbit P D.FInv.field D.FInv.translation_contDiff
    (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G)

theorem correctorTimePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (correctorTimePath τ hτ
  hτT B G)) :=
  EulerCylinderSlowCurl.derivative_orbit P D.T D.FInv.field D.inverseDerivative
    D.FInv.translation_contDiff D.inverseDerivative_orbit
    (potentialPath τ hτ hτT B G) (potentialTimePath τ hτ hτT B G)
    (potentialPath_orbit τ hτ hτT B G) (potentialTimePath_orbit τ hτ hτT B G)

theorem correctorPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (correctorPath τ hτ hτT B G))
      (correctorTimePath τ hτ hτT B G t) (Icc (0 : ℝ) D.T) t :=
  EulerCylinderSlowCurl.path_hasDerivWithinAt P D.T D.T_pos.le D.FInv.field D.inverseDerivative
    (potentialPath τ hτ hτT B G) (potentialTimePath τ hτ hτT B G)
    (potentialPath_orbit τ hτ hτT B G) (potentialTimePath_orbit τ hτ hτT B G)
    D.inverse_hasDerivWithinAt (potentialPath_time τ hτ hτT B G) t

def corrector : VectorField := fun z =>
  pointField P (correctorPath τ hτ hτT B G) (correctorPath_orbit τ hτ hτT B G)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

def correctorDerivative : VectorField := fun z =>
  pointField P (correctorTimePath τ hτ hτT B G) (correctorTimePath_orbit τ hτ hτT B G)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))

theorem velocityPath_raw_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, pointField P (velocityPath τ hτ hτT B G)
      (velocityPath_orbit τ hτ hτT B G) t (x,(θ : AddCircle P))) = 0 := by
  simpa only [vector,Data.clamp_coe] using vector_mean_zero τ hτ hτT B G t x

theorem rawPotential_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.rawPotential P (vector τ hτ hτT B G) (t,(x,θ)) =
      pointField P (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G) t (x,(θ :
        AddCircle P)) := by
  have he : (fun s : ℝ => vector τ hτ hτT B G (t,(x,s))) = fun s : ℝ =>
      pointField P (velocityPath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G) t (x,(s :
        AddCircle P)) :=
    funext (fun s => (vectorField τ hτ hτT B G).raw_eq t x s)
  rw [Data.rawPotential,Data.clamp_coe,he]
  exact (EulerCylinderPotential.potentialField_source_formula P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit (velocityPath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
    (velocityPath_raw_mean_zero τ hτ hτT B G) (fun t x => D.normal.field t x)
    (potentialCoefficient_apply D.normal D.normalLower D.normalLower_pos D.normal_lower) t x θ).symm

theorem corrector_formula (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    corrector τ hτ hτT B G (t,(x,θ)) =
      EulerMeanBoundary.curlMatrix
        ((EulerLiftedWeakDerivative.fieldFDeriv P
          (pointField P (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G) t) (x,(θ :
            AddCircle P))).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field t x))) := by
  change EulerCylinderSlowCurl.field P D.FInv.field D.FInv.translation_contDiff
    (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G) (D.clamp t) (x,(θ : AddCircle
      P)) = _
  rw [Data.clamp_coe]
  exact EulerCylinderSlowCurl.field_formula P D.FInv.field D.FInv.translation_contDiff
    (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G) t (x,(θ : AddCircle P))

theorem curlCorrector_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.curlCorrector P (vector τ hτ hτT B G) (t,(x,θ)) = corrector τ hτ hτT B G (t,(x,θ)) := by
  have he : (fun y : LiftTangent => D.rawPotential P (vector τ hτ hτT B G) (t,y)) =
      fun y : LiftTangent => pointField P (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ
        hτT B G)
        t (y.1,(y.2 : AddCircle P)) := funext (fun y => rawPotential_eq τ hτ hτT B G t y.1 y.2)
  rw [Data.curlCorrector,Data.clamp_coe,he,coverField_fderiv,corrector_formula τ hτ hτT B G t x θ]

def correctorField : Field P D.T (D.curlCorrector P (vector τ hτ hτT B G)) where
  path := correctorPath τ hτ hτT B G
  orbit := correctorPath_orbit τ hτ hτT B G
  raw_eq t x θ := (curlCorrector_eq τ hτ hτT B G t x θ).trans (by simp only
    [corrector,Data.clamp_coe])

def correctorDerivativeField : Field P D.T (correctorDerivative τ hτ hτT B G) where
  path := correctorTimePath τ hτ hτT B G
  orbit := correctorTimePath_orbit τ hτ hτT B G
  raw_eq t x θ := by simp only [correctorDerivative,Data.clamp_coe]

theorem correctorField_time : TimeDerivative D.T_pos.le
    (correctorField τ hτ hτT B G) (correctorDerivativeField τ hτ hτT B G) :=
  correctorPath_time τ hτ hτT B G

end EulerTransversePacketJoin
