/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialPath
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeGradient
import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity

/-! Genuine time derivatives of the constructed vector potential and its slow curl. -/

section

/-! Actual one-sided time differentiation of the packet's spatial curl corrector. -/

@[expose] public section

noncomputable section

namespace EulerPacketPiola

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerVolterraConvolution EulerLiftedWeakDerivative EulerMeanBoundary
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hd

/-- The two product-rule terms are derived from the genuine L² evolution and actual inverse frame
derivative. -/
theorem matrixSlowCurl_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P)
    (G : ℝ → Space →L[ℝ] Space) (G₁ : Space →L[ℝ] Space)
    (hG : HasDerivWithinAt G G₁ (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt
      (fun r => curlMatrix ((fieldFDeriv P (pointField P p hp (projIcc 0 T hT r)) x).comp
        ((ContinuousLinearMap.inl ℝ Space ℝ).comp (G r))))
      (curlMatrix ((fieldFDeriv P (pointField P f hf t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp (G t))) +
        curlMatrix ((fieldFDeriv P (pointField P p hp t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁)))
      (Icc (0 : ℝ) T) t := by
  have hL : HasDerivWithinAt (fun r => (ContinuousLinearMap.inl ℝ Space ℝ).comp (G r))
      ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁) (Icc (0 : ℝ) T) t := by
    have h := ((hasDerivAt_const (t : ℝ) (ContinuousLinearMap.inl ℝ Space
        ℝ)).hasDerivWithinAt).clm_comp hG
    simpa only [ContinuousLinearMap.zero_comp, zero_add] using h
  have hD := pointField_fderiv_hasDerivWithinAt P T hT p f hp hf hd t x
  have h := curlOperator.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hD.clm_comp hL)
  simpa only [Function.comp_def, map_add, curlOperator_apply, projIcc_of_mem hT t.property] using h

/-- This is the literal lifted curl in the Piola packet construction, including both time endpoints.
-/
theorem liftedSlowCurl_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P)
    (F : ℝ → Space → Space ≃L[ℝ] Space) (G₁ : Space →L[ℝ] Space)
    (hG : HasDerivWithinAt (fun r => (F r x.1).symm.toContinuousLinearMap) G₁
      (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt
      (fun r => liftedSlowCurl P (F r) (pointField P p hp (projIcc 0 T hT r)) x)
      (liftedSlowCurl P (F t) (pointField P f hf t) x +
        curlMatrix ((fieldFDeriv P (pointField P p hp t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁)))
      (Icc (0 : ℝ) T) t :=
  matrixSlowCurl_hasDerivWithinAt P T hT p f hp hf hd t x
    (fun r => (F r x.1).symm.toContinuousLinearMap) G₁ hG

end EulerPacketPiola

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderPotential

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedWeakDerivative EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderAnglePrimitive
  EulerMeanCoefficients EulerVolterraConvolution EulerMeanBoundary EulerPacketPiola
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (T : ℝ) (hT : 0 ≤ T)
  (B B₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (hB₁ : ContDiff ℝ ∞ (translateCoefficientPath B₁))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))

/-- Potential derivative, given by `potentialPath P B₁ p + potentialPath P B f`. -/
def potentialDerivative : C(Icc (0 : ℝ) T,LiftL2 P) :=
  potentialPath P B₁ p + potentialPath P B f

include hB hB₁ hp hf in
theorem potentialDerivative_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (potentialDerivative P T B B₁ p f)) := by
  simp only [potentialDerivative, map_add]
  exact (potentialPath_orbit P B₁ hB₁ p hp).add (potentialPath_orbit P B hB f hf)

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPotentialTime1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPotentialTime2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderPotentialTime3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderPotentialTime4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

variable
  (hBt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath T hT B s x)
      (extendPath T hT B₁ t x) (Icc (0 : ℝ) T) t)
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hBt hd

theorem potentialPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (potentialPath P B p))
      (potentialDerivative P T B B₁ p f t) (Icc (0 : ℝ) T) t :=
  fullProduct_hasDerivWithinAt P T hT B B₁ hBt (pathPrimitive P p) (pathPrimitive P f)
    (pathPrimitive_time_derivative P T hT p f hd) t

theorem potentialField_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    HasDerivWithinAt (fun r => potentialField P B hB p hp (projIcc 0 T hT r) x)
      (pointField P (potentialDerivative P T B B₁ p f)
        (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf) t x) (Icc (0 : ℝ) T) t :=
  pointField_hasDerivWithinAt P T hT (potentialPath P B p) (potentialDerivative P T B B₁ p f)
    (potentialPath_orbit P B hB p hp) (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf)
    (potentialPath_hasDerivWithinAt P T hT B B₁ p f hBt hd) t x

/-- The actual curl derivative is obtained from the constructed potential, not assumed as a profile
jet. -/
theorem potentialCurl_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P)
    (F : ℝ → Space → Space ≃L[ℝ] Space) (G₁ : Space →L[ℝ] Space)
    (hG : HasDerivWithinAt (fun r => (F r x.1).symm.toContinuousLinearMap) G₁
      (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt
      (fun r => liftedSlowCurl P (F r) (potentialField P B hB p hp (projIcc 0 T hT r)) x)
      (liftedSlowCurl P (F t)
          (pointField P (potentialDerivative P T B B₁ p f)
            (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf) t) x +
        curlMatrix ((fieldFDeriv P (potentialField P B hB p hp t) x).comp
          ((ContinuousLinearMap.inl ℝ Space ℝ).comp G₁)))
      (Icc (0 : ℝ) T) t :=
  liftedSlowCurl_hasDerivWithinAt P T hT (potentialPath P B p) (potentialDerivative P T B B₁ p f)
    (potentialPath_orbit P B hB p hp) (potentialDerivative_orbit P T B B₁ hB hB₁ p f hp hf)
    (potentialPath_hasDerivWithinAt P T hT B B₁ p f hBt hd) t x F G₁ hG

end EulerCylinderPotential
