/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeGradient
import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity

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
