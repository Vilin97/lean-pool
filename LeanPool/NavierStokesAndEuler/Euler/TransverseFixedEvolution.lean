/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedStrong
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramInverse
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1Reconstruction
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousGramAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1ContinuousDerivative

@[expose] public section

/-!
# Continuous coordinate velocity of the actual fixed Dirichlet inverse

The acceleration is constructed by the true Gram inverse. The weak solve
proves it is the derivative of the solved coordinate velocity; bounded H¹
reconstruction then supplies the actual continuous history path.
-/

noncomputable section

namespace EulerTransverseFixedEvolution

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerTerminalTimePrimitive EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse EulerTransverseFixedStrong
  EulerTransverseCoordinateRegularity EulerTransverseMomentumRegularity
  EulerTransverseStrongEquation EulerTransverseGramInverse EulerTransverseGramPath
  EulerTimeLpGramInverse EulerTimeH1Reconstruction

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T,U →L[ℝ] E)) (H : C(Icc (0 : ℝ) T,E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t v, ⟪H t v,v⟫_ℝ ≤ K*‖v‖^2)
  (hsmall : K*(T^2/2) ≤ 1/2)

def velocityLp : TimeLp T E →L[ℝ] TimeLp T U :=
  (zeroTraceDerivatives (U := U) T hT).subtypeL.comp
    (fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

def accelerationLp : TimeLp T E →L[ℝ] TimeLp T U :=
  (gramSolver T hT Q c hc hQ).comp ((timeMultiplier T hT Q).adjoint.comp
    (ContinuousLinearMap.id ℝ (TimeLp T E)-(2 : ℝ) • (timeMultiplier T hT Q₁).comp
      (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall)))

def velocityPath : TimeLp T E →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  (valuePart T hT).comp (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall)+
    (derivativePart T hT).comp (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

theorem velocityLp_zero_trace (f : TimeLp T E) :
    initialTrace T hT (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) = 0 :=
  (fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f).property

theorem accelerationLp_ae (f : TimeLp T E) :
    (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f : ℝ → U) =ᵐ[timeMeasure T]
      fun t => gramInverse (Q (projIcc 0 T hT t)) c hc (hQ (projIcc 0 T hT t))
        ((Q (projIcc 0 T hT t)).adjoint (f t-(2 : ℝ) • Q₁ (projIcc 0 T hT t)
          (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t))) := by
  let v := velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f
  let w := f-(2 : ℝ) • timeMultiplier T hT Q₁ v
  change (gramSolver T hT Q c hc hQ ((timeMultiplier T hT Q).adjoint w) : ℝ → U) =ᵐ[timeMeasure T] _
  rw [gramSolver_eq_multiplier]
  filter_upwards [timeMultiplier_ae T hT (gramInversePath T Q c hc hQ)
      ((timeMultiplier T hT Q).adjoint w), momentum_ae T hT Q w,
    Lp.coeFn_sub f ((2 : ℝ) • timeMultiplier T hT Q₁ v),
    Lp.coeFn_smul (2 : ℝ) (timeMultiplier T hT Q₁ v),timeMultiplier_ae T hT Q₁ v]
      with t ha hm hw hs hv
  change w t = _ at hw
  change ((timeMultiplier T hT Q).adjoint w) t = _ at hm
  rw [ha,hm,hw,Pi.sub_apply,hs,Pi.smul_apply,hv]
  rfl

theorem accelerationLp_equation (f : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T,
      gram (extendPath T hT Q t) (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t) =
        (extendPath T hT Q t).adjoint (f t-(2 : ℝ) • extendPath T hT Q₁ t
          (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t)) := by
  filter_upwards [accelerationLp_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall f] with t ht
  change gram (Q (projIcc 0 T hT t)) _ = _
  rw [ht]
  exact gram_inverse_apply _ c hc (hQ (projIcc 0 T hT t)) _

variable (Q₂ : C(Icc (0 : ℝ) T,U →L[ℝ] E))
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))

include hd₁ hframe in
theorem velocityLp_h1 (hTpos : 0 < T) (f : TimeLp T E) :
    ∃ v : ℝ → U, AbsolutelyContinuousOnInterval v 0 T ∧
      (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f : ℝ → U) =ᵐ[timeMeasure T] v ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt v (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t) t := by
  obtain ⟨v,hv,hrep,hder,heq⟩ := EulerTransverseFixedStrong.exists_strong T hT Q Q₁ H c hc hQ
    hd K hK hH hsmall Q₂ hd₁ hframe hTpos f
  refine ⟨v,hv,hrep,?_⟩
  filter_upwards [hder,heq,hrep,accelerationLp_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall f]
    with t hdt het hvt hat
  dsimp only [extendPath] at het
  have hi := congrArg (gramInverse (Q (projIcc 0 T hT t)) c hc (hQ (projIcc 0 T hT t))) het
  rw [inverse_gram_apply] at hi
  change (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) t = v t at hvt
  rw [← hvt,← hat] at hi
  rw [← hi]
  exact hdt

theorem velocityPath_eq (hTpos : 0 < T) (f : TimeLp T E) (v : ℝ → U)
    (hv : AbsolutelyContinuousOnInterval v 0 T)
    (hrep : (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f : ℝ → U) =ᵐ[timeMeasure T] v)
    (hder : ∀ᵐ t ∂timeMeasure T,
      HasDerivAt v (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t) t)
    (t : Icc (0 : ℝ) T) :
    velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t = v t :=
  reconstruction_eq_path T hTpos _ _ v hv hrep hder t

include hd₁ hframe in
theorem velocityPath_ae (hTpos : 0 < T) (f : TimeLp T E) :
    (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f : ℝ → U) =ᵐ[timeMeasure T]
      extendPath T hT (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) := by
  obtain ⟨v,hv,hrep,hder⟩ := velocityLp_h1 T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hd₁ hframe
    hTpos f
  filter_upwards [hrep,ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht]
  change v t = velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f (projIcc 0 T hT t)
  rw [projIcc_of_mem hT hmem]
  exact (velocityPath_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall hTpos f v hv hrep hder ⟨t,hmem⟩).symm

end EulerTransverseFixedEvolution
