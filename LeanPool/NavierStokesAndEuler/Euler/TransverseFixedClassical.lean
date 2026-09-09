/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedEvolution
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

@[expose] public section

/-!
# Classical time evolution for the fixed-coordinate Dirichlet solve

Continuous forcing gives a continuous Gram acceleration. The genuine H¹
velocity therefore has its actual derivative throughout the closed interval.
The displacement keeps both zero endpoint conditions.
-/

noncomputable section

namespace EulerTransverseFixedEvolution

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerTerminalTimePrimitive EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse EulerTransverseGramInverse
  EulerContinuousTimeIntegral EulerTimeH1ContinuousDerivative

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

def classicalAcceleration (f : C(Icc (0 : ℝ) T,E)) : C(Icc (0 : ℝ) T,U) :=
  EulerContinuousGramAcceleration.accelerationPath T Q Q₁ c hc hQ
    (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f)) f

def displacementPath (f : TimeLp T E) : C(Icc (0 : ℝ) T,U) :=
  terminalPrimitive T hT (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall f)

def physicalVelocityPath (f : C(Icc (0 : ℝ) T,E)) : C(Icc (0 : ℝ) T,E) :=
  multiplier Q (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f))

def physicalDerivativePath (f : C(Icc (0 : ℝ) T,E)) : C(Icc (0 : ℝ) T,E) :=
  multiplier Q₁ (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f))+
    multiplier Q (classicalAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall f)

theorem displacementPath_initial (f : TimeLp T E) :
    displacementPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f ⟨0,le_rfl,hT⟩ = 0 :=
  velocityLp_zero_trace T hT Q Q₁ H c hc hQ hd K hK hH hsmall f

theorem displacementPath_terminal (f : TimeLp T E) :
    displacementPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f ⟨T,hT,le_rfl⟩ = 0 :=
  terminalPrimitive_terminal T hT _

theorem classicalAcceleration_equation (f : C(Icc (0 : ℝ) T,E)) (t : Icc (0 : ℝ) T) :
    gram (Q t) (classicalAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t) =
      (Q t).adjoint (f t-(2 : ℝ) • Q₁ t
        (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f) t)) :=
  EulerContinuousGramAcceleration.accelerationPath_equation T Q Q₁ c hc hQ _ f t

variable (Q₂ : C(Icc (0 : ℝ) T,U →L[ℝ] E))
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
  (hTpos : 0 < T)

include hd₁ hframe hTpos in
theorem classicalAcceleration_ae (f : C(Icc (0 : ℝ) T,E)) :
    (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f) : ℝ → U) =ᵐ[timeMeasure T]
      extendPath T hT (classicalAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) :=
  EulerContinuousGramAcceleration.accelerationPath_ae T Q Q₁ c hc hQ hT
    (velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f))
    (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f))
    (pathLp T hT f) (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f)) f
    (velocityPath_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hd₁ hframe hTpos _)
    (pathLp_ae T hT f) (accelerationLp_equation T hT Q Q₁ H c hc hQ hd K hK hH hsmall _)

include hd₁ hframe hTpos in
/-- The actual coordinate history has the genuine time derivative in (10),
including within-interval derivatives at both endpoints. -/
theorem velocityPath_hasDerivWithinAt (f : C(Icc (0 : ℝ) T,E)) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT
      (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f)))
      (classicalAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t) (Icc (0 : ℝ) T) t := by
  obtain ⟨v,hv,hrep,hder⟩ := velocityLp_h1 T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    Q₂ hd₁ hframe hTpos (pathLp T hT f)
  have hdv := hasDerivWithinAt_of_continuous_representative T hT
    (accelerationLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f))
    (classicalAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall f)
    (classicalAcceleration_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hd₁ hframe hTpos f)
    v hv hder t
  apply hdv.congr_of_mem _ t.property
  intro s hs
  change velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f) (projIcc 0 T hT s) = v s
  rw [projIcc_of_mem hT hs]
  exact velocityPath_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall hTpos _ v hv hrep hder ⟨s,hs⟩

include hd₁ hframe hTpos in
theorem displacementPath_hasDerivWithinAt (f : C(Icc (0 : ℝ) T,E)) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT
      (displacementPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f)))
      (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f) t) (Icc (0 : ℝ) T) t := by
  let w := velocityLp T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f)
  have hdr := hasDerivWithinAt_of_continuous_representative T hT w
    (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f))
    (velocityPath_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hd₁ hframe hTpos _)
    (realPrimitive T w) (realPrimitive_absolutelyContinuous T w)
    (realPrimitive_hasDerivAt_ae T w) t
  apply hdr.congr_of_mem _ t.property
  intro s hs
  change realPrimitive T w (projIcc 0 T hT s) = realPrimitive T w s
  rw [projIcc_of_mem hT hs]

include hd₁ hframe hTpos in
theorem physicalVelocityPath_hasDerivWithinAt (f : C(Icc (0 : ℝ) T,E)) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT
      (physicalVelocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f))
      (physicalDerivativePath T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t) (Icc (0 : ℝ) T) t := by
  have h := (hd t).clm_apply
    (velocityPath_hasDerivWithinAt T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hd₁ hframe hTpos f t)
  change HasDerivWithinAt
    (fun s => extendPath T hT Q s
      (extendPath T hT (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f)) s))
    (Q₁ t (velocityPath T hT Q Q₁ H c hc hQ hd K hK hH hsmall (pathLp T hT f) t)+
      Q t (classicalAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall f t)) (Icc (0 : ℝ) T) t
  simpa only [extendPath,projIcc_of_mem hT t.property] using h

end EulerTransverseFixedEvolution
