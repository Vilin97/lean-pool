/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointCoordinates
import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointStrong
import LeanPool.NavierStokesAndEuler.Euler.FrameEndpointUniqueness
import LeanPool.NavierStokesAndEuler.Euler.TimeH1ContinuousDerivative

/-!
The constructed affine-terminal inverse as a classical coordinate path,
and its uniqueness among actual twice differentiable coordinate paths.
-/

@[expose] public section


noncomputable section

namespace EulerFixedEndpointClassical

open Set MeasureTheory ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseEndpointCoordinates
  EulerTransverseEndpointParameter EulerTransverseFixedEndpoint
  EulerTransverseForwardInverse EulerTransverseGramInverse
  EulerTransverseEndpointVelocity EulerTimeH1FrameTransport

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t v, ⟪H t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

/-- Displacement, given by `(initialPrimitive T hT).comp (coordinateSlope T hT Q Q₁ H c hc hQ hd
K hK hH hsmall)`. -/
def displacement : U →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  (initialPrimitive T hT).comp (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

/-- Acceleration as an element of `U →L[ℝ] C(Icc (0 : ℝ) T,U)`. -/
def acceleration : U →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  (EulerContinuousTimeIntegral.multiplier (generator T Q Q₁ c hc hQ)).comp
    (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

theorem displacement_initial (Y : U) :
    displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y ⟨0,le_rfl,hT⟩ = 0 :=
  initialPrimitive_initial T hT _

theorem displacement_terminal (hTpos : 0 < T) (Y : U) :
    displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y ⟨T,hT,le_rfl⟩ = Y := by
  let r := fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    (affineTrial T hT Q Q₁) Y
  have hr : initialTrace T hT (r : TimeLp T U) = 0 := r.property
  change initialPrimitive T hT (constantFieldOperator T hT (T⁻¹ • Y)-(r : TimeLp T U)) _ = Y
  rw [map_sub,ContinuousMap.sub_apply,initialPrimitive_constantFieldOperator,
    initialPrimitive_eq_terminal_sub,terminalPrimitive_terminal]
  change T • (T⁻¹ • Y)-(0-initialTrace T hT (r : TimeLp T U)) = Y
  rw [hr,sub_self,sub_zero,smul_smul,mul_inv_cancel₀ hTpos.ne',one_smul]

variable (Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (hTpos : 0 < T)
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))

include Q₂ hTpos hd₁ hframe in
theorem velocity_ae (Y : U) :
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y : ℝ → U) =ᵐ[timeMeasure T]
      extendPath T hT (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y) := by
  have ha := EulerFixedEndpointStrong.coordinateSlope_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      hTpos Y
  filter_upwards [ha,ae_restrict_mem measurableSet_Icc] with t ht hm
  rw [ht]
  change _ = continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y (projIcc 0 T hT t)
  rw [projIcc_of_mem hT hm]
  exact (EulerFixedEndpointStrong.continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH
    hsmall Q₂ hTpos hd₁ hframe Y ⟨t,hm⟩).symm

include Q₂ hTpos hd₁ hframe in
theorem displacement_hasDerivWithinAt (Y : U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y))
      (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t)
      (Icc (0 : ℝ) T) t := by
  have hh := EulerTimeH1ContinuousDerivative.hasDerivWithinAt_of_continuous_representative
    T hT (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (velocity_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y)
    (initialRealPrimitive T (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y))
    (initialRealPrimitive_absolutelyContinuous T _) (initialRealPrimitive_hasDerivAt_ae T _) t
  apply hh.congr_of_mem _ t.property
  intro s hs
  change initialRealPrimitive T _ (projIcc 0 T hT s) = initialRealPrimitive T _ s
  rw [projIcc_of_mem hT hs]
  rfl

include Q₂ hTpos hd₁ hframe in
theorem velocity_hasDerivWithinAt (Y : U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (extendPath T hT (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y))
      (acceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t) (Icc (0 : ℝ) T) t :=
  EulerFixedEndpointStrong.continuousCoordinateVelocity_hasDerivWithinAt_generator
    T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y t

theorem projected_equation (Y : U) (t : Icc (0 : ℝ) T) :
    gram (Q t) (acceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t) =
      (Q t).adjoint ((-2 : ℝ) • Q₁ t
        (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t)) := by
  change gram (Q t) ((-2 : ℝ) • gramInverse (Q t) c hc (hQ t) ((Q t).adjoint
    (Q₁ t (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t)))) = _
  rw [map_smul,gram_inverse_apply,map_smul]

include Q₂ hTpos hd₁ hframe in
theorem unique (Y : U) (z v a : C(Icc (0 : ℝ) T, U))
    (hz : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT z) (v t) (Icc (0 : ℝ) T) t)
    (hv : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT v) (a t) (Icc (0 : ℝ) T) t)
    (hz0 : z ⟨0,le_rfl,hT⟩ = 0) (hzT : z ⟨T,hT,le_rfl⟩ = Y)
    (heq : ∀ t, gram (Q t) (a t) = (Q t).adjoint ((-2 : ℝ) • Q₁ t (v t))) :
    z = displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y ∧
    v = continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y := by
  apply EulerFrameEndpointUniqueness.unique_of_projected_equation T hT hTpos
    Q Q₁ Q₂ H c hc hQ hd hd₁ hframe K hK hH hsmall z v a
    (displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (acceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y) hz hv
    (displacement_hasDerivWithinAt T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y)
    (velocity_hasDerivWithinAt T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y)
    (hz0.trans (displacement_initial T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y).symm)
    (hzT.trans (displacement_terminal T hT Q Q₁ H c hc hQ hd K hK hH hsmall hTpos Y).symm)
    heq (projected_equation T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)

end EulerFixedEndpointClassical
