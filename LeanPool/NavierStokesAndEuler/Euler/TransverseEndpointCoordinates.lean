/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1Reconstruction
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointParameter
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointVelocity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardInverse
import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEquation
import LeanPool.NavierStokesAndEuler.Euler.TransverseInitialInverse

/-!
The coordinate derivative and its continuous history representative for the
actual nonzero-terminal endpoint solution.  The coordinate derivative is the
explicit affine constant minus the same fixed-space variational correction.
Equation (10), already proved for that solution, provides its genuine time
derivative; the bounded H¹ reconstruction recovers the actual history path.
-/

@[expose] public section


noncomputable section


namespace EulerTransverseEndpointCoordinates

open Set MeasureTheory ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseInitialCoordinates
  EulerTransverseInitialInverse EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerTransverseEndpointParameter
  EulerTransverseEndpointMomentum EulerTransverseMomentumRegularity
  EulerTransverseEndpointVelocity EulerTransverseEndpointEquation
  EulerTransverseForwardInverse EulerTimeH1Reconstruction EulerContinuousTimeIntegral

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t v, ⟪H t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

/-- The actual derivative of the fixed terminal-coordinate solution. -/
def coordinateSlope : U →L[ℝ] TimeLp T U :=
  (constantFieldOperator T hT).comp (T⁻¹ • ContinuousLinearMap.id ℝ U) -
    (zeroTraceDerivatives (U := U) T hT).subtypeL.comp
      (fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall (affineTrial T hT Q Q₁))

theorem coordinateSlope_product (ξ : U) :
    initialProductDerivative T hT Q Q₁
      (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ) =
        fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
          (affineTrial T hT Q Q₁) ξ := by
  let r := fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall (affineTrial T hT Q Q₁) ξ
  have hr : initialTrace T hT (r : TimeLp T U) = 0 := r.property
  change initialProductDerivative T hT Q Q₁
    (constantFieldOperator T hT (T⁻¹ • ξ) - (r : TimeLp T U)) = _
  rw [map_sub, initialProductDerivative_eq_product_of_trace_zero T hT Q Q₁ _ hr]
  rfl

theorem coordinateSlope_derivative (ξ : U) :
    initialCoordinateDerivative T hT Q Q₁ c hc hQ
      (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
        (affineTrial T hT Q Q₁) ξ) =
      coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ := by
  rw [← coordinateSlope_product T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ]
  exact initialCoordinateOperator_product T hT Q Q₁ c hc hQ hd _

variable (m : Icc (0 : ℝ) T → E) (hm : ∀ t v, ⟪m t, Q t v⟫_ℝ = 0)
  (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ v : U, Q t v = η)

include hm hRange in
theorem coordinateSlope_physical_derivative (ξ : U) :
    initialCoordinateDerivative T hT Q Q₁ c hc hQ
      (endpointDerivative T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) ξ) =
      coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ := by
  rw [← fixedEndpointDerivative_eq_endpoint T hT Q Q₁ H c hc hQ hd K hK hH hsmall m hm hRange]
  exact coordinateSlope_derivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ

include hm hRange in
theorem coordinateSlope_ae (hTpos : 0 < T) (ξ : U) :
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ : ℝ → U) =ᵐ[timeMeasure T]
      coordinateVelocityPath T hT Q Q₁ c hc hQ H
        (endpointDerivative T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) ξ) := by
  rw [← coordinateSlope_physical_derivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall m hm hRange ξ]
  apply coordinateVelocityPath_ae T hT Q Q₁ c hc hQ H hd hTpos
  · exact initialMomentum_weak T hT Q Q₁ H hd m hm _
      (endpointDerivative_weak T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) ξ)
  · intro t
    exact hRange t _ (endpointDisplacement_tangent T hT m H K hK hH hsmall _
      (affineTrial_tangent T hT Q Q₁ hd m hm) ξ t)

/-- The literal right side of equation (10), in Bochner L². -/
def coordinateAcceleration : U →L[ℝ] TimeLp T U :=
  (timeMultiplier T hT (generator T Q Q₁ c hc hQ)).comp
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

/-- Bounded time reconstruction of the actual coordinate history. -/
def continuousCoordinateVelocity : U →L[ℝ] C(Icc (0 : ℝ) T, U) :=
  (valuePart T hT).comp (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall) +
    (derivativePart T hT).comp (coordinateAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

/-- The source history velocity `Q ξ_t` with the fixed terminal coordinate. -/
def historyVelocity : U →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  (multiplier Q).comp (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

section Regularity

variable (Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (hTpos : 0 < T)
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))

include hm hRange hd₁ hframe hTpos in
theorem coordinateSlope_h1 (ξ : U) :
    let v := coordinateVelocityPath T hT Q Q₁ c hc hQ H
      (endpointDerivative T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) ξ)
    AbsolutelyContinuousOnInterval v 0 T ∧
      (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ : ℝ → U) =ᵐ[timeMeasure T] v ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt v (coordinateAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t) t := by
  dsimp only
  let u := endpointDerivative T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) ξ
  let v := coordinateVelocityPath T hT Q Q₁ c hc hQ H u
  have hv := coordinateVelocityPath_continuous T hT Q Q₁ c hc hQ H u
  let g : C(Icc (0 : ℝ) T, U) := ⟨fun t => generator T Q Q₁ c hc hQ t (v t),
    (generator T Q Q₁ c hc hQ).continuous.clm_apply (hv.comp continuous_subtype_val)⟩
  have hdv (t : Icc (0 : ℝ) T) : HasDerivWithinAt v (g t) (Icc (0 : ℝ) T) t :=
    (endpoint_coordinate_equation T hT Q Q₁ Q₂ c hc hQ H hTpos hd hd₁ hframe
      m hm hRange K hK hH hsmall _ (affineTrial_tangent T hT Q Q₁ hd m hm) ξ t).2
  have hcont : AbsolutelyContinuousOnInterval v 0 T := by
    have hl : LipschitzOnWith ‖g‖₊ v (Icc (0 : ℝ) T) := by
      apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (f' := extendPath T hT g)
      · intro t ht
        simpa only [extendPath, projIcc_of_mem hT ht] using hdv ⟨t, ht⟩
      · intro t ht
        exact g.norm_coe_le_norm (projIcc 0 T hT t)
    exact (show LipschitzOnWith ‖g‖₊ v (uIcc (0 : ℝ) T) by
      simpa only [uIcc_of_le hT] using hl).absolutelyContinuousOnInterval
  have hae := coordinateSlope_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall m hm hRange hTpos ξ
  refine ⟨hcont, hae, ?_⟩
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, hae, timeMultiplier_ae T hT (generator T Q Q₁ c hc hQ)
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ)] with t ht hs ha
  have hti : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  change HasDerivAt v (timeMultiplier T hT (generator T Q Q₁ c hc hQ)
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ) t) t
  rw [ha, hs]
  have hdt := (hdv ⟨t, hti⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  change HasDerivAt v (generator T Q Q₁ c hc hQ ⟨t, hti⟩ (v t)) t at hdt
  simpa only [extendPath, projIcc_of_mem hT hti] using hdt

include hm hRange hd₁ hframe hTpos in
/-- The bounded reconstruction is the actual classical coordinate velocity at
every time, so the history estimates concern the primary solution itself. -/
theorem continuousCoordinateVelocity_eq (ξ : U) (t : Icc (0 : ℝ) T) :
    continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t =
      coordinateVelocityPath T hT Q Q₁ c hc hQ H
        (endpointDerivative T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) ξ) t := by
  have hreg := coordinateSlope_h1 T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    m hm hRange Q₂ hTpos hd₁ hframe ξ
  exact reconstruction_eq_path T hTpos _ _ _ hreg.1 hreg.2.1 hreg.2.2 t

include hm hRange hd₁ hframe hTpos in
theorem historyVelocity_eq (ξ : U) (t : Icc (0 : ℝ) T) :
    historyVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t =
      Q t (coordinateVelocityPath T hT Q Q₁ c hc hQ H
        (endpointDerivative T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) ξ) t) := by
  change Q t (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t) = _
  rw [continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    m hm hRange Q₂ hTpos hd₁ hframe]

end Regularity

end EulerTransverseEndpointCoordinates
