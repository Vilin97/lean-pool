/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointCoordinates
import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEquation

/-!
The actual affine-terminal fixed-coordinate variational solution satisfies
the source homogeneous coordinate equation.  The range condition follows
from its explicit coordinate primitive.  No ambient normal, nor a supplied
weak equation or smooth representative, is an input to these results.
-/

@[expose] public section


noncomputable section


namespace EulerFixedEndpointStrong

open Set MeasureTheory ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseInitialCoordinates
   EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerTransverseFixedSpaceInverse EulerTransverseEndpointParameter
  EulerTransverseEndpointMomentum EulerTransverseMomentumRegularity
  EulerTransverseEndpointVelocity EulerTransverseEndpointDifferentiation
  EulerTransverseEndpointEquation EulerTransverseEndpointCoordinates
  EulerTransverseForwardInverse EulerTimeH1Reconstruction EulerContinuousTimeIntegral
  EulerLinearDuhamel

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

/-- The constructed fixed-coordinate endpoint inverse obeys the literal
weak momentum identity, for every trial lift. -/
theorem fixedEndpointDerivative_weak
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V →L[ℝ] TimeLp T E) (Y : V)
    (v : TimeLp T U) (hv : initialTrace T hT v = 0) :
    let u := fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y
    ⟪momentum T hT Q u, v⟫_ℝ =
      -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ := by
  dsimp only
  have ht := fixedEndpointDerivative_orthogonal T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y ⟨v, hv⟩
  rw [energyOperator_inner,
    initialPrimitiveTimeLp_eq_primitive_of_trace_zero T hT _
      (fixedFrameDerivative_trace_zero T hT Q Q₁ hd ⟨v, hv⟩)] at ht
  change ⟪fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y,
      productDerivative T hT Q Q₁ v⟫_ℝ -
    ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT
      (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y)),
      primitiveTimeLp T hT (productDerivative T hT Q Q₁ v)⟫_ℝ = 0 at ht
  rw [primitiveTimeLp_productDerivative T hT Q Q₁ hd] at ht
  simp only [productDerivative, add_apply, comp_apply, inner_add_right] at ht
  simp only [momentum, initialMomentumForcing, sub_apply, comp_apply,
    inner_sub_left, adjoint_inner_left]
  linarith only [ht]

/-- The affine fixed-coordinate solution lies in the actual frame range
at every time, including the two endpoints. -/
theorem coordinateSlope_range (ξ : U) (t : Icc (0 : ℝ) T) :
    ∃ x : U, Q t x = initialRealPrimitive T
      (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
        (affineTrial T hT Q Q₁) ξ) t := by
  rw [← coordinateSlope_product T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ]
  exact ⟨initialPrimitive T hT (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ) t,
    (initialPrimitive_initialProductDerivative T hT Q Q₁ hd _ t).symm⟩

/-- The continuous momentum reconstruction represents the explicit
coordinate derivative of the fixed affine-terminal solution. -/
theorem coordinateSlope_ae (hTpos : 0 < T) (ξ : U) :
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ : ℝ → U) =ᵐ[timeMeasure T]
      coordinateVelocityPath T hT Q Q₁ c hc hQ H
        (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
          (affineTrial T hT Q Q₁) ξ) := by
  rw [← coordinateSlope_derivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ]
  exact coordinateVelocityPath_ae T hT Q Q₁ c hc hQ H hd hTpos _
    (fixedEndpointDerivative_weak T hT Q Q₁ H c hc hQ hd K hK hH hsmall _ ξ)
    (coordinateSlope_range T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ)

section Regularity

variable (Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (hTpos : 0 < T)
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))

include hd₁ hframe hTpos in
/-- Equation (10) for the constructed affine-terminal fixed-space inverse. -/
theorem coordinate_equation (ξ : U) (t : Icc (0 : ℝ) T) :
    let u := fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      (affineTrial T hT Q Q₁) ξ
    HasDerivWithinAt (initialCoordinates T hT Q c hc hQ u)
        (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t) (Icc (0 : ℝ) T) t ∧
      HasDerivWithinAt (coordinateVelocityPath T hT Q Q₁ c hc hQ H u)
        (generator T Q Q₁ c hc hQ t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t))
        (Icc (0 : ℝ) T) t := by
  dsimp only
  have hw := fixedEndpointDerivative_weak T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    (affineTrial T hT Q Q₁) ξ
  have hr := coordinateSlope_range T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ
  exact ⟨initialCoordinates_hasDerivWithinAt T hT Q Q₁ c hc hQ H hTpos hd _ hw hr t,
    coordinateVelocityPath_hasDerivWithinAt_generator T hT Q Q₁ Q₂ c hc hQ H
      hTpos hd hd₁ hframe _ hw hr t⟩

include hd₁ hframe hTpos in
theorem coordinateSlope_h1 (ξ : U) :
    let v := coordinateVelocityPath T hT Q Q₁ c hc hQ H
      (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
        (affineTrial T hT Q Q₁) ξ)
    AbsolutelyContinuousOnInterval v 0 T ∧
      (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ : ℝ → U) =ᵐ[timeMeasure T] v ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt v (coordinateAcceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t) t := by
  dsimp only
  let u := fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    (affineTrial T hT Q Q₁) ξ
  let v := coordinateVelocityPath T hT Q Q₁ c hc hQ H u
  have hv := coordinateVelocityPath_continuous T hT Q Q₁ c hc hQ H u
  let g : C(Icc (0 : ℝ) T, U) := ⟨fun t => generator T Q Q₁ c hc hQ t (v t),
    (generator T Q Q₁ c hc hQ).continuous.clm_apply (hv.comp continuous_subtype_val)⟩
  have hdv (t : Icc (0 : ℝ) T) : HasDerivWithinAt v (g t) (Icc (0 : ℝ) T) t :=
    (coordinate_equation T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe ξ t).2
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
  have hae := coordinateSlope_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall hTpos ξ
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

include hd₁ hframe hTpos in
/-- The existing bounded reconstruction is this actual stationary coordinate
velocity at every time. -/
theorem continuousCoordinateVelocity_eq (ξ : U) (t : Icc (0 : ℝ) T) :
    continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t =
      coordinateVelocityPath T hT Q Q₁ c hc hQ H
        (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
          (affineTrial T hT Q Q₁) ξ) t := by
  have hreg := coordinateSlope_h1 T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe ξ
  exact reconstruction_eq_path T hTpos _ _ _ hreg.1 hreg.2.1 hreg.2.2 t

include hd₁ hframe hTpos in
theorem historyVelocity_eq (ξ : U) (t : Icc (0 : ℝ) T) :
    historyVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t =
      Q t (coordinateVelocityPath T hT Q Q₁ c hc hQ H
        (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
          (affineTrial T hT Q Q₁) ξ) t) := by
  change Q t (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t) = _
  rw [continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe]

include hd₁ hframe hTpos in
theorem continuousCoordinateVelocity_hasDerivWithinAt_generator (ξ : U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (extendPath T hT (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ))
      (generator T Q Q₁ c hc hQ t
        (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t))
      (Icc (0 : ℝ) T) t := by
  have hv := (coordinate_equation T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe ξ t).2
  rw [← continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe ξ
      t] at hv
  apply hv.congr_of_mem _ t.property
  intro s hs
  simpa only [extendPath, projIcc_of_mem hT hs] using
    continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe ξ ⟨s,
        hs⟩

include hd₁ hframe hTpos in
/-- The affine-terminal coordinate history coincides with the actual
homogeneous forward solver with its own initial velocity. -/
theorem continuousCoordinateVelocity_eq_forward
    (evolution : Evolution T hT (generator T Q Q₁ c hc hQ))
    (ξ : U) (t : Icc (0 : ℝ) T) :
    continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ t =
      coordinates T hT Q Q₁ c hc hQ evolution 0
        (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ ⟨0, le_rfl, hT⟩) t :=
            by
  rw [continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe ξ t,
    continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe ξ ⟨0,
        le_rfl, hT⟩]
  exact coordinateVelocity_eq_forward T hT Q Q₁ Q₂ c hc hQ H hTpos hd hd₁ hframe _
    (fixedEndpointDerivative_weak T hT Q Q₁ H c hc hQ hd K hK hH hsmall _ ξ)
    (coordinateSlope_range T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ) evolution t

end Regularity

end EulerFixedEndpointStrong
