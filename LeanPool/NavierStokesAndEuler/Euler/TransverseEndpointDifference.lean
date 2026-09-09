/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointBounds

@[expose] public section

/-!
The neighboring-label estimate for the actual nonzero-terminal inverse.
The inverse is the same coercive inverse as the packet construction.  All
constants below bound coefficients or their explicit frame-transport cost;
no bound on an unknown inverse or on a supplied solution is assumed.
-/

noncomputable section


namespace EulerTransverseEndpointDifference

open Set ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1FrameTransport
  EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey
  EulerTransverseVariationalInverse EulerTransverseFixedSpaceInverse
  EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerTransverseEndpointParameter EulerTransverseEndpointBounds
  EulerCoerciveProjection EulerCoerciveEndpointBounds

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

/-- An abbreviation of the actual fixed-coordinate inverse, with its proved coercivity. -/
def fixedInverse : zeroTraceDerivatives (U := U) T hT →L[ℝ] zeroTraceDerivatives (U := U) T hT :=
  coerciveInverse (fixedFrameOperator T hT Q Q₁ H) (fixedCoercivity T Q Q₁ c)
    (fixedCoercivity_pos T hT Q Q₁ c hc)
    (fixedFrameOperator_coercive T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

theorem fixedInverse_norm_le (r : ℝ) (hr : transportCost T Q Q₁ c ≤ r) :
    ‖fixedInverse T hT Q Q₁ H c hc hQ hd K hK hH hsmall‖ ≤ 2 * r ^ 2 := by
  apply (coerciveInverse_norm_le _ _ _ _).trans
  have he : (fixedCoercivity T Q Q₁ c)⁻¹ = 2 * (transportCost T Q Q₁ c) ^ 2 := by
    simp only [fixedCoercivity, inv_div, inv_pow, div_inv_eq_mul]
  rw [he]
  have hp := (transportCost_pos T hT Q Q₁ c hc).le
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hp (hp.trans hr)).2 hr) (by norm_num)

variable (P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (G : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (hP : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖P t v‖ ^ 2)
  (hp : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT P) (P₁ t) (Icc (0 : ℝ) T) t)
  (hG : ∀ t v, ⟪G t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)

/-- The literal coefficient distance for differentiating moving-frame paths. -/
def derivativeDistance : ℝ := T * ‖Q₁-P₁‖ + ‖Q-P‖

omit [CompleteSpace U] [CompleteSpace E] in
include hT in
theorem derivativeDistance_nonneg : 0 ≤ derivativeDistance T Q Q₁ P P₁ := by
  unfold derivativeDistance
  positivity

theorem fixedFrameOperator_sub_norm_le (d a : ℝ)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a) :
    ‖fixedFrameOperator T hT Q Q₁ H - fixedFrameOperator T hT P P₁ G‖ ≤
      2 * d * a * derivativeDistance T Q Q₁ P P₁ + d ^ 2 * (T ^ 2 * ‖H-G‖) :=
  formOperator_sub_norm_le _ _ _ _ d a _ _
    ((fixedFrameDerivative_norm_le T hT Q Q₁).trans hD)
    ((fixedFrameDerivative_norm_le T hT P P₁).trans hD')
    ((dirichlet_norm_le T hT _ (primitive_norm_le_time T hT) H).trans hA)
    ((dirichlet_norm_le T hT _ (primitive_norm_le_time T hT) G).trans hA')
    (fixedFrameDerivative_sub_norm_le T hT Q Q₁ P P₁)
    (dirichlet_sub_norm_le T hT _ (primitive_norm_le_time T hT) H G)

theorem fixedInverse_sub_norm_le (d a r : ℝ)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r) :
    ‖fixedInverse T hT Q Q₁ H c hc hQ hd K hK hH hsmall -
      fixedInverse T hT P P₁ G c hc hP hp K hK hG hsmall‖ ≤
      (2 * r ^ 2) ^ 2 *
        (2 * d * a * derivativeDistance T Q Q₁ P P₁ + d ^ 2 * (T ^ 2 * ‖H-G‖)) := by
  let R := fixedInverse T hT Q Q₁ H c hc hQ hd K hK hH hsmall
  let S := fixedInverse T hT P P₁ G c hc hP hp K hK hG hsmall
  let A := fixedFrameOperator T hT Q Q₁ H
  let B := fixedFrameOperator T hT P P₁ G
  have hres : R-S = R.comp ((B-A).comp S) :=
    coerciveInverse_resolvent _ _ _ _ _ _ _ _
  have hR : ‖R‖ ≤ 2*r^2 := fixedInverse_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall r hr
  have hS : ‖S‖ ≤ 2*r^2 := fixedInverse_norm_le T hT P P₁ G c hc hP hp K hK hG hsmall r hr'
  have hAB : ‖B-A‖ ≤ 2*d*a*derivativeDistance T Q Q₁ P P₁ + d^2*(T^2*‖H-G‖) := by
    exact (norm_sub_rev B A).trans_le
      (fixedFrameOperator_sub_norm_le T hT Q Q₁ H P P₁ G d a hD hD' hA hA')
  have hAB0 := (show 0 ≤ ‖B-A‖ by positivity).trans hAB
  change ‖R-S‖ ≤ _
  rw [hres]
  apply ((opNorm_comp_le R ((B-A).comp S)).trans (mul_le_mul hR
    ((opNorm_comp_le (B-A) S).trans (mul_le_mul hAB hS (norm_nonneg S) hAB0))
      (norm_nonneg ((B-A).comp S)) (by positivity))).trans_eq
  ring

/-- The polynomial sensitivity of an affine terminal-coordinate solve. -/
def endpointDifferenceCost (d i a δd δa : ℝ) : ℝ :=
  (1 + 3 * d ^ 2 * i * a + 2 * d ^ 4 * i ^ 2 * a ^ 2) * δd +
    (d ^ 3 * i + d ^ 5 * i ^ 2 * a) * δa

theorem fixedAffineEndpoint_norm_le (d a r : ℝ)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hA : 1 + T ^ 2 * ‖H‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) :
    ‖fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      (affineTrial T hT Q Q₁)‖ ≤ (1+d^2*(2*r^2)*a) * (affineCost T*d) := by
  have hb : 0 ≤ affineCost T := by unfold affineCost; positivity
  exact EulerCoerciveEndpointBounds.endpointOperator_norm_le
    (fixedFrameDerivative T hT Q Q₁)
    (fixedInverse T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
    (energyOperator T hT H) (affineTrial T hT Q Q₁)
    d (2*r^2) a (affineCost T*d)
    ((fixedFrameDerivative_norm_le T hT Q Q₁).trans hD)
    (fixedInverse_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall r hr)
    ((energyOperator_norm_le T hT H).trans hA)
    ((affineTrial_norm_le T hT Q Q₁).trans (mul_le_mul_of_nonneg_left hD hb))

theorem fixedAffineEndpoint_sub_norm_le (d a r : ℝ)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r) :
    ‖fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
        (affineTrial T hT Q Q₁) -
      fixedEndpointDerivative T hT P P₁ G c hc hP hp K hK hG hsmall
        (affineTrial T hT P P₁)‖ ≤
      affineCost T * endpointDifferenceCost d (2*r^2) a
        (derivativeDistance T Q Q₁ P P₁) (T^2*‖H-G‖) := by
  have hB0 : 0 ≤ affineCost T := by unfold affineCost; positivity
  have h := EulerCoerciveEndpointBounds.endpointOperator_sub_norm_le
    (fixedFrameDerivative T hT Q Q₁) (fixedFrameDerivative T hT P P₁)
    (fixedInverse T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
    (fixedInverse T hT P P₁ G c hc hP hp K hK hG hsmall)
    (energyOperator T hT H) (energyOperator T hT G)
    (affineTrial T hT Q Q₁) (affineTrial T hT P P₁)
    d (2*r^2) a (affineCost T*d) (derivativeDistance T Q Q₁ P P₁)
    ((2*r^2)^2*(2*d*a*derivativeDistance T Q Q₁ P P₁+d^2*(T^2*‖H-G‖)))
    (T^2*‖H-G‖) (affineCost T*derivativeDistance T Q Q₁ P P₁)
    ((fixedFrameDerivative_norm_le T hT Q Q₁).trans hD)
    ((fixedFrameDerivative_norm_le T hT P P₁).trans hD')
    (fixedInverse_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall r hr)
    (fixedInverse_norm_le T hT P P₁ G c hc hP hp K hK hG hsmall r hr')
    ((energyOperator_norm_le T hT H).trans hA)
    ((energyOperator_norm_le T hT G).trans hA')
    ((affineTrial_norm_le T hT Q Q₁).trans (mul_le_mul_of_nonneg_left hD hB0))
    (fixedFrameDerivative_sub_norm_le T hT Q Q₁ P P₁)
    (fixedInverse_sub_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      P P₁ G hP hp hG d a r hD hD' hA hA' hr hr')
    (energyOperator_sub_norm_le T hT H G)
    (affineTrial_sub_norm_le T hT Q Q₁ P P₁)
  have he : EulerCoerciveEndpointBounds.endpointOperator
      (fixedFrameDerivative T hT Q Q₁)
      (fixedInverse T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
      (energyOperator T hT H) (affineTrial T hT Q Q₁) =
      fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall
        (affineTrial T hT Q Q₁) := by
    rfl
  have he' : EulerCoerciveEndpointBounds.endpointOperator
      (fixedFrameDerivative T hT P P₁)
      (fixedInverse T hT P P₁ G c hc hP hp K hK hG hsmall)
      (energyOperator T hT G) (affineTrial T hT P P₁) =
      fixedEndpointDerivative T hT P P₁ G c hc hP hp K hK hG hsmall
        (affineTrial T hT P P₁) := by
    rfl
  rw [he, he'] at h
  exact h.trans_eq (by unfold endpointDifferenceCost; ring)

variable (m n : Icc (0 : ℝ) T → E)
  (hm : ∀ t v, ⟪m t, Q t v⟫_ℝ = 0) (hn : ∀ t v, ⟪n t, P t v⟫_ℝ = 0)
  (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ v : U, Q t v = η)
  (hRange' : ∀ t η, ⟪n t, η⟫_ℝ = 0 → ∃ v : U, P t v = η)

include c hc hQ hd hP hp hm hn hRange hRange' in
/-- A genuine neighboring-label bound on the physical endpoint solutions. -/
theorem affineEndpoint_sub_norm_le (d a r : ℝ)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r) :
    ‖endpointDerivative T hT m H K hK hH hsmall (affineTrial T hT Q Q₁) -
      endpointDerivative T hT n G K hK hG hsmall (affineTrial T hT P P₁)‖ ≤
      affineCost T * endpointDifferenceCost d (2*r^2) a
        (derivativeDistance T Q Q₁ P P₁) (T^2*‖H-G‖) := by
  rw [← fixedEndpointDerivative_eq_endpoint T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    m hm hRange, ← fixedEndpointDerivative_eq_endpoint T hT P P₁ G c hc hP hp K hK hG hsmall
    n hn hRange']
  exact fixedAffineEndpoint_sub_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    P P₁ G hP hp hG d a r hD hD' hA hA' hr hr'

end EulerTransverseEndpointDifference
