/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGeneratorDifference
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1GeneratorBounds

@[expose] public section

/-!
Polynomial uniform-time bounds and neighboring-label estimates for the
actual primary history.  The terminal coordinate is the same at both labels.
`historyVelocity_eq` identifies the bounded path here with the genuine
coordinate velocity of the stationary endpoint solution.
-/

noncomputable section


namespace EulerTransverseHistoryBounds

open Set ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerInitialTimePrimitive EulerVolterraConvolution
  EulerTimeH1FrameTransport EulerTransverseInitialInverse
  EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint EulerTransverseEndpointParameter
  EulerTransverseEndpointBounds EulerTransverseEndpointDifference
  EulerTransverseEndpointCoordinates EulerTransverseGeneratorDifference
  EulerTransverseForwardInverse EulerTimeH1GeneratorBounds EulerContinuousTimeIntegral

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

def slopeCost (T d a r : ℝ) : ℝ := r * (1+d^2*(2*r^2)*a) * (affineCost T*d)

def slopeDifferenceCost (T d a r δd δa : ℝ) : ℝ :=
  r * (affineCost T * endpointDifferenceCost d (2*r^2) a δd δa + δd * slopeCost T d a r)

theorem coordinateSlope_norm_le (d a r : ℝ)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hA : 1 + T ^ 2 * ‖H‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) :
    ‖coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall‖ ≤ slopeCost T d a r := by
  have hd0 : 0 ≤ d := (show 0 ≤ T*‖Q₁‖+‖Q‖ by positivity).trans hD
  have ha0 : 0 ≤ a := (show 0 ≤ 1+T^2*‖H‖ by positivity).trans hA
  have hr0 := (transportCost_pos T hT Q Q₁ c hc).le.trans hr
  apply opNorm_le_bound _ (by unfold slopeCost affineCost; positivity)
  intro ξ
  have hinv := norm_le_initialProductDerivative T hT Q Q₁ c hc hQ hd
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ)
  rw [coordinateSlope_product T hT Q Q₁ H c hc hQ hd K hK hH hsmall] at hinv
  have he := (le_opNorm
    (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall (affineTrial T hT Q Q₁)) ξ).trans
      (mul_le_mul_of_nonneg_right
        (fixedAffineEndpoint_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall d a r hD hA hr)
        (norm_nonneg ξ))
  exact hinv.trans ((mul_le_mul hr he (norm_nonneg _) hr0).trans_eq (by unfold slopeCost; ring))

variable (P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (G : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (hP : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖P t v‖ ^ 2)
  (hp : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT P) (P₁ t) (Icc (0 : ℝ) T) t)
  (hG : ∀ t v, ⟪G t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)

theorem coordinateSlope_sub_norm_le (d a r : ℝ)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r) :
    ‖coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall -
      coordinateSlope T hT P P₁ G c hc hP hp K hK hG hsmall‖ ≤
      slopeDifferenceCost T d a r (derivativeDistance T Q Q₁ P P₁) (T^2*‖H-G‖) := by
  have hd0 : 0 ≤ d := (show 0 ≤ T*‖Q₁‖+‖Q‖ by positivity).trans hD
  have ha0 : 0 ≤ a := (show 0 ≤ 1+T^2*‖H‖ by positivity).trans hA
  have hr0 := (transportCost_pos T hT Q Q₁ c hc).le.trans hr
  have hδd := derivativeDistance_nonneg T hT Q Q₁ P P₁
  apply opNorm_le_bound _ (by
    unfold slopeDifferenceCost slopeCost endpointDifferenceCost affineCost
    positivity)
  intro ξ
  have hinv := norm_sub_le_initialProductDerivative T hT Q Q₁ c hc hQ hd P P₁
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall ξ)
    (coordinateSlope T hT P P₁ G c hc hP hp K hK hG hsmall ξ)
  rw [coordinateSlope_product T hT Q Q₁ H c hc hQ hd K hK hH hsmall,
    coordinateSlope_product T hT P P₁ G c hc hP hp K hK hG hsmall] at hinv
  have hδend := fixedAffineEndpoint_sub_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    P P₁ G hP hp hG d a r hD hD' hA hA' hr hr'
  have hend := (le_opNorm
    (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall (affineTrial T hT Q Q₁) -
     fixedEndpointDerivative T hT P P₁ G c hc hP hp K hK hG hsmall (affineTrial T hT P P₁)) ξ).trans
    (mul_le_mul_of_nonneg_right hδend (norm_nonneg ξ))
  have hprev := (le_opNorm (coordinateSlope T hT P P₁ G c hc hP hp K hK hG hsmall) ξ).trans
    (mul_le_mul_of_nonneg_right
      (coordinateSlope_norm_le T hT P P₁ G c hc hP hp K hK hG hsmall d a r hD' hA' hr')
        (norm_nonneg ξ))
  have hright := add_le_add hend (mul_le_mul_of_nonneg_left hprev hδd)
  exact hinv.trans ((mul_le_mul hr hright (by positivity) hr0).trans_eq
    (by unfold slopeDifferenceCost derivativeDistance; ring))

def historyCost (T c q q₁ d a r : ℝ) : ℝ :=
  q * traceCost T (2*c⁻¹*q*q₁) * slopeCost T d a r

def historyDifferenceCost (T c q q₁ d a r δq δq₁ δH : ℝ) : ℝ :=
  δq * traceCost T (2*c⁻¹*q*q₁) * slopeCost T d a r +
    q * (2*(1+T)*generatorDifferenceCost c q q₁ δq δq₁*slopeCost T d a r +
      traceCost T (2*c⁻¹*q*q₁)*slopeDifferenceCost T d a r (T*δq₁+δq) (T^2*δH))

theorem historyVelocity_norm_le (hTpos : 0 < T) (q q₁ d a r : ℝ)
    (hQn : ‖Q‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ q₁)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hA : 1 + T ^ 2 * ‖H‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) :
    ‖historyVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall‖ ≤ historyCost T c q q₁ d a r := by
  exact transportedTrace_norm_le T hT hTpos Q (generator T Q Q₁ c hc hQ)
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
    q (2*c⁻¹*q*q₁) (slopeCost T d a r) hQn
    (generator_norm_le T Q Q₁ c hc hQ q q₁ hQn hQ₁n)
    (coordinateSlope_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall d a r hD hA hr)

/-- The primary history has a polynomial, uniform-in-time coefficient
sensitivity.  In particular coefficient Lipschitz bounds give the source's
physical-label Lipschitz bound with the same fixed terminal coordinate. -/
theorem historyVelocity_sub_norm_le (hTpos : 0 < T) (q q₁ d a r : ℝ)
    (hQn : ‖Q‖ ≤ q) (hPn : ‖P‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ q₁) (hP₁n : ‖P₁‖ ≤ q₁)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r) :
    ‖historyVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall -
      historyVelocity T hT P P₁ G c hc hP hp K hK hG hsmall‖ ≤
      historyDifferenceCost T c q q₁ d a r ‖Q-P‖ ‖Q₁-P₁‖ ‖H-G‖ := by
  exact transportedTrace_sub_norm_le T hT hTpos Q P
    (generator T Q Q₁ c hc hQ) (generator T P P₁ c hc hP)
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
    (coordinateSlope T hT P P₁ G c hc hP hp K hK hG hsmall)
    q (2*c⁻¹*q*q₁) (slopeCost T d a r) ‖Q-P‖
    (generatorDifferenceCost c q q₁ ‖Q-P‖ ‖Q₁-P₁‖)
    (slopeDifferenceCost T d a r (derivativeDistance T Q Q₁ P P₁) (T^2*‖H-G‖))
    hPn (generator_norm_le T Q Q₁ c hc hQ q q₁ hQn hQ₁n)
    (generator_norm_le T P P₁ c hc hP q q₁ hPn hP₁n)
    (coordinateSlope_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall d a r hD hA hr)
    le_rfl (generator_sub_norm_le T Q Q₁ P P₁ c hc hQ hP q q₁ hQn hPn hQ₁n hP₁n)
    (coordinateSlope_sub_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      P P₁ G hP hp hG d a r hD hD' hA hA' hr hr')

end EulerTransverseHistoryBounds
