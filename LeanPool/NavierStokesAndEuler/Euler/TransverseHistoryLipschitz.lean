/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryBounds

@[expose] public section

/-! The explicit history perturbation estimate yields actual coefficient Lipschitz control. -/

noncomputable section


namespace EulerTransverseHistoryBounds

open Set ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerVolterraConvolution EulerTimeH1FrameTransport
  EulerTransverseEndpointCoordinates EulerTransverseEndpointDifference
  EulerTransverseEndpointBounds EulerTransverseGeneratorDifference EulerTimeH1GeneratorBounds

theorem historyDifferenceCost_linear (T c q q₁ d a r x y z : ℝ) :
    historyDifferenceCost T c q q₁ d a r x y z =
      historyDifferenceCost T c q q₁ d a r 1 0 0 * x +
      historyDifferenceCost T c q q₁ d a r 0 1 0 * y +
      historyDifferenceCost T c q q₁ d a r 0 0 1 * z := by
  unfold historyDifferenceCost slopeDifferenceCost slopeCost endpointDifferenceCost
    generatorDifferenceCost traceCost
  ring

theorem historyDifferenceCost_nonneg (T c q q₁ d a r x y z : ℝ)
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hq : 0 ≤ q) (hq₁ : 0 ≤ q₁)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ historyDifferenceCost T c q q₁ d a r x y z := by
  unfold historyDifferenceCost slopeDifferenceCost slopeCost endpointDifferenceCost
    generatorDifferenceCost traceCost affineCost
  positivity

theorem historyDifferenceCost_le_scale (T c q q₁ d a r x y z L₀ L₁ LH s : ℝ)
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hq : 0 ≤ q) (hq₁ : 0 ≤ q₁)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : x ≤ L₀*s) (hy : y ≤ L₁*s) (hz : z ≤ LH*s) :
    historyDifferenceCost T c q q₁ d a r x y z ≤
      historyDifferenceCost T c q q₁ d a r L₀ L₁ LH * s := by
  have h₀ := historyDifferenceCost_nonneg T c q q₁ d a r 1 0 0 hT hc hq hq₁ hd ha hr
    zero_le_one le_rfl le_rfl
  have h₁ := historyDifferenceCost_nonneg T c q q₁ d a r 0 1 0 hT hc hq hq₁ hd ha hr
    le_rfl zero_le_one le_rfl
  have hH := historyDifferenceCost_nonneg T c q q₁ d a r 0 0 1 hT hc hq hq₁ hd ha hr
    le_rfl le_rfl zero_le_one
  rw [historyDifferenceCost_linear T c q q₁ d a r x y z]
  exact (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx h₀)
    (mul_le_mul_of_nonneg_left hy h₁)) (mul_le_mul_of_nonneg_left hz hH)).trans_eq
      (by rw [historyDifferenceCost_linear T c q q₁ d a r L₀ L₁ LH]; ring)

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
  (P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (G : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (hP : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖P t v‖ ^ 2)
  (hp : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT P) (P₁ t) (Icc (0 : ℝ) T) t)
  (hG : ∀ t v, ⟪G t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)

/-- The actual history operator inherits a Lipschitz estimate from the given
coefficient paths, with an explicit polynomial coefficient. -/
theorem historyVelocity_sub_norm_le_of_coefficient_bounds (hTpos : 0 < T) (q q₁ d a r : ℝ)
    (hQn : ‖Q‖ ≤ q) (hPn : ‖P‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ q₁) (hP₁n : ‖P₁‖ ≤ q₁)
    (hD : T * ‖Q₁‖ + ‖Q‖ ≤ d) (hD' : T * ‖P₁‖ + ‖P‖ ≤ d)
    (hA : 1 + T ^ 2 * ‖H‖ ≤ a) (hA' : 1 + T ^ 2 * ‖G‖ ≤ a)
    (hr : transportCost T Q Q₁ c ≤ r) (hr' : transportCost T P P₁ c ≤ r)
    (L₀ L₁ LH s : ℝ) (h₀ : ‖Q-P‖ ≤ L₀*s) (h₁ : ‖Q₁-P₁‖ ≤ L₁*s) (hHdiff : ‖H-G‖ ≤ LH*s) :
    ‖historyVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall -
      historyVelocity T hT P P₁ G c hc hP hp K hK hG hsmall‖ ≤
      historyDifferenceCost T c q q₁ d a r L₀ L₁ LH * s := by
  apply (historyVelocity_sub_norm_le T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    P P₁ G hP hp hG hTpos q q₁ d a r hQn hPn hQ₁n hP₁n hD hD' hA hA' hr hr').trans
  exact historyDifferenceCost_le_scale T c q q₁ d a r ‖Q-P‖ ‖Q₁-P₁‖ ‖H-G‖ L₀ L₁ LH s
    hT hc.le ((show 0 ≤ ‖Q‖ by positivity).trans hQn) ((show 0 ≤ ‖Q₁‖ by positivity).trans hQ₁n)
    ((show 0 ≤ T*‖Q₁‖+‖Q‖ by positivity).trans hD)
    ((show 0 ≤ 1+T^2*‖H‖ by positivity).trans hA)
    ((transportCost_pos T hT Q Q₁ c hc).le.trans hr) h₀ h₁ hHdiff

end EulerTransverseHistoryBounds
