/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointCoordinates
import LeanPool.NavierStokesAndEuler.Euler.TransverseInitialInverse
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1Reconstruction
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientMap
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardInverse
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Polynomial uniform-time bounds and neighboring-label estimates for the
actual primary history.  The terminal coordinate is the same at both labels.
`historyVelocity_eq` identifies the bounded path here with the genuine
coordinate velocity of the stationary endpoint solution.
-/

section

/-!
Quantitative operator algebra for the actual fixed-space endpoint solve.
The input called `R` below is an inverse operator; the transverse specialization
constructs it by coercivity and discharges all of its norm bounds.
-/

@[expose] public section

noncomputable section

namespace EulerCoerciveEndpointBounds

open ContinuousLinearMap

variable {S E V F G W : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Taking adjoints preserves the norm of an operator difference. -/
theorem norm_adjoint_sub (A B : S →L[ℝ] E) :
    ‖A.adjoint - B.adjoint‖ = ‖A - B‖ := by
  simpa only [dist_eq_norm] using
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := S) (F := E)).dist_map A B

theorem norm_comp_sub_le (A B : F →L[ℝ] G) (C D : W →L[ℝ] F) :
    ‖A.comp C - B.comp D‖ ≤ ‖A - B‖ * ‖C‖ + ‖B‖ * ‖C - D‖ := by
  have he : A.comp C - B.comp D = (A - B).comp C + B.comp (C - D) := by
    ext x
    simp only [comp_apply, sub_apply, add_apply, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))

/-- The actual algebraic stationary correction in a fixed coordinate space. -/
def correctionOperator (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  D.comp (R.comp (D.adjoint.comp A))

/-- Endpoint operator, given by `L - (correctionOperator D R A).comp L`. -/
def endpointOperator (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E)
    (L : V →L[ℝ] E) : V →L[ℝ] E := L - (correctionOperator D R A).comp L

theorem correctionOperator_norm_le (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E)
    (d r a : ℝ) (hd : ‖D‖ ≤ d) (hr : ‖R‖ ≤ r) (ha : ‖A‖ ≤ a) :
    ‖correctionOperator D R A‖ ≤ d ^ 2 * r * a := by
  have hd0 := (norm_nonneg D).trans hd
  have hr0 := (norm_nonneg R).trans hr
  have ha0 := (norm_nonneg A).trans ha
  have hDA : ‖D.adjoint.comp A‖ ≤ d * a := by
    apply (opNorm_comp_le _ _).trans
    simp only [LinearIsometryEquiv.norm_map]
    exact mul_le_mul hd ha (norm_nonneg _) hd0
  have hRDA : ‖R.comp (D.adjoint.comp A)‖ ≤ r * (d * a) :=
    (opNorm_comp_le _ _).trans (mul_le_mul hr hDA (norm_nonneg _) hr0)
  exact ((opNorm_comp_le _ _).trans
    (mul_le_mul hd hRDA (norm_nonneg _) hd0)).trans_eq (by ring)

theorem correctionOperator_sub_norm_le
    (D D' : S →L[ℝ] E) (R R' : S →L[ℝ] S) (A A' : E →L[ℝ] E)
    (d r a δd δr δa : ℝ)
    (hd : ‖D‖ ≤ d) (hd' : ‖D'‖ ≤ d) (hr : ‖R‖ ≤ r) (hr' : ‖R'‖ ≤ r)
    (ha : ‖A‖ ≤ a) (_ha' : ‖A'‖ ≤ a)
    (hδd : ‖D - D'‖ ≤ δd) (hδr : ‖R - R'‖ ≤ δr) (hδa : ‖A - A'‖ ≤ δa) :
    ‖correctionOperator D R A - correctionOperator D' R' A'‖ ≤
      2 * d * r * a * δd + d ^ 2 * a * δr + d ^ 2 * r * δa := by
  have hd0 := (norm_nonneg D).trans hd
  have hr0 := (norm_nonneg R).trans hr
  have ha0 := (norm_nonneg A).trans ha
  have hδd0 := (norm_nonneg (D-D')).trans hδd
  have hδr0 := (norm_nonneg (R-R')).trans hδr
  have hδa0 := (norm_nonneg (A-A')).trans hδa
  have hDA : ‖D.adjoint.comp A‖ ≤ d * a := by
    apply (opNorm_comp_le _ _).trans
    simp only [LinearIsometryEquiv.norm_map]
    exact mul_le_mul hd ha (norm_nonneg _) hd0
  have hDAδ : ‖D.adjoint.comp A - D'.adjoint.comp A'‖ ≤ δd * a + d * δa := by
    apply (norm_comp_sub_le _ _ _ _).trans
    have hh : ‖D.adjoint - D'.adjoint‖ = ‖D-D'‖ := norm_adjoint_sub D D'
    simp only [hh, LinearIsometryEquiv.norm_map]
    exact add_le_add (mul_le_mul hδd ha (norm_nonneg _) hδd0)
      (mul_le_mul hd' hδa (norm_nonneg _) hd0)
  have hRDA : ‖R.comp (D.adjoint.comp A)‖ ≤ r * (d * a) :=
    (opNorm_comp_le _ _).trans (mul_le_mul hr hDA (norm_nonneg _) hr0)
  have hRDAδ : ‖R.comp (D.adjoint.comp A) - R'.comp (D'.adjoint.comp A')‖ ≤
      δr * (d * a) + r * (δd * a + d * δa) := by
    apply (norm_comp_sub_le _ _ _ _).trans
    exact add_le_add (mul_le_mul hδr hDA (norm_nonneg _) hδr0)
      (mul_le_mul hr' hDAδ (norm_nonneg _) hr0)
  apply ((norm_comp_sub_le _ _ _ _).trans
    (add_le_add (mul_le_mul hδd hRDA (norm_nonneg _) hδd0)
      (mul_le_mul hd' hRDAδ (norm_nonneg _) hd0))).trans_eq
  ring

theorem endpointOperator_norm_le (D : S →L[ℝ] E) (R : S →L[ℝ] S) (A : E →L[ℝ] E)
    (L : V →L[ℝ] E) (d r a l : ℝ)
    (hd : ‖D‖ ≤ d) (hr : ‖R‖ ≤ r) (ha : ‖A‖ ≤ a) (hl : ‖L‖ ≤ l) :
    ‖endpointOperator D R A L‖ ≤ (1 + d ^ 2 * r * a) * l := by
  have hs := correctionOperator_norm_le D R A d r a hd hr ha
  have hs0 := (norm_nonneg _).trans hs
  apply ((norm_sub_le _ _).trans (add_le_add hl ((opNorm_comp_le _ _).trans
    (mul_le_mul hs hl (norm_nonneg _) hs0)))).trans_eq
  ring

theorem endpointOperator_sub_norm_le
    (D D' : S →L[ℝ] E) (R R' : S →L[ℝ] S) (A A' : E →L[ℝ] E)
    (L L' : V →L[ℝ] E) (d r a l δd δr δa δl : ℝ)
    (hd : ‖D‖ ≤ d) (hd' : ‖D'‖ ≤ d) (hr : ‖R‖ ≤ r) (hr' : ‖R'‖ ≤ r)
    (ha : ‖A‖ ≤ a) (ha' : ‖A'‖ ≤ a) (hl : ‖L‖ ≤ l)
    (hδd : ‖D - D'‖ ≤ δd) (hδr : ‖R - R'‖ ≤ δr)
    (hδa : ‖A - A'‖ ≤ δa) (hδl : ‖L - L'‖ ≤ δl) :
    ‖endpointOperator D R A L - endpointOperator D' R' A' L'‖ ≤
      (1 + d ^ 2 * r * a) * δl +
        (2 * d * r * a * δd + d ^ 2 * a * δr + d ^ 2 * r * δa) * l := by
  have hs := correctionOperator_norm_le D' R' A' d r a hd' hr' ha'
  have hs0 := (norm_nonneg _).trans hs
  have hds := correctionOperator_sub_norm_le D D' R R' A A' d r a δd δr δa
    hd hd' hr hr' ha ha' hδd hδr hδa
  have hds0 := (norm_nonneg _).trans hds
  have hprod := (norm_comp_sub_le (correctionOperator D R A)
    (correctionOperator D' R' A') L L').trans
      (add_le_add (mul_le_mul hds hl (norm_nonneg _) hds0)
        (mul_le_mul hs hδl (norm_nonneg _) hs0))
  have he : endpointOperator D R A L - endpointOperator D' R' A' L' =
      (L-L') - ((correctionOperator D R A).comp L - (correctionOperator D' R' A').comp L') := by
    unfold endpointOperator
    abel
  rw [he]
  exact ((norm_sub_le _ _).trans (add_le_add hδl hprod)).trans_eq (by ring)

/-- The transported quadratic form used by the fixed-coordinate inverse. -/
def formOperator (D : S →L[ℝ] E) (A : E →L[ℝ] E) : S →L[ℝ] S :=
  D.adjoint.comp (A.comp D)

theorem formOperator_sub_norm_le
    (D D' : S →L[ℝ] E) (A A' : E →L[ℝ] E) (d a δd δa : ℝ)
    (hd : ‖D‖ ≤ d) (hd' : ‖D'‖ ≤ d) (ha : ‖A‖ ≤ a) (ha' : ‖A'‖ ≤ a)
    (hδd : ‖D - D'‖ ≤ δd) (hδa : ‖A - A'‖ ≤ δa) :
    ‖formOperator D A - formOperator D' A'‖ ≤ 2 * d * a * δd + d ^ 2 * δa := by
  have had : ‖D.adjoint-D'.adjoint‖ ≤ δd := (norm_adjoint_sub D D').trans_le hδd
  have h := correctionOperator_sub_norm_le D.adjoint D'.adjoint A A'
    (ContinuousLinearMap.id ℝ S) (ContinuousLinearMap.id ℝ S) d a 1 δd δa 0
    (by simpa only [LinearIsometryEquiv.norm_map] using hd)
    (by simpa only [LinearIsometryEquiv.norm_map] using hd') ha ha' norm_id_le norm_id_le
    had hδa (by simp)
  simpa only [correctionOperator, adjoint_adjoint, comp_id, mul_one, mul_zero, add_zero,
    formOperator] using h

end EulerCoerciveEndpointBounds

end
end

end

section

/-!
The neighboring-label estimate for the actual nonzero-terminal inverse.
The inverse is the same coercive inverse as the packet construction.  All
constants below bound coefficients or their explicit frame-transport cost;
no bound on an unknown inverse or on a supplied solution is assumed.
-/

@[expose] public section

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

end
end

end

section

/-! Polynomial size and coefficient sensitivity of the actual source (10) generator. -/

@[expose] public section

noncomputable section

namespace EulerTransverseGeneratorDifference

open Set ContinuousLinearMap InnerProductSpace
  EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseForwardInverse EulerCoerciveEndpointBounds EulerCoerciveProjection

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gram_sub_norm_le (A B : U →L[ℝ] E) (q : ℝ)
    (hA : ‖A‖ ≤ q) (hB : ‖B‖ ≤ q) :
    ‖gram A - gram B‖ ≤ 2 * q * ‖A-B‖ := by
  have hq := (norm_nonneg A).trans hA
  have had : ‖A.adjoint-B.adjoint‖ = ‖A-B‖ := norm_adjoint_sub A B
  apply (norm_comp_sub_le A.adjoint B.adjoint A B).trans
  simp only [had, LinearIsometryEquiv.norm_map]
  exact (add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))).trans_eq (by ring)

theorem gramInverse_sub_norm_le (A B : U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ ‖A u‖ ^ 2) (hB : ∀ u, c * ‖u‖ ^ 2 ≤ ‖B u‖ ^ 2)
    (q : ℝ) (hAn : ‖A‖ ≤ q) (hBn : ‖B‖ ≤ q) :
    ‖gramInverse A c hc hA - gramInverse B c hc hB‖ ≤
      2 * (c⁻¹)^2 * q * ‖A-B‖ := by
  have hh := coerciveInverse_norm_sub_le (gram A) (gram B) c c hc hc
    (gram_coercive A c hA) (gram_coercive B c hB)
  have hgram : ‖gram B-gram A‖ ≤ 2*q*‖A-B‖ :=
    (norm_sub_rev _ _).trans_le (gram_sub_norm_le A B q hAn hBn)
  exact hh.trans ((mul_le_mul_of_nonneg_left hgram (by positivity)).trans_eq (by ring))

variable (T : ℝ) (Q Q₁ P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hQ : ∀ t u, c * ‖u‖ ^ 2 ≤ ‖Q t u‖ ^ 2)
  (hP : ∀ t u, c * ‖u‖ ^ 2 ≤ ‖P t u‖ ^ 2)

theorem generator_norm_le (q r : ℝ) (hQn : ‖Q‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ r) :
    ‖generator T Q Q₁ c hc hQ‖ ≤ 2 * c⁻¹ * q * r := by
  have hq := (norm_nonneg Q).trans hQn
  have hr := (norm_nonneg Q₁).trans hQ₁n
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  change ‖(-2 : ℝ) • (gramInverse (Q t) c hc (hQ t)).comp ((Q t).adjoint.comp (Q₁ t))‖ ≤ _
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs]
  have hprod : ‖(Q t).adjoint.comp (Q₁ t)‖ ≤ q*r := by
    apply (opNorm_comp_le _ _).trans
    simp only [LinearIsometryEquiv.norm_map]
    exact mul_le_mul ((Q.norm_coe_le_norm t).trans hQn)
      ((Q₁.norm_coe_le_norm t).trans hQ₁n) (norm_nonneg _) hq
  apply (mul_le_mul_of_nonneg_left ((opNorm_comp_le _ _).trans
    (mul_le_mul (gramInverse_norm (Q t) c hc (hQ t)) hprod
      (norm_nonneg _) (inv_nonneg.mpr hc.le))) (by norm_num)).trans_eq
  ring

/-- Only frame differences occur in the genuine generator difference. -/
def generatorDifferenceCost (c q r δq δr : ℝ) : ℝ :=
  (4*(c⁻¹)^2*q^2*r + 2*c⁻¹*r)*δq + 2*c⁻¹*q*δr

theorem generator_sub_norm_le (q r : ℝ)
    (hQn : ‖Q‖ ≤ q) (hPn : ‖P‖ ≤ q) (hQ₁n : ‖Q₁‖ ≤ r) (_hP₁n : ‖P₁‖ ≤ r) :
    ‖generator T Q Q₁ c hc hQ - generator T P P₁ c hc hP‖ ≤
      generatorDifferenceCost c q r ‖Q-P‖ ‖Q₁-P₁‖ := by
  have hq := (norm_nonneg Q).trans hQn
  have hr := (norm_nonneg Q₁).trans hQ₁n
  have hcost : 0 ≤ generatorDifferenceCost c q r ‖Q-P‖ ‖Q₁-P₁‖ := by
    unfold generatorDifferenceCost
    positivity
  apply (ContinuousMap.norm_le _ hcost).2
  intro t
  have htQ : ‖Q t‖ ≤ q := (Q.norm_coe_le_norm t).trans hQn
  have htP : ‖P t‖ ≤ q := (P.norm_coe_le_norm t).trans hPn
  have htQ₁ : ‖Q₁ t‖ ≤ r := (Q₁.norm_coe_le_norm t).trans hQ₁n
  have hδQ : ‖Q t-P t‖ ≤ ‖Q-P‖ := (Q-P).norm_coe_le_norm t
  have hδQ₁ : ‖Q₁ t-P₁ t‖ ≤ ‖Q₁-P₁‖ := (Q₁-P₁).norm_coe_le_norm t
  have hI : ‖gramInverse (Q t) c hc (hQ t) - gramInverse (P t) c hc (hP t)‖ ≤
      2*(c⁻¹)^2*q*‖Q-P‖ :=
    (gramInverse_sub_norm_le (Q t) (P t) c hc (hQ t) (hP t) q htQ htP).trans
      (mul_le_mul_of_nonneg_left hδQ (by positivity))
  have hprod : ‖(Q t).adjoint.comp (Q₁ t)‖ ≤ q*r := by
    apply (opNorm_comp_le _ _).trans
    simp only [LinearIsometryEquiv.norm_map]
    exact mul_le_mul htQ htQ₁ (norm_nonneg _) hq
  have hprodδ : ‖(Q t).adjoint.comp (Q₁ t) - (P t).adjoint.comp (P₁ t)‖ ≤
      ‖Q-P‖*r + q*‖Q₁-P₁‖ := by
    apply (norm_comp_sub_le _ _ _ _).trans
    have had : ‖(Q t).adjoint-(P t).adjoint‖ = ‖Q t-P t‖ := norm_adjoint_sub (Q t) (P t)
    simp only [had, LinearIsometryEquiv.norm_map]
    exact add_le_add (mul_le_mul hδQ htQ₁ (by positivity) (by positivity))
      (mul_le_mul htP hδQ₁ (norm_nonneg _) hq)
  have htotal := (norm_comp_sub_le
    (gramInverse (Q t) c hc (hQ t)) (gramInverse (P t) c hc (hP t))
    ((Q t).adjoint.comp (Q₁ t)) ((P t).adjoint.comp (P₁ t))).trans
      (add_le_add (mul_le_mul hI hprod (norm_nonneg _) (by positivity))
        (mul_le_mul (gramInverse_norm (P t) c hc (hP t)) hprodδ
          (norm_nonneg _) (inv_nonneg.mpr hc.le)))
  change ‖(-2 : ℝ) • (gramInverse (Q t) c hc (hQ t)).comp ((Q t).adjoint.comp (Q₁ t)) -
    (-2 : ℝ) • (gramInverse (P t) c hc (hP t)).comp ((P t).adjoint.comp (P₁ t))‖ ≤ _
  rw [← smul_sub, norm_smul]
  norm_num only [Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left htotal (by norm_num)).trans_eq
    (by unfold generatorDifferenceCost; ring)

end EulerTransverseGeneratorDifference

end
end

end

section

/-! Uniform-time polynomial bounds from an actual L² value and generator derivative. -/

@[expose] public section

noncomputable section

namespace EulerTimeH1GeneratorBounds

open Set ContinuousLinearMap EulerTimeLp EulerTimeH1Reconstruction
  EulerVolterraConvolution EulerTimeLpCoefficientMap EulerContinuousTimeIntegral
  EulerCoerciveEndpointBounds

variable {U E V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (T : ℝ) (hT : 0 ≤ T)

/-- Reconstruct from the L² value and its prescribed generator derivative. -/
def generatorTrace (B : C(Icc (0 : ℝ) T, U →L[ℝ] U)) :
    TimeLp T U →L[ℝ] C(Icc (0 : ℝ) T, U) :=
  valuePart T hT + (derivativePart T hT).comp (timeMultiplier T hT B)

/-- Trace cost, given by `(1+T) * (T⁻¹ + 2*b)`. -/
def traceCost (T b : ℝ) : ℝ := (1+T) * (T⁻¹ + 2*b)

theorem sqrt_le_one_add (hT : 0 ≤ T) : Real.sqrt T ≤ 1+T := by
  nlinarith only [Real.sq_sqrt hT, Real.sqrt_nonneg T, sq_nonneg (Real.sqrt T-1)]

theorem generatorTrace_norm_le (hTpos : 0 < T)
    (B : C(Icc (0 : ℝ) T, U →L[ℝ] U)) (b : ℝ) (hB : ‖B‖ ≤ b) :
    ‖generatorTrace T hT B‖ ≤ traceCost T b := by
  have hb := (show 0 ≤ ‖B‖ by positivity).trans hB
  have hm := (timeMultiplier_norm T hT B).trans hB
  have hn := (norm_add_le (valuePart (E := U) T hT)
    ((derivativePart T hT).comp (timeMultiplier T hT B))).trans
      (add_le_add (valuePart_norm_le (E := U) T hTpos)
        ((opNorm_comp_le _ _).trans
          (mul_le_mul (derivativePart_norm_le (E := U) T hTpos) hm
            (norm_nonneg _) (by positivity))))
  change ‖generatorTrace T hT B‖ ≤ _ at hn
  apply hn.trans
  calc
    (T⁻¹*Real.sqrt T)+(2*Real.sqrt T)*b = Real.sqrt T * (T⁻¹+2*b) := by ring
    _ ≤ (1+T)*(T⁻¹+2*b) := mul_le_mul_of_nonneg_right (sqrt_le_one_add T hT) (by positivity)

theorem generatorTrace_sub_norm_le (hTpos : 0 < T)
    (B B' : C(Icc (0 : ℝ) T, U →L[ℝ] U)) :
    ‖generatorTrace T hT B - generatorTrace T hT B'‖ ≤ 2*(1+T)*‖B-B'‖ := by
  have he : generatorTrace T hT B - generatorTrace T hT B' =
      (derivativePart T hT).comp (timeMultiplier T hT B-timeMultiplier T hT B') := by
    unfold generatorTrace
    rw [comp_sub]
    abel
  rw [he]
  apply ((opNorm_comp_le _ _).trans (mul_le_mul
    (derivativePart_norm_le (E := U) T hTpos)
    (EulerTransverseEndpointBounds.multiplier_sub_norm_le T hT B B')
    (norm_nonneg _) (by positivity))).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sqrt_le_one_add T hT) (by norm_num)) (by positivity)

theorem continuousMultiplier_sub_norm_le
    (Q P : C(Icc (0 : ℝ) T, U →L[ℝ] E)) : ‖multiplier Q - multiplier P‖ ≤ ‖Q-P‖ := by
  change ‖EulerContinuousPathCalculus.coefficientMap Q -
    EulerContinuousPathCalculus.coefficientMap P‖ ≤ _
  rw [← map_sub]
  exact multiplier_norm (Q-P)

theorem transportedTrace_norm_le (hTpos : 0 < T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (B : C(Icc (0 : ℝ) T, U →L[ℝ] U)) (S : V →L[ℝ] TimeLp T U)
    (q b s : ℝ) (hQ : ‖Q‖ ≤ q) (hB : ‖B‖ ≤ b) (hS : ‖S‖ ≤ s) :
    ‖(multiplier Q).comp ((generatorTrace T hT B).comp S)‖ ≤ q * traceCost T b * s := by
  have hq := (show 0 ≤ ‖Q‖ by positivity).trans hQ
  have htrace := generatorTrace_norm_le T hT hTpos B b hB
  have ht0 := (show 0 ≤ ‖generatorTrace T hT B‖ by positivity).trans htrace
  have hs := (opNorm_comp_le (generatorTrace T hT B) S).trans
    (mul_le_mul htrace hS (norm_nonneg _) ht0)
  exact ((opNorm_comp_le _ _).trans (mul_le_mul ((multiplier_norm Q).trans hQ) hs
    (norm_nonneg _) hq)).trans_eq (by ring)

theorem transportedTrace_sub_norm_le (hTpos : 0 < T)
    (Q P : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (B B' : C(Icc (0 : ℝ) T, U →L[ℝ] U)) (S S' : V →L[ℝ] TimeLp T U)
    (q b s δq δb δs : ℝ) (hP : ‖P‖ ≤ q) (hB : ‖B‖ ≤ b) (hB' : ‖B'‖ ≤ b)
    (hS : ‖S‖ ≤ s) (hδq : ‖Q - P‖ ≤ δq) (hδb : ‖B - B'‖ ≤ δb) (hδs : ‖S - S'‖ ≤ δs) :
    ‖(multiplier Q).comp ((generatorTrace T hT B).comp S) -
      (multiplier P).comp ((generatorTrace T hT B').comp S')‖ ≤
      δq * traceCost T b * s + q * (2*(1+T)*δb*s + traceCost T b*δs) := by
  have hq := (show 0 ≤ ‖P‖ by positivity).trans hP
  have htrace := generatorTrace_norm_le T hT hTpos B b hB
  have htrace' := generatorTrace_norm_le T hT hTpos B' b hB'
  have ht0 := (show 0 ≤ ‖generatorTrace T hT B‖ by positivity).trans htrace
  have hδt := (generatorTrace_sub_norm_le T hT hTpos B B').trans
    (mul_le_mul_of_nonneg_left hδb (by positivity))
  have hδt0 := (show 0 ≤ ‖generatorTrace T hT B - generatorTrace T hT B'‖ by positivity).trans hδt
  have hs := (opNorm_comp_le (generatorTrace T hT B) S).trans
    (mul_le_mul htrace hS (norm_nonneg _) ht0)
  have hds := (norm_comp_sub_le (generatorTrace T hT B) (generatorTrace T hT B') S S').trans
    (add_le_add (mul_le_mul hδt hS (norm_nonneg _) hδt0)
      (mul_le_mul htrace' hδs (norm_nonneg _) ht0))
  have hδq0 := (show 0 ≤ ‖Q-P‖ by positivity).trans hδq
  apply ((norm_comp_sub_le _ _ _ _).trans
    (add_le_add (mul_le_mul ((continuousMultiplier_sub_norm_le T Q P).trans hδq) hs
      (norm_nonneg _) hδq0)
      (mul_le_mul ((multiplier_norm P).trans hP) hds (norm_nonneg _) hq))).trans_eq
  ring

end EulerTimeH1GeneratorBounds

end
end

end

@[expose] public section

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

/-- Slope cost, given by `r * (1+d^2*(2*r^2)*a) * (affineCost T*d)`. -/
def slopeCost (T d a r : ℝ) : ℝ := r * (1+d^2*(2*r^2)*a) * (affineCost T*d)

/-- Slope difference cost, given by `r * (affineCost T * endpointDifferenceCost d (2*r^2) a δd
δa + δd * slopeCost T d a r)`. -/
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

/-- History cost, given by `q * traceCost T (2*c⁻¹*q*q₁) * slopeCost T d a r`. -/
def historyCost (T c q q₁ d a r : ℝ) : ℝ :=
  q * traceCost T (2*c⁻¹*q*q₁) * slopeCost T d a r

/-- History difference cost, constructed using `δq`. -/
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
