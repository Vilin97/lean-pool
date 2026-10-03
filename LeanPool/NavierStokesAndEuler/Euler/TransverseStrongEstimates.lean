/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEquation
import Mathlib.Algebra.Order.Star.Real

/-!
# Quantitative bounds for the actual transverse coordinate inverse

These bounds use the lower frame constant and coefficient norms. In particular
no exponential dependence on the undifferentiated coefficient norm is introduced.
-/

@[expose] public section

-- Numeric exponents elaborate as natural numbers at once: left to the default instance,
-- every `x ^ 2` of a long statement stays pending and is retried after each later binder.
local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))


noncomputable section

namespace EulerTransverseStrongEstimates

open Set InnerProductSpace ContinuousLinearMap MeasureTheory
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTransverseVariationalInverse
  EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseCoordinateRegularity EulerTransverseStrongEquation
  EulerTransverseMomentumRegularity

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)

/-- The genuine inverse coefficient has the uniform coercive inverse bound. -/
theorem gramInversePath_norm : ‖gramInversePath T Q c hc hQ‖ ≤ c⁻¹ := by
  apply (ContinuousMap.norm_le _ (inv_nonneg.mpr hc.le)).2
  intro t
  exact gramInverse_norm (Q t) c hc (hQ t)

/-- The Gram derivative is controlled by the actual frame and frame derivative norms. -/
theorem gramDerivativePath_norm :
    ‖gramDerivativePath T Q Q₁‖ ≤ 2 * ‖Q‖ * ‖Q₁‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (norm_nonneg _))).2
  intro t
  calc
    _ ≤ ‖(adjoint (𝕜 := ℝ) (E := U) (F := E) (Q₁ t)).comp (Q t)‖ +
        ‖(adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t)).comp (Q₁ t)‖ := norm_add_le _ _
    _ ≤ ‖adjoint (𝕜 := ℝ) (E := U) (F := E) (Q₁ t)‖ * ‖Q t‖ +
        ‖adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t)‖ * ‖Q₁ t‖ :=
      add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ = ‖Q₁ t‖ * ‖Q t‖ + ‖Q t‖ * ‖Q₁ t‖ := by
      simp only [LinearIsometryEquiv.norm_map]
    _ ≤ ‖Q₁‖ * ‖Q‖ + ‖Q‖ * ‖Q₁‖ :=
      add_le_add
        (mul_le_mul (Q₁.norm_coe_le_norm t) (Q.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Q.norm_coe_le_norm t) (Q₁.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- The derivative of the inverse pays two inverse factors and one coefficient derivative. -/
theorem gramInverseDerivativePath_norm :
    ‖gramInverseDerivativePath T Q Q₁ c hc hQ‖ ≤ 2 * (c⁻¹)^2 * ‖Q‖ * ‖Q₁‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg
    (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _)) (norm_nonneg _)) (norm_nonneg _))).2
  intro t
  change ‖-(gramInversePath T Q c hc hQ t).comp
    ((gramDerivativePath T Q Q₁ t).comp (gramInversePath T Q c hc hQ t))‖ ≤ _
  rw [norm_neg]
  calc
    _ ≤ ‖gramInversePath T Q c hc hQ t‖ *
        (‖gramDerivativePath T Q Q₁ t‖ * ‖gramInversePath T Q c hc hQ t‖) :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ c⁻¹ * ((2 * ‖Q‖ * ‖Q₁‖) * c⁻¹) := by
      have hinv := gramInverse_norm (Q t) c hc (hQ t)
      have hder := ((gramDerivativePath T Q Q₁).norm_coe_le_norm t).trans
        (gramDerivativePath_norm T Q Q₁)
      exact mul_le_mul hinv (mul_le_mul hder hinv (norm_nonneg _) ((norm_nonneg _).trans hder))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (inv_nonneg.mpr hc.le)
    _ = _ := by ring

/-- Recovering coordinates has one inverse factor. -/
theorem frameLeftInversePath_norm :
    ‖frameLeftInversePath T Q c hc hQ‖ ≤ c⁻¹ * ‖Q‖ := by
  apply (ContinuousMap.norm_le (frameLeftInversePath T Q c hc hQ)
    (mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg Q))).2
  intro t
  change ‖(gramInversePath T Q c hc hQ t).comp (adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t))‖ ≤ _
  calc
    _ ≤ ‖gramInversePath T Q c hc hQ t‖ * ‖adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t)‖ :=
      opNorm_comp_le _ _
    _ = ‖gramInversePath T Q c hc hQ t‖ * ‖Q t‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ c⁻¹ * ‖Q‖ := mul_le_mul (gramInverse_norm (Q t) c hc (hQ t))
      (Q.norm_coe_le_norm t) (norm_nonneg _) (inv_nonneg.mpr hc.le)

/-- Differentiating coordinate recovery has polynomial coefficient cost. -/
theorem frameLeftInverseDerivativePath_norm :
    ‖frameLeftInverseDerivativePath T Q Q₁ c hc hQ‖ ≤
      2 * (c⁻¹)^2 * ‖Q‖^2 * ‖Q₁‖ + c⁻¹ * ‖Q₁‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _)) (sq_nonneg _)) (norm_nonneg _))
    (mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg _)))).2
  intro t
  calc
    _ ≤ ‖(gramInverseDerivativePath T Q Q₁ c hc hQ t).comp
          (adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t))‖ +
        ‖(gramInversePath T Q c hc hQ t).comp
          (adjoint (𝕜 := ℝ) (E := U) (F := E) (Q₁ t))‖ := norm_add_le _ _
    _ ≤ ‖gramInverseDerivativePath T Q Q₁ c hc hQ t‖ *
          ‖adjoint (𝕜 := ℝ) (E := U) (F := E) (Q t)‖ +
        ‖gramInversePath T Q c hc hQ t‖ * ‖adjoint (𝕜 := ℝ) (E := U) (F := E) (Q₁ t)‖ :=
      add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ = ‖gramInverseDerivativePath T Q Q₁ c hc hQ t‖ * ‖Q t‖ +
        ‖gramInversePath T Q c hc hQ t‖ * ‖Q₁ t‖ := by
      simp only [LinearIsometryEquiv.norm_map]
    _ ≤ (2 * (c⁻¹)^2 * ‖Q‖ * ‖Q₁‖) * ‖Q‖ + c⁻¹ * ‖Q₁‖ := by
      have h₁ := ((gramInverseDerivativePath T Q Q₁ c hc hQ).norm_coe_le_norm t).trans
        (gramInverseDerivativePath_norm T Q Q₁ c hc hQ)
      exact add_le_add
        (mul_le_mul h₁ (Q.norm_coe_le_norm t) (norm_nonneg _) ((norm_nonneg _).trans h₁))
        (mul_le_mul (gramInverse_norm (Q t) c hc (hQ t)) (Q₁.norm_coe_le_norm t)
          (norm_nonneg _) (inv_nonneg.mpr hc.le))
    _ = _ := by ring

/-- Explicit polynomial bound for the actual coordinate derivative. -/
theorem coordinateDerivative_norm (hT : 0 ≤ T) (u : TimeLp T E) :
    ‖coordinateDerivative T hT Q Q₁ c hc hQ u‖ ≤
      ((2 * (c⁻¹)^2 * ‖Q‖^2 * ‖Q₁‖ + c⁻¹ * ‖Q₁‖) * T + c⁻¹ * ‖Q‖) * ‖u‖ := by
  have hs : Real.sqrt (T^2/2) ≤ T := by
    calc
      _ ≤ Real.sqrt (T^2) := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg T])
      _ = T := Real.sqrt_sq hT
  apply (productDerivative_norm_le T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ) u).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  apply add_le_add _ (frameLeftInversePath_norm T Q c hc hQ)
  exact mul_le_mul (frameLeftInverseDerivativePath_norm T Q Q₁ c hc hQ) hs
    (Real.sqrt_nonneg _) (by positivity)

/-- The actual coercive forcing-to-coordinate-velocity map has a polynomial bound. -/
theorem transverseCoordinateDerivative_norm (hT : 0 ≤ T)
    (m : Icc (0 : ℝ) T → E) (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2) (f : TimeLp T E) :
    ‖coordinateDerivative T hT Q Q₁ c hc hQ
      (transverseSolver T hT m H K hK hH hsmall f : TimeLp T E)‖ ≤
      ((2 * (c⁻¹)^2 * ‖Q‖^2 * ‖Q₁‖ + c⁻¹ * ‖Q₁‖) * T + c⁻¹ * ‖Q‖) *
        (2 * T * ‖f‖) := by
  apply (coordinateDerivative_norm T Q Q₁ c hc hQ hT _).trans
  exact mul_le_mul_of_nonneg_left (transverseSolver_norm T hT m H K hK hH hsmall f) (by positivity)

/-- Inverting the projected strong equation is an exact equality of actual L² fields. -/
theorem acceleration_eq_inverse (hT : 0 ≤ T) (v a : TimeLp T U) (f : TimeLp T E)
    (heq : ∀ᵐ t ∂timeMeasure T, gram (extendPath T hT Q t) (a t) =
      adjoint (𝕜 := ℝ) (E := U) (F := E) (extendPath (Y := U →L[ℝ] E) T hT Q t)
        (f t - (2 : ℝ) • extendPath T hT Q₁ t (v t))) :
    a = timeMultiplier T hT (gramInversePath T Q c hc hQ)
      (adjoint (𝕜 := ℝ) (E := TimeLp T U) (F := TimeLp T E) (timeMultiplier T hT Q)
        (f - (2 : ℝ) • timeMultiplier T hT Q₁ v)) := by
  let r := f - (2 : ℝ) • timeMultiplier T hT Q₁ v
  apply Lp.ext
  filter_upwards [heq,
    timeMultiplier_ae T hT (gramInversePath T Q c hc hQ) (momentum T hT Q r),
    momentum_ae T hT Q r,
    Lp.coeFn_sub f ((2 : ℝ) • timeMultiplier T hT Q₁ v),
    Lp.coeFn_smul (2 : ℝ) (timeMultiplier T hT Q₁ v),
    timeMultiplier_ae T hT Q₁ v] with t ht hB hp hr hs hQ₁
  change a t = (timeMultiplier T hT (gramInversePath T Q c hc hQ) (momentum T hT Q r)) t
  change r t = f t - ((2 : ℝ) • timeMultiplier T hT Q₁ v) t at hr
  change ((2 : ℝ) • timeMultiplier T hT Q₁ v) t = (2 : ℝ) • (timeMultiplier T hT Q₁ v) t at hs
  simp only [hB, hp, hr, hs, hQ₁]
  have hinv := congrArg (gramInverse (Q (projIcc 0 T hT t)) c hc (hQ (projIcc 0 T hT t))) ht
  dsimp only [extendPath] at hinv
  rw [inverse_gram_apply] at hinv
  exact hinv

include hc hQ in
/-- The strong acceleration bound pays one inverse Gram factor and no derivative
of the Hessian or extra undifferentiated time-growth factor. -/
theorem acceleration_norm (hT : 0 ≤ T) (v a : TimeLp T U) (f : TimeLp T E)
    (heq : ∀ᵐ t ∂timeMeasure T, gram (extendPath T hT Q t) (a t) =
      adjoint (𝕜 := ℝ) (E := U) (F := E) (extendPath (Y := U →L[ℝ] E) T hT Q t)
        (f t - (2 : ℝ) • extendPath T hT Q₁ t (v t))) :
    ‖a‖ ≤ c⁻¹ * ‖Q‖ * (‖f‖ + 2 * ‖Q₁‖ * ‖v‖) := by
  rw [acceleration_eq_inverse T Q Q₁ c hc hQ hT v a f heq]
  let r := f - (2 : ℝ) • timeMultiplier T hT Q₁ v
  have hM : ‖timeMultiplier T hT Q‖ ≤ ‖Q‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q) (timeApply_bound T hT Q)
  have hp : ‖adjoint (𝕜 := ℝ) (E := TimeLp T U) (F := TimeLp T E) (timeMultiplier T hT Q) r‖ ≤
      ‖Q‖ * ‖r‖ := by
    exact ((adjoint (𝕜 := ℝ) (E := TimeLp T U) (F := TimeLp T E)
      (timeMultiplier T hT Q)).le_opNorm r).trans (mul_le_mul_of_nonneg_right
        ((LinearIsometryEquiv.norm_map _ _).trans_le hM) (norm_nonneg r))
  have hr : ‖r‖ ≤ ‖f‖ + 2 * ‖Q₁‖ * ‖v‖ := by
    have hq : ‖timeMultiplier T hT Q₁ v‖ ≤ ‖Q₁‖ * ‖v‖ := timeApply_bound T hT Q₁ v
    exact (norm_sub_le f ((2 : ℝ) • timeMultiplier T hT Q₁ v)).trans (add_le_add le_rfl
      ((norm_smul_of_nonneg zero_le_two _).trans_le
        ((mul_le_mul_of_nonneg_left hq zero_le_two).trans_eq (mul_assoc _ _ _).symm)))
  calc
    _ ≤ ‖gramInversePath T Q c hc hQ‖ *
        ‖adjoint (𝕜 := ℝ) (E := TimeLp T U) (F := TimeLp T E) (timeMultiplier T hT Q) r‖ :=
      timeApply_bound T hT (gramInversePath T Q c hc hQ) _
    _ ≤ c⁻¹ * (‖Q‖ * ‖r‖) := mul_le_mul (gramInversePath_norm T Q c hc hQ) hp
      (norm_nonneg _) (inv_nonneg.mpr hc.le)
    _ ≤ c⁻¹ * (‖Q‖ * (‖f‖ + 2 * ‖Q₁‖ * ‖v‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (norm_nonneg Q))
        (inv_nonneg.mpr hc.le)
    _ = _ := by ring

/-- Applying the strong bound to the actual variational solver gives a polynomial
acceleration estimate in terms of its already bounded coordinate velocity. -/
theorem transverseCoordinateSecondDerivative_norm
    (Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (hT : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖^2)
    (hsmall : K * (T^2/2) ≤ 1/2)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t))) (f : TimeLp T E) :
    let u : TimeLp T E := transverseSolver T hT.le m H K hK hH hsmall f
    ‖coordinateSecondDerivative T hT.le Q Q₁ Q₂ c hc hQ H u f‖ ≤
      c⁻¹ * ‖Q‖ * (‖f‖ + 2 * ‖Q₁‖ * ‖coordinateDerivative T hT.le Q Q₁ c hc hQ u‖) := by
  let u : TimeLp T E := transverseSolver T hT.le m H K hK hH hsmall f
  obtain ⟨v, _, _, hv, _, _, heq⟩ :=
    transverseSolver_strong T hT.le Q Q₁ Q₂ c hc hQ hd hd₁ hT m hm hRange
      H K hK hH hsmall hframe f
  apply acceleration_norm T Q Q₁ c hc hQ hT.le
  filter_upwards [hv, heq] with t hvt ht
  rw [hvt]
  exact ht

end EulerTransverseStrongEstimates
