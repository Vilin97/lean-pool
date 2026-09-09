/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEstimates

@[expose] public section

/-!
# Transport of actual H¹ derivative spaces by a moving frame

The forward map is the actual derivative of `Q(t) Jv(t)`. Its left inverse is
the actual derivative after applying the constructed Gram left inverse. This
places parameter-dependent transverse variational problems on one fixed Hilbert
space before coefficient differentiation or all-order estimates.
-/

noncomputable section

namespace EulerTimeH1FrameTransport

open Set InnerProductSpace ContinuousLinearMap MeasureTheory
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTransverseVariationalInverse
  EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseCoordinateRegularity EulerTransverseStrongEstimates

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖^2 ≤ ‖Q t x‖^2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)

include hd in
/-- Differentiating the constructed left inverse recovers every coordinate
H¹ derivative. No initial condition is needed for this transport identity. -/
theorem coordinateDerivative_productDerivative (v : TimeLp T U) :
    coordinateDerivative T hT Q Q₁ c hc hQ (productDerivative T hT Q Q₁ v) = v := by
  apply terminalPrimitive_injective T hT
  apply ContinuousMap.ext
  intro t
  change terminalPrimitive T hT
    (productDerivative T hT (frameLeftInversePath T Q c hc hQ)
      (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
      (productDerivative T hT Q Q₁ v)) t = _
  rw [terminalPrimitive_productDerivative T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
    (frameLeftInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd),
    terminalPrimitive_productDerivative T hT Q Q₁ hd]
  exact frameLeftInverse_apply (Q t) c hc (hQ t) _

/-- A strictly positive polynomial transport cost from the inverse-frame bounds. -/
def transportCost : ℝ :=
  1 + ((2 * (c⁻¹)^2 * ‖Q‖^2 * ‖Q₁‖ + c⁻¹ * ‖Q₁‖) * T + c⁻¹ * ‖Q‖)

omit [CompleteSpace U] [CompleteSpace E] in
include hT hc in
/-- The transport cost is positive even in a degenerate zero-dimensional space. -/
theorem transportCost_pos : 0 < transportCost T Q Q₁ c := by
  unfold transportCost
  positivity

include hc hQ hd in
/-- The coordinate derivative norm is bounded by the physical derivative norm. -/
theorem norm_le_transportCost_productDerivative (v : TimeLp T U) :
    ‖v‖ ≤ transportCost T Q Q₁ c * ‖productDerivative T hT Q Q₁ v‖ := by
  calc
    ‖v‖ = ‖coordinateDerivative T hT Q Q₁ c hc hQ (productDerivative T hT Q Q₁ v)‖ := by
      rw [coordinateDerivative_productDerivative T hT Q Q₁ c hc hQ hd]
    _ ≤ ((2 * (c⁻¹)^2 * ‖Q‖^2 * ‖Q₁‖ + c⁻¹ * ‖Q₁‖) * T + c⁻¹ * ‖Q‖) *
        ‖productDerivative T hT Q Q₁ v‖ :=
      coordinateDerivative_norm T Q Q₁ c hc hQ hT _
    _ ≤ transportCost T Q Q₁ c * ‖productDerivative T hT Q Q₁ v‖ := by
      unfold transportCost
      nlinarith only [norm_nonneg (productDerivative T hT Q Q₁ v)]

include hc hQ hd in
/-- A quantitative lower bound for the transported kinetic energy. -/
theorem productDerivative_norm_sq_lower (v : TimeLp T U) :
    (transportCost T Q Q₁ c)⁻¹ ^ 2 * ‖v‖^2 ≤ ‖productDerivative T hT Q Q₁ v‖^2 := by
  have hC := transportCost_pos T hT Q Q₁ c hc
  have hn := norm_le_transportCost_productDerivative T hT Q Q₁ c hc hQ hd v
  have hdiv : ‖v‖ / transportCost T Q Q₁ c ≤ ‖productDerivative T hT Q Q₁ v‖ :=
    (div_le_iff₀ hC).2 (by simpa only [mul_comm] using hn)
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg v) hC.le) (norm_nonneg _)).2 hdiv
  simpa only [div_eq_mul_inv, mul_pow, mul_comm] using hs

/-- The fixed Hilbert space of coordinate derivatives with zero initial trace.
Terminal zero is already supplied by the primitive. -/
def zeroTraceDerivatives (T : ℝ) (hT : 0 ≤ T) : Submodule ℝ (TimeLp T U) :=
  LinearMap.ker (initialTrace T hT).toLinearMap

/-- The fixed zero-trace coordinate space is complete. -/
instance zeroTraceDerivatives_complete (T : ℝ) (hT : 0 ≤ T) :
    CompleteSpace (zeroTraceDerivatives (U := U) T hT) :=
  (initialTrace (E := U) T hT).isClosed_ker.completeSpace_coe

variable (m : Icc (0 : ℝ) T → E)
  (hTangent : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
  (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)

/-- Actual differentiation transports the fixed coordinate space to the
physical zero-endpoint moving-plane space. -/
def transverseForward : zeroTraceDerivatives (U := U) T hT →L[ℝ] transverseDerivatives T hT m :=
  ((productDerivative T hT Q Q₁).comp (zeroTraceDerivatives (U := U) T hT).subtypeL).codRestrict
    (transverseDerivatives T hT m) (fun v =>
      EulerTransverseMomentumRegularity.productDerivative_mem_transverse T hT Q Q₁ hd m hTangent
        (v : TimeLp T U) v.property)

/-- Applying the constructed inverse-frame derivative transports back to the
same fixed coordinate space. -/
def transverseBackward : transverseDerivatives T hT m →L[ℝ] zeroTraceDerivatives (U := U) T hT :=
  ((productDerivative T hT (frameLeftInversePath T Q c hc hQ)
    (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)).comp
      (transverseDerivatives T hT m).subtypeL).codRestrict
    (zeroTraceDerivatives T hT) (fun u => by
      change initialTrace T hT (productDerivative T hT (frameLeftInversePath T Q c hc hQ)
        (frameLeftInverseDerivativePath T Q Q₁ c hc hQ) (u : TimeLp T E)) = 0
      rw [initialTrace_productDerivative T hT (frameLeftInversePath T Q c hc hQ)
        (frameLeftInverseDerivativePath T Q Q₁ c hc hQ)
        (frameLeftInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd), u.property.1, map_zero])

/-- The backward transport is the actual inverse on every fixed coordinate derivative. -/
theorem transverseBackward_forward (v : zeroTraceDerivatives (U := U) T hT) :
    transverseBackward T hT Q Q₁ c hc hQ hd m
      (transverseForward T hT Q Q₁ hd m hTangent v) = v := by
  apply Subtype.ext
  exact coordinateDerivative_productDerivative T hT Q Q₁ c hc hQ hd (v : TimeLp T U)

include hRange in
/-- The forward transport recovers every physical transverse derivative. -/
theorem transverseForward_backward (u : transverseDerivatives T hT m) :
    transverseForward T hT Q Q₁ hd m hTangent
      (transverseBackward T hT Q Q₁ c hc hQ hd m u) = u := by
  apply Subtype.ext
  exact coordinateDerivative_reconstruct T hT Q Q₁ c hc hQ hd m hRange u

/-- A proved bounded linear equivalence to a parameter-independent Hilbert space. -/
def transverseEquiv : zeroTraceDerivatives (U := U) T hT ≃L[ℝ] transverseDerivatives T hT m where
  toLinearEquiv :=
    { toFun := transverseForward T hT Q Q₁ hd m hTangent
      invFun := transverseBackward T hT Q Q₁ c hc hQ hd m
      left_inv := transverseBackward_forward T hT Q Q₁ c hc hQ hd m hTangent
      right_inv := transverseForward_backward T hT Q Q₁ c hc hQ hd m hTangent hRange
      map_add' := map_add _
      map_smul' := map_smul _ }
  continuous_toFun := (transverseForward T hT Q Q₁ hd m hTangent).continuous
  continuous_invFun := (transverseBackward T hT Q Q₁ c hc hQ hd m).continuous

end EulerTimeH1FrameTransport
