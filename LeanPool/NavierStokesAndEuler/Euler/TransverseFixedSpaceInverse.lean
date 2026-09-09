/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1FrameTransport

@[expose] public section

/-!
# The actual transverse inverse on a fixed Hilbert space

The domain is the kernel of the ordinary time initial-trace operator, independent
of the spatial label, angle, or frame. The transported form and its actual
coercive inverse are constructed here and identified with the original physical
transverse solve. This is the fixed-space starting point for parameter estimates.
-/

noncomputable section

namespace EulerTransverseFixedSpaceInverse

open Set InnerProductSpace ContinuousLinearMap MeasureTheory
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTimeH1FrameTransport EulerCoerciveProjection
  EulerTransverseVariationalInverse EulerTransverseCoordinateRegularity

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

/-- The actual physical derivative associated to a fixed zero-trace coordinate derivative. -/
def fixedFrameDerivative : zeroTraceDerivatives (U := U) T hT →L[ℝ] TimeLp T E :=
  (productDerivative T hT Q Q₁).comp (zeroTraceDerivatives (U := U) T hT).subtypeL

/-- The actual physical displacement associated to a fixed coordinate derivative. -/
def fixedFramePrimitive : zeroTraceDerivatives (U := U) T hT →L[ℝ] TimeLp T E :=
  (primitiveTimeLp T hT).comp (fixedFrameDerivative T hT Q Q₁)

/-- The transported Dirichlet operator on the fixed coordinate Hilbert space. -/
def fixedFrameOperator :
    zeroTraceDerivatives (U := U) T hT →L[ℝ] zeroTraceDerivatives (U := U) T hT :=
  (fixedFrameDerivative T hT Q Q₁).adjoint.comp
    ((dirichletOperator (primitiveTimeLp T hT) (timeMultiplier T hT H)).comp
      (fixedFrameDerivative T hT Q Q₁))

/-- The transported operator has exactly the source displacement form. -/
theorem fixedFrameOperator_inner (u v : zeroTraceDerivatives (U := U) T hT) :
    ⟪fixedFrameOperator T hT Q Q₁ H u, v⟫_ℝ =
      ⟪fixedFrameDerivative T hT Q Q₁ u, fixedFrameDerivative T hT Q Q₁ v⟫_ℝ -
      ⟪timeMultiplier T hT H (fixedFramePrimitive T hT Q Q₁ u),
        fixedFramePrimitive T hT Q Q₁ v⟫_ℝ := by
  change ⟪(fixedFrameDerivative T hT Q Q₁).adjoint
    (dirichletOperator (primitiveTimeLp T hT) (timeMultiplier T hT H)
      (fixedFrameDerivative T hT Q Q₁ u)), v⟫_ℝ = _
  rw [adjoint_inner_left, dirichletOperator_inner]
  rfl

variable (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖^2 ≤ ‖Q t x‖^2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖^2)
  (hsmall : K * (T^2/2) ≤ 1/2)

/-- A polynomial quantitative coercivity constant on the fixed coordinate space. -/
def fixedCoercivity : ℝ := (transportCost T Q Q₁ c)⁻¹ ^ 2 / 2

omit [CompleteSpace U] [CompleteSpace E] in
include hT hc in
/-- The transported coercivity constant is strictly positive. -/
theorem fixedCoercivity_pos : 0 < fixedCoercivity T Q Q₁ c := by
  unfold fixedCoercivity
  exact div_pos (pow_pos (inv_pos.mpr (transportCost_pos T hT Q Q₁ c hc)) 2) (by norm_num)

include hc hQ hd K hK hH hsmall in
/-- The actual transported form is coercive, with a proved coefficient-only constant. -/
theorem fixedFrameOperator_coercive (v : zeroTraceDerivatives (U := U) T hT) :
    fixedCoercivity T Q Q₁ c * ‖v‖^2 ≤ ⟪fixedFrameOperator T hT Q Q₁ H v, v⟫_ℝ := by
  have hlow := productDerivative_norm_sq_lower T hT Q Q₁ c hc hQ hd (v : TimeLp T U)
  have hphys := dirichletOperator_coercive (primitiveTimeLp T hT) (timeMultiplier T hT H)
    (T^2/2) K hK (primitiveTimeLp_norm_sq_le T hT)
    (timeMultiplier_quadratic_upper T hT H K hH) hsmall (fixedFrameDerivative T hT Q Q₁ v)
  calc
    fixedCoercivity T Q Q₁ c * ‖v‖^2 =
        (1/2 : ℝ) * ((transportCost T Q Q₁ c)⁻¹ ^ 2 * ‖v‖^2) := by
      unfold fixedCoercivity
      ring
    _ ≤ (1/2 : ℝ) * ‖fixedFrameDerivative T hT Q Q₁ v‖^2 :=
      mul_le_mul_of_nonneg_left hlow (by norm_num)
    _ ≤ ⟪fixedFrameOperator T hT Q Q₁ H v, v⟫_ℝ := by
      change _ ≤ ⟪(fixedFrameDerivative T hT Q Q₁).adjoint
        (dirichletOperator (primitiveTimeLp T hT) (timeMultiplier T hT H)
          (fixedFrameDerivative T hT Q Q₁ v)), v⟫_ℝ
      rw [adjoint_inner_left]
      exact hphys

/-- The genuine fixed-space inverse, constructed from the transported coercive form. -/
def fixedFrameSolver : TimeLp T E →L[ℝ] zeroTraceDerivatives (U := U) T hT :=
  (coerciveInverse (fixedFrameOperator T hT Q Q₁ H) (fixedCoercivity T Q Q₁ c)
    (fixedCoercivity_pos T hT Q Q₁ c hc)
    (fixedFrameOperator_coercive T hT Q Q₁ H c hc hQ hd K hK hH hsmall)).comp
      (-(fixedFramePrimitive T hT Q Q₁).adjoint)

/-- The actual fixed-space solution obeys the entire source variational form. -/
theorem fixedFrameSolver_weak (f : TimeLp T E) (v : zeroTraceDerivatives (U := U) T hT) :
    let u := fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f
    ⟪fixedFrameDerivative T hT Q Q₁ u, fixedFrameDerivative T hT Q Q₁ v⟫_ℝ -
      ⟪timeMultiplier T hT H (fixedFramePrimitive T hT Q Q₁ u),
        fixedFramePrimitive T hT Q Q₁ v⟫_ℝ = -⟪f, fixedFramePrimitive T hT Q Q₁ v⟫_ℝ := by
  dsimp only
  rw [← fixedFrameOperator_inner]
  change ⟪fixedFrameOperator T hT Q Q₁ H
    (coerciveInverse (fixedFrameOperator T hT Q Q₁ H) (fixedCoercivity T Q Q₁ c)
      (fixedCoercivity_pos T hT Q Q₁ c hc)
      (fixedFrameOperator_coercive T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
      (-(fixedFramePrimitive T hT Q Q₁).adjoint f)), v⟫_ℝ = _
  rw [operator_inverse_apply, inner_neg_left, adjoint_inner_left]

/-- The fixed-space variational inverse is unique. -/
theorem fixedFrameSolver_unique (f : TimeLp T E) (u : zeroTraceDerivatives (U := U) T hT)
    (hu : ∀ v : zeroTraceDerivatives (U := U) T hT,
      ⟪fixedFrameDerivative T hT Q Q₁ u, fixedFrameDerivative T hT Q Q₁ v⟫_ℝ -
        ⟪timeMultiplier T hT H (fixedFramePrimitive T hT Q Q₁ u),
          fixedFramePrimitive T hT Q Q₁ v⟫_ℝ = -⟪f, fixedFramePrimitive T hT Q Q₁ v⟫_ℝ) :
    u = fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f := by
  apply (coerciveEquiv (fixedFrameOperator T hT Q Q₁ H) (fixedCoercivity T Q Q₁ c)
    (fixedCoercivity_pos T hT Q Q₁ c hc)
    (fixedFrameOperator_coercive T hT Q Q₁ H c hc hQ hd K hK hH hsmall)).injective
  simp only [coerciveEquiv_apply]
  apply ext_inner_right ℝ
  intro v
  rw [fixedFrameOperator_inner, hu, fixedFrameOperator_inner, fixedFrameSolver_weak]

/-- The new fixed-space inverse is exactly the coordinates of the original
physical transverse solve, rather than a separate unconnected construction. -/
theorem fixedFrameSolver_eq_transverse (m : Icc (0 : ℝ) T → E)
    (hTangent : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (f : TimeLp T E) :
    fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f =
      transverseBackward T hT Q Q₁ c hc hQ hd m
        (transverseSolver T hT m H K hK hH hsmall f) := by
  symm
  apply fixedFrameSolver_unique T hT Q Q₁ H c hc hQ hd K hK hH hsmall
  intro v
  let u := transverseSolver T hT m H K hK hH hsmall f
  have h := transverseSolver_weak T hT m H K hK hH hsmall f
    (transverseForward T hT Q Q₁ hd m hTangent v)
  have hu := congrArg (fun z : transverseDerivatives T hT m => (z : TimeLp T E))
    (transverseForward_backward T hT Q Q₁ c hc hQ hd m hTangent hRange u)
  change fixedFrameDerivative T hT Q Q₁ (transverseBackward T hT Q Q₁ c hc hQ hd m u) =
    (u : TimeLp T E) at hu
  change ⟪fixedFrameDerivative T hT Q Q₁ (transverseBackward T hT Q Q₁ c hc hQ hd m u),
      fixedFrameDerivative T hT Q Q₁ v⟫_ℝ -
    ⟪timeMultiplier T hT H (primitiveTimeLp T hT
        (fixedFrameDerivative T hT Q Q₁ (transverseBackward T hT Q Q₁ c hc hQ hd m u))),
      fixedFramePrimitive T hT Q Q₁ v⟫_ℝ = _
  rw [hu]
  exact h

end EulerTransverseFixedSpaceInverse
