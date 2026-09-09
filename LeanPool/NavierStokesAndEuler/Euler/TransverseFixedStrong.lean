/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSpaceInverse
public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEquation

@[expose] public section

/-!
# The actual fixed-coordinate Dirichlet inverse satisfies the strong equation

This version uses the range of the frame directly. It applies to supported
spatial or cylinder L² spaces, where a pointwise transverse constraint must
not be replaced by orthogonality to a single Hilbert-space vector.
-/

noncomputable section

namespace EulerTransverseFixedStrong

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerTerminalTimePrimitive EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse
  EulerTransverseCoordinateRegularity EulerTransverseMomentumRegularity
  EulerTransverseStrongEquation EulerTransverseGramInverse

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T,U →L[ℝ] E)) (H : C(Icc (0 : ℝ) T,E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t v, ⟪H t v,v⟫_ℝ ≤ K*‖v‖^2)
  (hsmall : K*(T^2/2) ≤ 1/2)

/-- The actual derivative of the physical displacement from the fixed inverse. -/
def physicalDerivative : TimeLp T E →L[ℝ] TimeLp T E :=
  (fixedFrameDerivative T hT Q Q₁).comp
    (fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

theorem physicalDerivative_range (f : TimeLp T E) (t : Icc (0 : ℝ) T) :
    ∃ v : U, Q t v = realPrimitive T
      (physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) t := by
  let w := fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f
  refine ⟨terminalPrimitive T hT (w : TimeLp T U) t, ?_⟩
  exact (terminalPrimitive_productDerivative T hT Q Q₁ hd (w : TimeLp T U) t).symm

/-- The existing coordinate derivative is exactly the solved fixed-space field. -/
theorem coordinateDerivative_eq (f : TimeLp T E) :
    coordinateDerivative T hT Q Q₁ c hc hQ
      (physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) =
      (fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f : TimeLp T U) :=
  coordinateDerivative_productDerivative T hT Q Q₁ c hc hQ hd _

/-- Actual product tests supply the weak momentum identity for this inverse. -/
theorem momentum_weak (f : TimeLp T E) (v : TimeLp T U)
    (hv : initialTrace T hT v = 0) :
    ⟪momentum T hT Q (physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f),v⟫_ℝ =
      -⟪momentumForcing T hT Q Q₁ H
        (physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) f,
        primitiveTimeLp T hT v⟫_ℝ := by
  apply momentum_weak_of_product_tests T hT Q Q₁ hd H
    (physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) f v
  exact fixedFrameSolver_weak T hT Q Q₁ H c hc hQ hd K hK hH hsmall f ⟨v,hv⟩

variable (Q₂ : C(Icc (0 : ℝ) T,U →L[ℝ] E))
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))

include hd₁ hframe in
/-- A true H¹ coordinate velocity and equation (10) follow from the fixed
coercive solve. There is no assumed strong solution or ambient normal. -/
theorem exists_strong (hTpos : 0 < T) (f : TimeLp T E) :
    let u := physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f
    ∃ v : ℝ → U,
      AbsolutelyContinuousOnInterval v 0 T ∧
      (fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall f : ℝ → U) =ᵐ[timeMeasure T] v ∧
      (∀ᵐ t ∂timeMeasure T,
        HasDerivAt v (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) t) ∧
      ∀ᵐ t ∂timeMeasure T,
        gram (extendPath T hT Q t) (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) =
          (extendPath T hT Q t).adjoint (f t-(2 : ℝ) • extendPath T hT Q₁ t (v t)) := by
  let u := physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f
  obtain ⟨v,_,hv,hrep,_,hder,heq⟩ := exists_strong_of_weak_momentum T hT Q Q₁ Q₂ c hc hQ hd hd₁
    hTpos H u f (physicalDerivative_range T hT Q Q₁ H c hc hQ hd K hK hH hsmall f)
    hframe (momentum_weak T hT Q Q₁ H c hc hQ hd K hK hH hsmall f)
  refine ⟨v,hv,?_,hder,heq⟩
  change (coordinateDerivative T hT Q Q₁ c hc hQ
    (physicalDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall f) : ℝ → U) =ᵐ[timeMeasure T] v at
      hrep
  rw [coordinateDerivative_eq T hT Q Q₁ H c hc hQ hd K hK hH hsmall f] at hrep
  exact hrep

end EulerTransverseFixedStrong
