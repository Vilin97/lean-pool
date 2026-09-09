/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSpaceInverse
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientMap
public import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveParameter
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse

@[expose] public section

/-!
# Actual all-order parameter regularity of the transverse inverse

The fixed Hilbert-space operator is assembled from the prescribed coefficient
paths and their true Bochner multipliers. Its coercive inverse is the previously
constructed transverse solution. Smoothness of every finite order follows from
coefficient smoothness; no regularity of a pre-existing inverse is assumed.
-/

noncomputable section

open scoped ContDiff

namespace EulerTransverseParameterRegularity

open Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTimeH1FrameTransport EulerTimeLpCoefficientMap
  EulerTransverseVariationalInverse EulerTransverseGramInverse
  EulerTransverseCoordinateRegularity EulerTransverseFixedSpaceInverse
  EulerCoerciveProjection EulerHilbertCoerciveParameter

variable {P U E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  {n : ℕ∞ω}

/-- Adjoint regularity with both operator spaces fixed before composition. -/
theorem contDiff_adjoint {A : P → U →L[ℝ] E} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => (A x).adjoint) := by
  have hAdj : ContDiff ℝ n (realAdjoint (U := U) (E := E)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := U →L[ℝ] E) (F := E →L[ℝ] U) _
  exact hAdj.comp hA

omit [CompleteSpace U] [CompleteSpace E] in
/-- Parameter regularity of the actual H¹ physical derivative map. -/
theorem contDiff_fixedFrameDerivative (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) :
    ContDiff ℝ n (fun x => fixedFrameDerivative T hT (Q x) (Q₁ x)) := by
  exact (contDiff_productDerivative T hT Q Q₁ hQ hQ₁).clm_comp contDiff_const

omit [CompleteSpace U] [CompleteSpace E] in
/-- Parameter regularity of the actual physical displacement map. -/
theorem contDiff_fixedFramePrimitive (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) :
    ContDiff ℝ n (fun x => fixedFramePrimitive T hT (Q x) (Q₁ x)) := by
  exact contDiff_const.clm_comp (contDiff_fixedFrameDerivative T hT Q Q₁ hQ hQ₁)

/-- Parameter regularity of the genuine transported form on the fixed space. -/
theorem contDiff_fixedFrameOperator (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hH : ContDiff ℝ n H) :
    ContDiff ℝ n (fun x => fixedFrameOperator T hT (Q x) (Q₁ x) (H x)) := by
  have hD := contDiff_fixedFrameDerivative T hT Q Q₁ hQ hQ₁
  have hA : ContDiff ℝ n (fun x => dirichletOperator (primitiveTimeLp T hT)
      (timeMultiplier T hT (H x))) := by
    exact contDiff_const.sub
      (contDiff_const.clm_comp ((contDiff_timeMultiplier T hT H hH).clm_comp contDiff_const))
  exact ((realAdjoint (U := zeroTraceDerivatives (U := U) T hT)
    (E := TimeLp T E)).contDiff.comp hD).clm_comp (hA.clm_comp hD)

variable (c : ℝ) (hc : 0 < c)
  (hLower : ∀ x t v, c * ‖v‖^2 ≤ ‖Q x t v‖^2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖^2)
  (hsmall : K * (T^2/2) ≤ 1/2)

/-- The actual fixed-space forcing-to-solution operator has every prescribed
order of coefficient regularity, including smoothness. -/
theorem contDiff_fixedFrameSolver (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hH : ContDiff ℝ n H) :
    ContDiff ℝ n (fun x =>
      fixedFrameSolver T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
        K hK (hPotential x) hsmall) := by
  have hA := contDiff_fixedFrameOperator T hT Q Q₁ H hQ hQ₁ hH
  have hi := contDiff_coerciveInverse_variable
    (fun x => fixedFrameOperator T hT (Q x) (Q₁ x) (H x))
    (fun x => fixedCoercivity T (Q x) (Q₁ x) c)
    (fun x => fixedCoercivity_pos T hT (Q x) (Q₁ x) c hc)
    (fun x => fixedFrameOperator_coercive T hT (Q x) (Q₁ x) (H x)
      c hc (hLower x) (hd x) K hK (hPotential x) hsmall) hA
  have hZ := contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁
  exact hi.clm_comp (contDiff_adjoint hZ).neg

/-- Actual parameter regularity for a parameterized forcing. -/
theorem contDiff_fixedFrameSolution (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hH : ContDiff ℝ n H) (f : P → TimeLp T E) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x =>
      fixedFrameSolver T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
        K hK (hPotential x) hsmall (f x)) :=
  (contDiff_fixedFrameSolver T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH).clm_apply
    hf

include hd in
/-- The coordinates of the original physical transverse solve inherit the
proved parameter regularity through equality with the fixed-space inverse. -/
theorem contDiff_transverse_coordinates
    (m : P → Icc (0 : ℝ) T → E)
    (hTangent : ∀ x t v, ⟪m x t, Q x t v⟫_ℝ = 0)
    (hRange : ∀ x t η, ⟪m x t, η⟫_ℝ = 0 → ∃ v : U, Q x t v = η)
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)
    (f : P → TimeLp T E) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => coordinateDerivative T hT (Q x) (Q₁ x) c hc (hLower x)
      (transverseSolver T hT (m x) (H x) K hK (hPotential x) hsmall (f x) : TimeLp T E)) := by
  have hsol := (zeroTraceDerivatives (U := U) T hT).subtypeL.contDiff.comp
    (contDiff_fixedFrameSolution T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f hf)
  convert hsol using 1
  funext x
  have heq := fixedFrameSolver_eq_transverse T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
    K hK (hPotential x) hsmall (m x) (hTangent x) (hRange x) (f x)
  exact congrArg (fun v : zeroTraceDerivatives (U := U) T hT => (v : TimeLp T U)) heq.symm

include hd in
/-- The physical velocity of the original constructed inverse has the actual
parameter regularity of the prescribed frame and forcing. -/
theorem contDiff_transverse_velocity
    (m : P → Icc (0 : ℝ) T → E)
    (hTangent : ∀ x t v, ⟪m x t, Q x t v⟫_ℝ = 0)
    (hRange : ∀ x t η, ⟪m x t, η⟫_ℝ = 0 → ∃ v : U, Q x t v = η)
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)
    (f : P → TimeLp T E) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => timeMultiplier T hT (Q x)
      (coordinateDerivative T hT (Q x) (Q₁ x) c hc (hLower x)
        (transverseSolver T hT (m x) (H x) K hK (hPotential x) hsmall (f x) : TimeLp T E))) :=
  (contDiff_timeMultiplier T hT Q hQ).clm_apply
    (contDiff_transverse_coordinates T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
      m hTangent hRange hQ hQ₁ hH f hf)

end EulerTransverseParameterRegularity
