/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedEndpoint
public import LeanPool.NavierStokesAndEuler.Euler.InitialH1OperatorProduct
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveParameter
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientMap
import LeanPool.NavierStokesAndEuler.Euler.TransverseParameterRegularity

/-!
Actual parameter regularity of the nonzero-terminal transverse inverse.
The initial-zero energy and fixed-coordinate correction depend smoothly on
the coefficient paths.  An explicit affine coordinate trial implements the
same terminal coordinate at neighboring labels.
-/

@[expose] public section


noncomputable section


namespace EulerTransverseEndpointParameter

open Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTimeLpCoefficientMap EulerTransverseVariationalInverse EulerTransverseGramInverse
  EulerTransverseFixedSpaceInverse EulerTransverseParameterRegularity
  EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerCoerciveProjection EulerHilbertCoerciveParameter
open scoped ContDiff

variable {P U E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  {n : ℕ∞ω}

theorem contDiff_initialEnergy (hH : ContDiff ℝ n H) :
    ContDiff ℝ n (fun x => energyOperator T hT (H x)) :=
  contDiff_const.sub
    (contDiff_const.clm_comp ((contDiff_timeMultiplier T hT H hH).clm_comp contDiff_const))

omit [CompleteSpace U] [CompleteSpace E] in
theorem contDiff_initialProductDerivative (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) :
    ContDiff ℝ n (fun x => initialProductDerivative T hT (Q x) (Q₁ x)) :=
  ((contDiff_timeMultiplier T hT Q₁ hQ₁).clm_comp contDiff_const).add
    (contDiff_timeMultiplier T hT Q hQ)

variable (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

theorem contDiff_fixedEndpointCorrection
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)
    (L : P → V →L[ℝ] TimeLp T E) (hL : ContDiff ℝ n L) :
    ContDiff ℝ n (fun x => fixedEndpointCorrection T hT (Q x) (Q₁ x) (H x)
      c hc (hLower x) (hd x) K hK (hPotential x) hsmall (L x)) := by
  have hA := contDiff_fixedFrameOperator T hT Q Q₁ H hQ hQ₁ hH
  have hi := contDiff_coerciveInverse_variable
    (fun x => fixedFrameOperator T hT (Q x) (Q₁ x) (H x))
    (fun x => fixedCoercivity T (Q x) (Q₁ x) c)
    (fun x => fixedCoercivity_pos T hT (Q x) (Q₁ x) c hc)
    (fun x => fixedFrameOperator_coercive T hT (Q x) (Q₁ x) (H x)
      c hc (hLower x) (hd x) K hK (hPotential x) hsmall) hA
  have hD := contDiff_fixedFrameDerivative T hT Q Q₁ hQ hQ₁
  have hE := contDiff_initialEnergy T hT H hH
  exact hi.clm_comp ((contDiff_adjoint hD).clm_comp (hE.clm_comp hL))

theorem contDiff_fixedEndpointDerivative
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)
    (L : P → V →L[ℝ] TimeLp T E) (hL : ContDiff ℝ n L) :
    ContDiff ℝ n (fun x => fixedEndpointDerivative T hT (Q x) (Q₁ x) (H x)
      c hc (hLower x) (hd x) K hK (hPotential x) hsmall (L x)) :=
  hL.sub ((contDiff_fixedFrameDerivative T hT Q Q₁ hQ hQ₁).clm_comp
    (contDiff_fixedEndpointCorrection T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
      hQ hQ₁ hH L hL))

include c hc hLower hd in
/-- The physical endpoint solution inherits the proved parameter regularity. -/
theorem contDiff_endpointDerivative
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)
    (L : P → V →L[ℝ] TimeLp T E) (hL : ContDiff ℝ n L)
    (m : P → Icc (0 : ℝ) T → E) (hm : ∀ x t v, ⟪m x t, Q x t v⟫_ℝ = 0)
    (hRange : ∀ x t η, ⟪m x t, η⟫_ℝ = 0 → ∃ v : U, Q x t v = η) :
    ContDiff ℝ n (fun x => endpointDerivative T hT (m x) (H x)
      K hK (hPotential x) hsmall (L x)) := by
  have he : (fun x => endpointDerivative T hT (m x) (H x)
      K hK (hPotential x) hsmall (L x)) =
      (fun x => fixedEndpointDerivative T hT (Q x) (Q₁ x) (H x)
        c hc (hLower x) (hd x) K hK (hPotential x) hsmall (L x)) := by
    funext x
    exact (fixedEndpointDerivative_eq_endpoint T hT (Q x) (Q₁ x) (H x)
      c hc (hLower x) (hd x) K hK (hPotential x) hsmall (m x) (hm x) (hRange x) (L x)).symm
  rw [he]
  exact contDiff_fixedEndpointDerivative T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
    hQ hQ₁ hH L hL

section AffineTrial

variable (A A₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))

/-- The exact derivative of `(t/T) Q(t) ξT`. -/
def affineTrial : U →L[ℝ] TimeLp T E :=
  (initialProductDerivative T hT A A₁).comp
    ((constantFieldOperator T hT).comp (T⁻¹ • ContinuousLinearMap.id ℝ U))

theorem affineTrial_primitive
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (ξT : U) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (affineTrial T hT A A₁ ξT) t =
      A t (((t : ℝ) / T) • ξT) := by
  change initialPrimitive T hT
    (initialProductDerivative T hT A A₁ (constantFieldOperator T hT (T⁻¹ • ξT))) t = _
  rw [initialPrimitive_initialProductDerivative T hT A A₁ hA,
    initialPrimitive_constantFieldOperator, smul_smul, div_eq_mul_inv]

theorem affineTrial_terminal (hTpos : 0 < T)
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (ξT : U) :
    initialPrimitive T hT (affineTrial T hT A A₁ ξT) ⟨T, hT, le_rfl⟩ =
      A ⟨T, hT, le_rfl⟩ ξT := by
  rw [affineTrial_primitive T hT A A₁ hA, div_self hTpos.ne', one_smul]

theorem affineTrial_tangent
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t v, ⟪m t, A t v⟫_ℝ = 0)
    (ξT : U) (t : Icc (0 : ℝ) T) :
    ⟪m t, initialPrimitive T hT (affineTrial T hT A A₁ ξT) t⟫_ℝ = 0 := by
  rw [affineTrial_primitive T hT A A₁ hA]
  exact hm t _

end AffineTrial

omit [CompleteSpace U] [CompleteSpace E] in
theorem contDiff_affineTrial (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) :
    ContDiff ℝ n (fun x => affineTrial T hT (Q x) (Q₁ x)) :=
  (contDiff_initialProductDerivative T hT Q Q₁ hQ hQ₁).clm_comp contDiff_const

include c hc hLower hd in
/-- Neighboring labels use precisely the same terminal coordinate, and the
resulting physical derivatives have the coefficient parameter regularity. -/
theorem contDiff_affineEndpoint
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)
    (m : P → Icc (0 : ℝ) T → E) (hm : ∀ x t v, ⟪m x t, Q x t v⟫_ℝ = 0)
    (hRange : ∀ x t η, ⟪m x t, η⟫_ℝ = 0 → ∃ v : U, Q x t v = η) (ξT : U) :
    ContDiff ℝ n (fun x => endpointDerivative T hT (m x) (H x)
      K hK (hPotential x) hsmall (affineTrial T hT (Q x) (Q₁ x)) ξT) :=
  (contDiff_endpointDerivative T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
    hQ hQ₁ hH (fun x => affineTrial T hT (Q x) (Q₁ x))
    (contDiff_affineTrial T hT Q Q₁ hQ hQ₁) m hm hRange).clm_apply contDiff_const

end EulerTransverseEndpointParameter
