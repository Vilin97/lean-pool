/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.InitialH1OperatorProduct
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveParameter
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientMap
import LeanPool.NavierStokesAndEuler.Euler.TransverseParameterRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSpaceInverse
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy

/-!
Actual parameter regularity of the nonzero-terminal transverse inverse.
The initial-zero energy and fixed-coordinate correction depend smoothly on
the coefficient paths.  An explicit affine coordinate trial implements the
same terminal coordinate at neighboring labels.
-/

section

/-!
The nonzero-terminal variational inverse on the same fixed coordinate Hilbert
space used by the packet inverse.  The zero-trace correction is an actual
coercive solve.  Full-range frame transport proves exact equality with the
physical endpoint solution, rather than introducing a second unrelated solve.
-/

@[expose] public section

noncomputable section

namespace EulerTransverseFixedEndpoint

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerCoerciveProjection
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTransverseVariationalInverse EulerTransverseFixedSpaceInverse
  EulerTransverseEndpointEnergy

variable {U E V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

include hd in
theorem fixedFrameDerivative_trace_zero (v : zeroTraceDerivatives (U := U) T hT) :
    initialTrace T hT (fixedFrameDerivative T hT Q Q₁ v) = 0 := by
  have hv : initialTrace T hT (v : TimeLp T U) = 0 := v.property
  change initialTrace T hT (productDerivative T hT Q Q₁ (v : TimeLp T U)) = 0
  rw [initialTrace_productDerivative T hT Q Q₁ hd, hv, map_zero]

include hd in
/-- The fixed coordinate form is exactly the restriction of the physical initial-zero form. -/
theorem fixedFrame_energy (u v : zeroTraceDerivatives (U := U) T hT) :
    ⟪energyOperator T hT H (fixedFrameDerivative T hT Q Q₁ u),
      fixedFrameDerivative T hT Q Q₁ v⟫_ℝ =
        ⟪fixedFrameOperator T hT Q Q₁ H u, v⟫_ℝ := by
  rw [energyOperator_inner, fixedFrameOperator_inner,
    initialPrimitiveTimeLp_eq_primitive_of_trace_zero T hT _
      (fixedFrameDerivative_trace_zero T hT Q Q₁ hd u),
    initialPrimitiveTimeLp_eq_primitive_of_trace_zero T hT _
      (fixedFrameDerivative_trace_zero T hT Q Q₁ hd v)]
  rfl

/-- Fixed endpoint correction as an element of `V →L[ℝ] zeroTraceDerivatives (U := U) T hT`. -/
def fixedEndpointCorrection (L : V →L[ℝ] TimeLp T E) :
    V →L[ℝ] zeroTraceDerivatives (U := U) T hT :=
  (coerciveInverse (fixedFrameOperator T hT Q Q₁ H) (fixedCoercivity T Q Q₁ c)
    (fixedCoercivity_pos T hT Q Q₁ c hc)
    (fixedFrameOperator_coercive T hT Q Q₁ H c hc hQ hd K hK hH hsmall)).comp
      ((fixedFrameDerivative T hT Q Q₁).adjoint.comp ((energyOperator T hT H).comp L))

/-- Fixed endpoint derivative, given by `L - (fixedFrameDerivative T hT Q Q₁).comp
(fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall L)`. -/
def fixedEndpointDerivative (L : V →L[ℝ] TimeLp T E) : V →L[ℝ] TimeLp T E :=
  L - (fixedFrameDerivative T hT Q Q₁).comp
    (fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall L)

theorem fixedEndpointCorrection_equation (L : V →L[ℝ] TimeLp T E) (Y : V)
    (v : zeroTraceDerivatives (U := U) T hT) :
    ⟪energyOperator T hT H (fixedFrameDerivative T hT Q Q₁
        (fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y)),
      fixedFrameDerivative T hT Q Q₁ v⟫_ℝ =
        ⟪energyOperator T hT H (L Y), fixedFrameDerivative T hT Q Q₁ v⟫_ℝ := by
  rw [fixedFrame_energy T hT Q Q₁ H hd]
  change ⟪fixedFrameOperator T hT Q Q₁ H
    (coerciveInverse (fixedFrameOperator T hT Q Q₁ H) (fixedCoercivity T Q Q₁ c)
      (fixedCoercivity_pos T hT Q Q₁ c hc)
      (fixedFrameOperator_coercive T hT Q Q₁ H c hc hQ hd K hK hH hsmall)
      ((fixedFrameDerivative T hT Q Q₁).adjoint (energyOperator T hT H (L Y)))), v⟫_ℝ = _
  rw [operator_inverse_apply, adjoint_inner_left]

theorem fixedEndpointDerivative_orthogonal (L : V →L[ℝ] TimeLp T E) (Y : V)
    (v : zeroTraceDerivatives (U := U) T hT) :
    ⟪energyOperator T hT H (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y),
      fixedFrameDerivative T hT Q Q₁ v⟫_ℝ = 0 := by
  change ⟪energyOperator T hT H (L Y - fixedFrameDerivative T hT Q Q₁
    (fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y)), _⟫_ℝ = 0
  rw [map_sub, inner_sub_left, fixedEndpointCorrection_equation, sub_self]

variable (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
  (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)

include hm in
theorem fixedEndpointDerivative_sub_mem (L : V →L[ℝ] TimeLp T E) (Y : V) :
    fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y - L Y ∈
      transverseDerivatives T hT m := by
  let r := fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y
  have hr : fixedFrameDerivative T hT Q Q₁ r ∈ transverseDerivatives T hT m :=
    (transverseForward T hT Q Q₁ hd m hm r).property
  have he : fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y - L Y =
      -(fixedFrameDerivative T hT Q Q₁ r) := by
    change (L Y - fixedFrameDerivative T hT Q Q₁ r) - L Y = _
    abel
  rw [he]
  exact (transverseDerivatives T hT m).neg_mem hr

include hm hRange in
theorem fixedEndpointDerivative_physical_orthogonal (L : V →L[ℝ] TimeLp T E) (Y : V)
    (v : transverseDerivatives T hT m) :
    ⟪energyOperator T hT H (fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y),
      (v : TimeLp T E)⟫_ℝ = 0 := by
  have hv := congrArg (fun z : transverseDerivatives T hT m => (z : TimeLp T E))
    (transverseForward_backward T hT Q Q₁ c hc hQ hd m hm hRange v)
  change fixedFrameDerivative T hT Q Q₁ (transverseBackward T hT Q Q₁ c hc hQ hd m v) =
    (v : TimeLp T E) at hv
  rw [← hv]
  exact fixedEndpointDerivative_orthogonal T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y _

include hm hRange in
/-- The fixed-space solve is the same nonzero-terminal inverse used by activation. -/
theorem fixedEndpointDerivative_eq_endpoint (L : V →L[ℝ] TimeLp T E) :
    fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L =
      endpointDerivative T hT m H K hK hH hsmall L := by
  apply ContinuousLinearMap.ext
  intro Y
  let u := fixedEndpointDerivative T hT Q Q₁ H c hc hQ hd K hK hH hsmall L Y
  let w := endpointDerivative T hT m H K hK hH hsmall L Y
  have hdiff : u - w ∈ transverseDerivatives T hT m := by
    have h₁ := fixedEndpointDerivative_sub_mem T hT Q Q₁ H c hc hQ hd K hK hH hsmall m hm L Y
    have h₂ := endpointDerivative_sub_mem T hT m H K hK hH hsmall L Y
    have hh := (transverseDerivatives T hT m).sub_mem h₁ h₂
    have he : (u - L Y) - (w - L Y) = u - w := by abel
    exact he ▸ hh
  let d : transverseDerivatives T hT m := ⟨u - w, hdiff⟩
  have hu : ⟪energyOperator T hT H u, (d : TimeLp T E)⟫_ℝ = 0 :=
    fixedEndpointDerivative_physical_orthogonal T hT Q Q₁ H c hc hQ hd K hK hH hsmall m hm hRange L
        Y d
  have hw : ⟪energyOperator T hT H w, (d : TimeLp T E)⟫_ℝ = 0 := by
    rw [energyOperator_inner, initialPrimitiveTimeLp_transverse T hT m d]
    exact endpointDerivative_weak T hT m H K hK hH hsmall L Y d
  have hz : ⟪energyOperator T hT H (u - w), u - w⟫_ℝ = 0 := by
    change ⟪energyOperator T hT H (u - w), (d : TimeLp T E)⟫_ℝ = 0
    rw [map_sub, inner_sub_left, hu, hw, sub_zero]
  have hc' := energyOperator_coercive T hT H K hK hH hsmall (u - w)
  rw [hz] at hc'
  have hn : ‖u - w‖ = 0 := by nlinarith only [hc', norm_nonneg (u - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end EulerTransverseFixedEndpoint

end
end

end

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
