/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointData
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointParameter
import LeanPool.NavierStokesAndEuler.Euler.TimeH1WeakPairing

/-!
The actual cylinder endpoint inverse is affine data minus the genuine
zero-endpoint inverse of its explicit forcing. These identities transfer
the already proved support, translation and same-radius estimates to the
nonzero-terminal construction.
-/

section

/-!
# The affine endpoint correction as an actual forced Dirichlet solve

For the affine coordinate lift `t Y / T`, the Jacobi identity cancels the
potential term. Its variational correction is exactly the already
constructed zero-endpoint inverse applied to `2 Q₁(t) (Y/T)`.
-/

@[expose] public section

noncomputable section

namespace EulerFixedEndpointForcing

open Set MeasureTheory ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerTransverseFixedSpaceInverse EulerTransverseEndpointParameter
   EulerContinuousTimeIntegral
  EulerTimeH1WeakPairing

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

omit [CompleteSpace U] [CompleteSpace E] in
/-- Affine velocity as an element of `C(Icc (0 : ℝ) T,E)`. -/
def affineVelocity (Y : U) : C(Icc (0 : ℝ) T,E) :=
  ⟨fun t => Q₁ t ((t : ℝ) • (T⁻¹ • Y))+Q t (T⁻¹ • Y),
    (Q₁.continuous.clm_apply (continuous_subtype_val.smul continuous_const)).add
      (Q.continuous.clm_apply continuous_const)⟩

omit [CompleteSpace U] [CompleteSpace E] in
/-- Affine acceleration as an element of `C(Icc (0 : ℝ) T,E)`. -/
def affineAcceleration (Y : U) : C(Icc (0 : ℝ) T,E) :=
  ⟨fun t => Q₂ t ((t : ℝ) • (T⁻¹ • Y))+(2 : ℝ) • Q₁ t (T⁻¹ • Y),
    (Q₂.continuous.clm_apply (continuous_subtype_val.smul continuous_const)).add
      ((Q₁.continuous.clm_apply continuous_const).const_smul (2 : ℝ))⟩

omit [CompleteSpace U] [CompleteSpace E] in
/-- The genuine affine forcing, as a bounded linear function of terminal data. -/
def affineForcing : U →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (2 : ℝ) • (multiplier Q₁).comp
    ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)).comp (T⁻¹ • ContinuousLinearMap.id ℝ U))

omit [CompleteSpace E] in
theorem affineTrial_eq_pathLp (Y : U) :
    affineTrial T hT Q Q₁ Y = pathLp T hT (affineVelocity T Q Q₁ Y) := by
  apply Lp.ext
  filter_upwards [initialProductDerivative_ae T hT Q Q₁
      (constantFieldOperator T hT (T⁻¹ • Y)),constantFieldOperator_ae T hT (T⁻¹ • Y),
    pathLp_ae T hT (affineVelocity T Q Q₁ Y),ae_restrict_mem measurableSet_Icc]
      with t hd hc hp hm
  have hi := initialPrimitive_constantFieldOperator T hT (T⁻¹ • Y) ⟨t,hm⟩
  change initialRealPrimitive T (constantFieldOperator T hT (T⁻¹ • Y)) t = t • (T⁻¹ • Y) at hi
  change initialProductDerivative T hT Q Q₁ (constantFieldOperator T hT (T⁻¹ • Y)) t = _
  rw [hd,hp,hc,hi]
  simp only [extendPath,projIcc_of_mem hT hm]
  rfl

variable (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))

include hd hd₁ in
omit [CompleteSpace U] [CompleteSpace E] in
theorem affineVelocity_hasDerivWithinAt (Y : U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (affineVelocity T Q Q₁ Y))
      (affineAcceleration T Q₁ Q₂ Y t) (Icc (0 : ℝ) T) t := by
  have hlin : HasDerivWithinAt (fun s : ℝ => s • (T⁻¹ • Y)) (T⁻¹ • Y)
      (Icc (0 : ℝ) T) t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (t : ℝ)).smul_const (T⁻¹ •
        Y)).hasDerivWithinAt
  have h := ((hd₁ t).clm_apply hlin).add
    ((hd t).clm_apply (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (T⁻¹ • Y)))
  have he : Q₂ t ((t : ℝ) • (T⁻¹ • Y))+extendPath T hT Q₁ t (T⁻¹ • Y) +
      (Q₁ t (T⁻¹ • Y)+extendPath T hT Q t 0) = affineAcceleration T Q₁ Q₂ Y t := by
    simp only [extendPath,projIcc_of_mem hT t.property,map_zero,add_zero]
    change Q₂ t ((t : ℝ) • (T⁻¹ • Y))+Q₁ t (T⁻¹ • Y)+Q₁ t (T⁻¹ • Y) =
      Q₂ t ((t : ℝ) • (T⁻¹ • Y))+(2 : ℝ) • Q₁ t (T⁻¹ • Y)
    module
  apply (h.congr_deriv he).congr_of_mem _ t.property
  intro s hs
  simp only [Pi.add_apply,extendPath,projIcc_of_mem hT hs]
  rfl

include hd hframe in
theorem affineAcceleration_add_potential (Y : U) :
    pathLp T hT (affineAcceleration T Q₁ Q₂ Y) +
      timeMultiplier T hT H (initialPrimitiveTimeLp T hT (affineTrial T hT Q Q₁ Y)) =
        pathLp T hT (affineForcing T Q₁ Y) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (pathLp T hT (affineAcceleration T Q₁ Q₂ Y))
      (timeMultiplier T hT H (initialPrimitiveTimeLp T hT (affineTrial T hT Q Q₁ Y))),
    pathLp_ae T hT (affineAcceleration T Q₁ Q₂ Y),
    timeMultiplier_ae T hT H (initialPrimitiveTimeLp T hT (affineTrial T hT Q Q₁ Y)),
    initialPrimitiveTimeLp_ae T hT (affineTrial T hT Q Q₁ Y),
    pathLp_ae T hT (affineForcing T Q₁ Y),ae_restrict_mem measurableSet_Icc]
      with t ha hq hH hi hf hm
  have hp := affineTrial_primitive T hT Q Q₁ hd Y ⟨t,hm⟩
  change initialRealPrimitive T (affineTrial T hT Q Q₁ Y) t = Q ⟨t,hm⟩ ((t/T) • Y) at hp
  rw [ha,Pi.add_apply,hq,hH,hi,hf,hp]
  simp only [extendPath,projIcc_of_mem hT hm]
  change Q₂ ⟨t,hm⟩ (t • (T⁻¹ • Y))+(2 : ℝ) • Q₁ ⟨t,hm⟩ (T⁻¹ • Y) +
    H ⟨t,hm⟩ (Q ⟨t,hm⟩ ((t/T) • Y)) = (2 : ℝ) • Q₁ ⟨t,hm⟩ (T⁻¹ • Y)
  rw [hframe]
  simp only [neg_apply,comp_apply,div_eq_mul_inv,smul_smul]
  module

include hd hd₁ hframe in
/-- The exact affine energy pairing, obtained by genuine integration by parts. -/
theorem affine_energy_pairing (Y : U) (v : zeroTraceDerivatives (U := U) T hT) :
    ⟪energyOperator T hT H (affineTrial T hT Q Q₁ Y),fixedFrameDerivative T hT Q Q₁ v⟫_ℝ =
      -⟪pathLp T hT (affineForcing T Q₁ Y),fixedFramePrimitive T hT Q Q₁ v⟫_ℝ := by
  have hv := fixedFrameDerivative_trace_zero T hT Q Q₁ hd v
  have hw : ⟪affineTrial T hT Q Q₁ Y,fixedFrameDerivative T hT Q Q₁ v⟫_ℝ =
      -⟪pathLp T hT (affineAcceleration T Q₁ Q₂ Y),
        primitiveTimeLp T hT (fixedFrameDerivative T hT Q Q₁ v)⟫_ℝ := by
    rw [affineTrial_eq_pathLp]
    exact pathLp_inner_zero_trace T hT _ _
      (affineVelocity_hasDerivWithinAt T hT Q Q₁ Q₂ hd hd₁ Y) _ hv
  have he := congrArg (fun w : TimeLp T E =>
    ⟪w,primitiveTimeLp T hT (fixedFrameDerivative T hT Q Q₁ v)⟫_ℝ)
      (affineAcceleration_add_potential T hT Q Q₁ Q₂ H hd hframe Y)
  rw [inner_add_left] at he
  rw [energyOperator_inner,initialPrimitiveTimeLp_eq_primitive_of_trace_zero T hT _ hv,hw]
  change _ = -⟪pathLp T hT (affineForcing T Q₁ Y),
    primitiveTimeLp T hT (fixedFrameDerivative T hT Q Q₁ v)⟫_ℝ
  linarith only [he]

variable (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t v, ⟪H t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

include hd₁ hframe in
/-- The stationary affine correction is exactly the forced inverse applied
to the explicit source `2 Q₁ Y/T`; no new inverse is assumed. -/
theorem correction_eq_forced (Y : U) :
    fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      (affineTrial T hT Q Q₁) Y =
    fixedFrameSolver T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      (pathLp T hT (affineForcing T Q₁ Y)) := by
  apply fixedFrameSolver_unique T hT Q Q₁ H c hc hQ hd K hK hH hsmall
  intro v
  have he := fixedEndpointCorrection_equation T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    (affineTrial T hT Q Q₁) Y v
  rw [fixedFrame_energy T hT Q Q₁ H hd,fixedFrameOperator_inner] at he
  exact he.trans (affine_energy_pairing T hT Q Q₁ Q₂ H hd hd₁ hframe Y v)

end EulerFixedEndpointForcing

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerTimeLp
  EulerVolterraConvolution EulerTimeH1FrameTransport EulerTerminalTimePrimitive
  EulerInitialTimePrimitive EulerTransverseFixedEndpoint
  EulerTransverseEndpointParameter EulerTransverseEndpointCoordinates
  EulerFixedEndpointForcing EulerContinuousTimeIntegral

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : ℝ) [Fact (0 < P)] {T : ℝ} (D : Coefficients T U E)

/-- The exact forcing of the affine endpoint correction. -/
def endpointForcing : CylinderL2 P U →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P E) :=
  affineForcing T (D.frameDerivative P)

omit [CompleteSpace U] [CompleteSpace E] in
theorem endpointForcing_apply (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    D.endpointForcing P Y t = (2 : ℝ) • D.frameDerivative P t (T⁻¹ • Y) := rfl

/-- Equality of the genuinely constructed corrections, not a new solution assumption. -/
theorem endpointCorrection_eq_forced (Y : CylinderL2 P U) :
    D.endpointCorrection P Y = D.coordinateSolver P (pathLp T D.time_pos.le (D.endpointForcing P
        Y)) :=
  correction_eq_forced T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.frameSecond P)
    (D.hessian P) (D.frame_derivative P) (D.frame_second_derivative P) (D.frame_equation P)
    D.lower D.lower_pos (D.frame_lower P) D.potential D.potential_nonneg
    (D.hessian_upper P) D.small Y

theorem endpointSlope_eq_const_sub (Y : CylinderL2 P U) :
    D.endpointSlope P Y = constantFieldOperator T D.time_pos.le (T⁻¹ • Y) -
      D.velocityLp P (pathLp T D.time_pos.le (D.endpointForcing P Y)) := by
  change constantFieldOperator T D.time_pos.le (T⁻¹ • Y) -
    (D.endpointCorrection P Y : TimeLp T (CylinderL2 P U)) = _
  rw [D.endpointCorrection_eq_forced P Y]
  rfl

theorem endpointDisplacement_eq_affine_sub (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    D.endpointDisplacement P Y t = (t : ℝ) • (T⁻¹ • Y) -
      D.displacementPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t := by
  have hz : initialTrace T D.time_pos.le
      (D.velocityLp P (pathLp T D.time_pos.le (D.endpointForcing P Y))) = 0 :=
    (D.coordinateSolver P (pathLp T D.time_pos.le (D.endpointForcing P Y))).property
  change initialPrimitive T D.time_pos.le (D.endpointSlope P Y) t = _
  rw [D.endpointSlope_eq_const_sub P Y,map_sub,ContinuousMap.sub_apply,
    initialPrimitive_constantFieldOperator,initialPrimitive_eq_terminal_sub,
    hz,sub_zero]
  rfl

/-- Equality in continuous time follows from the true displacement
derivative, including the endpoint derivatives. -/
theorem endpointCoordinate_eq_const_sub (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    D.endpointCoordinate P Y t = T⁻¹ • Y -
      D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t := by
  have hc : HasDerivWithinAt (fun s : ℝ => s • (T⁻¹ • Y)) (T⁻¹ • Y)
      (Icc (0 : ℝ) T) t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (t : ℝ)).smul_const (T⁻¹ •
        Y)).hasDerivWithinAt
  have hh := hc.sub (D.displacement_hasDerivWithinAt P (D.endpointForcing P Y) t)
  have he : HasDerivWithinAt (extendPath T D.time_pos.le (D.endpointDisplacement P Y))
      (T⁻¹ • Y-D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t)
      (Icc (0 : ℝ) T) t := by
    apply hh.congr_of_mem _ t.property
    intro s hs
    simpa only [Pi.sub_apply,extendPath,projIcc_of_mem D.time_pos.le hs] using
      D.endpointDisplacement_eq_affine_sub P Y ⟨s,hs⟩
  exact ((D.endpointDisplacement_hasDerivWithinAt P Y t).derivWithin
    ((uniqueDiffOn_Icc D.time_pos) _ t.property)).symm.trans
      (he.derivWithin ((uniqueDiffOn_Icc D.time_pos) _ t.property))

theorem endpointCoordinate_eq_forced (Y : CylinderL2 P U) :
    D.endpointCoordinate P Y = ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y) -
      D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) := by
  apply ContinuousMap.ext
  intro t
  exact D.endpointCoordinate_eq_const_sub P Y t

theorem endpointAcceleration_eq_forced (Y : CylinderL2 P U) :
    D.endpointAcceleration P Y = -D.accelerationPath P (D.endpointForcing P Y) := by
  apply ContinuousMap.ext
  intro t
  have hh := (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (T⁻¹ • Y)).sub
    (D.velocity_hasDerivWithinAt P (D.endpointForcing P Y) t)
  have he : HasDerivWithinAt (extendPath T D.time_pos.le (D.endpointCoordinate P Y))
      (-D.accelerationPath P (D.endpointForcing P Y) t) (Icc (0 : ℝ) T) t := by
    apply (hh.congr_deriv (zero_sub _)).congr_of_mem _ t.property
    intro s hs
    simpa only [Pi.sub_apply,extendPath,projIcc_of_mem D.time_pos.le hs] using
      D.endpointCoordinate_eq_const_sub P Y ⟨s,hs⟩
  exact ((D.endpointCoordinate_hasDerivWithinAt P Y t).derivWithin
    ((uniqueDiffOn_Icc D.time_pos) _ t.property)).symm.trans
      (he.derivWithin ((uniqueDiffOn_Icc D.time_pos) _ t.property))

theorem endpointVelocity_eq_forced (Y : CylinderL2 P U) :
    D.endpointVelocity P Y =
      multiplier (D.frame P) (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y)) -
        D.physicalVelocity P (D.endpointForcing P Y) := by
  apply ContinuousMap.ext
  intro t
  change D.frame P t (D.endpointCoordinate P Y t) =
    D.frame P t (T⁻¹ • Y)-D.frame P t
      (D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t)
  rw [D.endpointCoordinate_eq_const_sub P Y t,map_sub]

theorem endpointDerivative_eq_forced (Y : CylinderL2 P U) :
    D.endpointDerivative P Y =
      multiplier (D.frameDerivative P) (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y)) -
        D.physicalDerivative P (D.endpointForcing P Y) := by
  apply ContinuousMap.ext
  intro t
  change D.frameDerivative P t (D.endpointCoordinate P Y t)+D.frame P t (D.endpointAcceleration P Y
      t) =
    D.frameDerivative P t (T⁻¹ • Y)-(D.frameDerivative P t
      (D.velocityPath P (pathLp T D.time_pos.le (D.endpointForcing P Y)) t) +
        D.frame P t (D.accelerationPath P (D.endpointForcing P Y) t))
  rw [D.endpointCoordinate_eq_const_sub P Y t,D.endpointAcceleration_eq_forced P Y,
    ContinuousMap.neg_apply,map_sub,map_neg]
  abel

end EulerCylinderDirichlet.Coefficients
