/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveLocalSmoothness

/-! Smooth parameter dependence from the actual local Volterra equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter
namespace AVenhance.Infra.Section4

/-- The substitution derivative is the actual pointwise primitive state
Jacobian operator, with no global derivative bound premise. -/
theorem amnrCurveJointCompose_hasFDerivAt_local {K E : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (η : C(K, ℝ)) (u : C(K, E)) :
    HasFDerivAt (amnrCurveJointCompose f hf.continuous η)
      (amnrCurveOperator (amnrCurveJointCompose (amnrStateDerivative f)
        (amnrStateDerivative_contDiff hf).continuous η u)) u := by
  have hh := (amnrCurveJointCompose_contDiff_infty_local hf η).differentiable (by simp) u
  convert hh.hasFDerivAt using 1
  ext v t
  exact (amnrCurveJointCompose_fderiv_eval_local hf η u v t).symm

/-- The actual residual is smooth on trajectories from local field smoothness. -/
theorem amnrCurveResidual_contDiff_infty_local {K E : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrCurveResidual f hf.continuous η V) := by
  convert contDiff_id.sub (V.contDiff.comp (amnrCurveJointCompose_contDiff_infty_local hf η))
      using 1
  rfl

/-- The actual residual derivative follows from the local substitution rule. -/
theorem amnrCurveResidual_hasFDerivAt_local {K E : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) (u : C(K, E)) :
    HasFDerivAt (amnrCurveResidual f hf.continuous η V)
      ((1 : C(K, E) →L[ℝ] C(K, E)) - amnrCurveJacobianCoefficient f hf η V u) u :=
  (hasFDerivAt_id u).sub (V.hasFDerivAt.comp u (amnrCurveJointCompose_hasFDerivAt_local hf η u))

/-- A continuous family solving the actual integral equation is smooth
whenever the actual linearized Volterra operator is small at the reference
curve. This is a local calculus criterion, not a flow regularity assumption. -/
theorem amnrCurveResidual_solution_contDiffAt_local {K E P : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E))
    {Q R : P → C(K, E)} {x : P} (hQ : ContinuousAt Q x)
    (hR : ContDiffAt ℝ (⊤ : ℕ∞) R x)
    (heq : ∀ y, amnrCurveResidual f hf.continuous η V (Q y) = R y)
    (hsmall : ‖amnrCurveJacobianCoefficient f hf η V (Q x)‖ < 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) Q x := by
  let W := amnrCurveJacobianCoefficient f hf η V (Q x)
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hsmall
  let e := ContinuousLinearEquiv.ofUnit u
  have he : (e : C(K, E) →L[ℝ] C(K, E)) = 1 - W := hu
  have hd := amnrCurveResidual_hasFDerivAt_local hf η V (Q x)
  change HasFDerivAt (amnrCurveResidual f hf.continuous η V) (1 - W) (Q x) at hd
  rw [← he] at hd
  exact amnr_contDiffAt_of_invertible_left_equation hQ
    (amnrCurveResidual_contDiff_infty_local hf η V).contDiffAt e hd hR heq

/-- Primitive Jacobian bounds along a single actual reference trajectory
control the local linearized Volterra operator. -/
theorem amnrCurveJacobianCoefficient_norm_le_along {K E : Type}
    [TopologicalSpace K] [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (η : C(K, ℝ)) (V : C(K, E) →L[ℝ] C(K, E)) (u : C(K, E))
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t, ‖amnrStateDerivative f (η t, u t)‖ ≤ M) :
    ‖amnrCurveJacobianCoefficient f hf η V u‖ ≤ ‖V‖ * M := by
  let A := amnrCurveJointCompose (amnrStateDerivative f)
    (amnrStateDerivative_contDiff hf).continuous η u
  have hA : ‖A‖ ≤ M := (ContinuousMap.norm_le A hM).mpr hstate
  exact (V.opNorm_comp_le (amnrCurveOperator A)).trans
    (mul_le_mul_of_nonneg_left ((amnrCurveOperator_norm_le A).trans hA) (norm_nonneg V))

end AVenhance.Infra.Section4
