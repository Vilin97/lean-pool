/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldPrecomp
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A physical label dilation of a smooth velocity has the conjugate
actual flow. Displacement, material velocity and material acceleration
are the literal dilations of the corresponding original fields. -/

@[expose] public section


noncomputable section

namespace EulerSmoothBanachFlow

open Set ContinuousLinearMap MeasureTheory EulerSmoothFlowGevrey
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E) (ell : ℝ)

/-- Scaled coefficient, given by `(A.precompLinear (ell⁻¹ • ContinuousLinearMap.id ℝ E)).map
(ell • ContinuousLinearMap.id ℝ E)`. -/
def scaledCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  (A.precompLinear (ell⁻¹ • ContinuousLinearMap.id ℝ E)).map (ell • ContinuousLinearMap.id ℝ E)

@[simp] theorem scaledCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (scaledCoefficient T A ell).field t x = ell • A.field t (ell⁻¹ • x) := rfl

theorem scaledCoefficient_timeDerivative
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (htime : SmoothTimeField.TimeDerivative T hT A A₁) :
    SmoothTimeField.TimeDerivative T hT (scaledCoefficient T A ell) (scaledCoefficient T A₁ ell) :=
  (htime.precompLinear (ell⁻¹ • ContinuousLinearMap.id ℝ E)).map (ell • ContinuousLinearMap.id ℝ E)

variable [FiniteDimensional ℝ E]

theorem scaled_flow_eq (hell : ell ≠ 0) (s t : ℝ) (x : E) :
    (flowData T hT (scaledCoefficient T A ell)).flow s t x =
      ell • (flowData T hT A).flow s t (ell⁻¹ • x) := by
  let V := flowData T hT (scaledCoefficient T A ell)
  have hd (r : ℝ) : HasDerivAt (fun q => ell • (flowData T hT A).flow s q (ell⁻¹ • x))
      (V.velocity r (ell • (flowData T hT A).flow s r (ell⁻¹ • x))) r := by
    have h := ((flowData T hT A).flow_hasDerivAt s r (ell⁻¹ • x)).const_smul ell
    convert h using 1
    · rfl
    · change ell • A.field (projIcc 0 T hT r)
        (ell⁻¹ • (ell • (flowData T hT A).flow s r (ell⁻¹ • x))) = _
      simp only [smul_smul,inv_mul_cancel₀ hell,one_smul]
      rfl
  have hi : ell • (flowData T hT A).flow s s (ell⁻¹ • x) = x := by
    simp only [EulerBoundedLipschitzFlow.Data.flow_initial,smul_smul,mul_inv_cancel₀ hell,one_smul]
  exact (congrFun (V.flow_unique s x _ hd hi) t).symm

theorem scaled_displacement_eq (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) (x : E) :
    displacement T hT (scaledCoefficient T A ell) t x =
      ell • displacement T hT A t (ell⁻¹ • x) := by
  rw [displacement_eq,displacement_eq]
  change (flowData T hT (scaledCoefficient T A ell)).flow 0 t x-x = _
  rw [scaled_flow_eq T hT A ell hell,smul_sub,smul_smul,mul_inv_cancel₀ hell,one_smul]
  rfl

theorem scaled_materialVelocity_eq (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) (x : E) :
    materialVelocity T hT (scaledCoefficient T A ell) t x =
      ell • materialVelocity T hT A t (ell⁻¹ • x) := by
  unfold materialVelocity
  rw [scaledCoefficient_apply]
  change ell • A.field t (ell⁻¹ • (flowData T hT (scaledCoefficient T A ell)).flow 0 t x) = _
  rw [scaled_flow_eq T hT A ell hell,smul_smul,inv_mul_cancel₀ hell,one_smul]
  rfl

omit [FiniteDimensional ℝ E] in
theorem scaledCoefficient_fderiv (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) (x : E) :
    fderiv ℝ ((scaledCoefficient T A ell).field t : E → E) x =
      fderiv ℝ (A.field t : E → E) (ell⁻¹ • x) := by
  have h := ((((A.smooth t).differentiable (by simp) (ell⁻¹ • x)).hasFDerivAt).comp x
    ((ell⁻¹ • ContinuousLinearMap.id ℝ E).hasFDerivAt)).const_smul ell
  change HasFDerivAt (fun y => ell • A.field t (ell⁻¹ • y)) _ x at h
  change fderiv ℝ (fun y => ell • A.field t (ell⁻¹ • y)) x = _
  rw [h.fderiv]
  ext v
  simp only [FunLike.coe_smul,Pi.smul_apply,comp_apply,id_apply,map_smul,smul_smul,mul_inv_cancel₀
      hell,one_smul]

omit [FiniteDimensional ℝ E] in
theorem scaled_accelerationField_eq
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : E) :
    accelerationField T (scaledCoefficient T A ell) (scaledCoefficient T A₁ ell) t x =
      ell • accelerationField T A A₁ t (ell⁻¹ • x) := by
  simp only [accelerationField,scaledCoefficient_apply,scaledCoefficient_fderiv T A ell hell,
    map_smul,smul_add]

theorem scaled_materialAcceleration_eq
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : E) :
    materialAcceleration T hT (scaledCoefficient T A ell) (scaledCoefficient T A₁ ell) t x =
      ell • materialAcceleration T hT A A₁ t (ell⁻¹ • x) := by
  unfold materialAcceleration
  rw [scaled_accelerationField_eq T A ell A₁ hell]
  change ell • accelerationField T A A₁ t
    (ell⁻¹ • (flowData T hT (scaledCoefficient T A ell)).flow 0 t x) = _
  rw [scaled_flow_eq T hT A ell hell,smul_smul,inv_mul_cancel₀ hell,one_smul]
  rfl

omit [FiniteDimensional ℝ E] in
theorem scaledCoefficient_trace_zero (hell : ell ≠ 0)
    (hdiv : ∀ t x, LinearMap.trace ℝ E (fderiv ℝ (A.field t : E → E) x).toLinearMap = 0)
    (t : Icc (0 : ℝ) T) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ ((scaledCoefficient T A ell).field t : E → E) x).toLinearMap=0 :=
        by
  rw [scaledCoefficient_fderiv T A ell hell]
  exact hdiv t _

end EulerSmoothBanachFlow
