/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothGraphFlow
public import LeanPool.NavierStokesAndEuler.Euler.SmoothScaledFlow
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume

/-! The true physical graph flow and its first two time derivatives.
The change of labels is an actual ODE conjugacy, and the resulting
three-dimensional flow preserves ordinary Lebesgue volume. -/

@[expose] public section


noncomputable section

namespace EulerGraphInvariantFlow

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothBanachFlow
  EulerSmoothFlowGevrey
open scoped ContDiff

variable (k : ℝ) (m : Vector3) (T : ℝ) (hT : 0 ≤ T)
  (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hgraph : ∀ t z, graphConstraint k m (A.field t z) = 0)

include hgraph in
theorem graph_materialVelocity_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialVelocity T hT (graphCoefficient k m T A) t x =
      (materialVelocity T hT A t (graphLinear k m x)).1 := by
  change (A.field t (graphLinear k m
    ((flowData T hT (graphCoefficient k m T A)).flow 0 t x))).1 = _
  rw [← graph_flow_cover k m T hT A hgraph]
  rfl

include hgraph in
theorem graph_accelerationField_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    accelerationField T (graphCoefficient k m T A) (graphCoefficient k m T A₁) t x =
      (accelerationField T A A₁ t (graphLinear k m x)).1 := by
  let J := graphLinear k m
  let L := fst ℝ Vector3 ℝ
  have hd := (L.hasFDerivAt.comp x
    (((A.smooth t).differentiable (by simp) (J x)).hasFDerivAt.comp x J.hasFDerivAt)).fderiv
  change fderiv ℝ ((graphCoefficient k m T A).field t : Vector3 → Vector3) x =
    L.comp ((fderiv ℝ (A.field t : LiftTangent → LiftTangent) (J x)).comp J) at hd
  have hval : J (A.field t (J x)).1 = A.field t (J x) := by
    apply Prod.ext
    · rfl
    · exact (sub_eq_zero.mp (hgraph t (J x))).symm
  change (A₁.field t (J x)).1 +
    fderiv ℝ ((graphCoefficient k m T A).field t : Vector3 → Vector3) x (A.field t (J x)).1 = _
  rw [hd,comp_apply,comp_apply,hval]
  rfl

include hgraph in
theorem graph_materialAcceleration_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialAcceleration T hT (graphCoefficient k m T A) (graphCoefficient k m T A₁) t x =
      (materialAcceleration T hT A A₁ t (graphLinear k m x)).1 := by
  unfold materialAcceleration
  rw [graph_accelerationField_eq k m T A A₁ hgraph]
  change (accelerationField T A A₁ t (graphLinear k m
    ((flowData T hT (graphCoefficient k m T A)).flow 0 t x))).1 = _
  rw [← graph_flow_cover k m T hT A hgraph]
  rfl

/-- Physical coefficient, given by `scaledCoefficient T (graphCoefficient k m T A) ell`. -/
def physicalCoefficient (ell : ℝ) : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  scaledCoefficient T (graphCoefficient k m T A) ell

@[simp] theorem physicalCoefficient_apply (ell : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (physicalCoefficient k m T A ell).field t x = ell • (A.field t (graphLinear k m (ell⁻¹ • x))).1
        := rfl

theorem physicalCoefficient_timeDerivative (ell : ℝ)
    (htime : SmoothTimeField.TimeDerivative T hT A A₁) :
    SmoothTimeField.TimeDerivative T hT (physicalCoefficient k m T A ell)
      (physicalCoefficient k m T A₁ ell) :=
  scaledCoefficient_timeDerivative T hT (graphCoefficient k m T A) ell
    (graphCoefficient k m T A₁) (graphCoefficient_timeDerivative k m T hT A A₁ htime)

include hgraph in
theorem physical_flow_eq (ell : ℝ) (hell : ell ≠ 0) (s t : ℝ) (x : Vector3) :
    (flowData T hT (physicalCoefficient k m T A ell)).flow s t x =
      ell • ((flowData T hT A).flow s t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,scaled_flow_eq T hT (graphCoefficient k m T A) ell hell]
  rw [← graph_flow_eq k m T hT A hgraph]
  rfl

include hgraph in
theorem physical_displacement_eq (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    displacement T hT (physicalCoefficient k m T A ell) t x =
      ell • (displacement T hT A t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,scaled_displacement_eq T hT (graphCoefficient k m T A) ell hell,
    ← graph_displacement_eq k m T hT A hgraph]

include hgraph in
theorem physical_materialVelocity_eq (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialVelocity T hT (physicalCoefficient k m T A ell) t x =
      ell • (materialVelocity T hT A t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,scaled_materialVelocity_eq T hT (graphCoefficient k m T A) ell hell,
    graph_materialVelocity_eq k m T hT A hgraph]

include hgraph in
theorem physical_materialAcceleration_eq (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialAcceleration T hT (physicalCoefficient k m T A ell) (physicalCoefficient k m T A₁ ell)
        t x =
      ell • (materialAcceleration T hT A A₁ t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,physicalCoefficient,
    scaled_materialAcceleration_eq T hT (graphCoefficient k m T A) ell
      (graphCoefficient k m T A₁) hell,graph_materialAcceleration_eq k m T hT A A₁ hgraph]

variable (hdiv : ∀ t z,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) z).toLinearMap =
      0)

include hgraph hdiv in
theorem physicalCoefficient_trace_zero (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    LinearMap.trace ℝ Vector3
      (fderiv ℝ ((physicalCoefficient k m T A ell).field t : Vector3 → Vector3) x).toLinearMap=0 :=
  scaledCoefficient_trace_zero T (graphCoefficient k m T A) ell hell
    (graphCoefficient_trace_zero k m T A hgraph hdiv) t x

include hgraph hdiv in
theorem physical_forward_measurePreserving (ell : ℝ) (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) :
    MeasurePreserving ((flowData T hT (physicalCoefficient k m T A ell)).forward t) volume volume
        := by
  exact forward_measurePreserving T hT (physicalCoefficient k m T A ell)
    (physicalCoefficient_trace_zero k m T A hgraph hdiv ell hell) volume t

end EulerGraphInvariantFlow
