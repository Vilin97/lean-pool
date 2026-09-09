/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldPrecomp
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
public import LeanPool.NavierStokesAndEuler.Euler.GraphInvariantFlow
import LeanPool.NavierStokesAndEuler.Euler.GraphVelocityTrace
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume

/-! The graph restriction of the actual lifted flow is the actual flow
of a smooth three-dimensional velocity. It preserves ordinary spatial
volume when the original lifted velocity has zero trace. -/

@[expose] public section


noncomputable section

namespace EulerGraphInvariantFlow

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothBanachFlow
open scoped ContDiff

variable (k : ℝ) (m : Vector3) (T : ℝ) (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)

/-- Graph coefficient, given by `(A.precompLinear (graphLinear k m)).map (fst ℝ Vector3 ℝ)`. -/
def graphCoefficient : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  (A.precompLinear (graphLinear k m)).map (fst ℝ Vector3 ℝ)

@[simp] theorem graphCoefficient_apply (t : Icc (0 : ℝ) T) (x : Vector3) :
    (graphCoefficient k m T A).field t x = (A.field t (graphLinear k m x)).1 := rfl

theorem graphCoefficient_timeDerivative
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
    (htime : SmoothTimeField.TimeDerivative T hT A A₁) :
    SmoothTimeField.TimeDerivative T hT (graphCoefficient k m T A) (graphCoefficient k m T A₁) :=
  (htime.precompLinear (graphLinear k m)).map (fst ℝ Vector3 ℝ)

variable (hgraph : ∀ t z, graphConstraint k m (A.field t z) = 0)

include hgraph in
theorem flowData_tangent (r : ℝ) (z : LiftTangent) :
    graphConstraint k m ((flowData T hT A).velocity r z)=0 :=
  hgraph (projIcc 0 T hT r) z

include hgraph in
theorem graph_flow_eq (s t : ℝ) (x : Vector3) :
    graphFlow k m (flowData T hT A) s t x =
      (flowData T hT (graphCoefficient k m T A)).flow s t x := by
  let V := flowData T hT (graphCoefficient k m T A)
  have hd (r : ℝ) : HasDerivAt (fun q => graphFlow k m (flowData T hT A) s q x)
      (V.velocity r (graphFlow k m (flowData T hT A) s r x)) r :=
    graphFlow_hasDerivAt k m (flowData T hT A) (flowData_tangent k m T hT A hgraph) s r x
  exact congrFun (V.flow_unique s x (fun q => graphFlow k m (flowData T hT A) s q x)
    hd (graphFlow_initial k m (flowData T hT A) s x)) t

include hgraph in
theorem graph_flow_cover (s t : ℝ) (x : Vector3) :
    (flowData T hT A).flow s t (graphLinear k m x) =
      graphLinear k m ((flowData T hT (graphCoefficient k m T A)).flow s t x) := by
  rw [graphFlow_invariant k m (flowData T hT A) (flowData_tangent k m T hT A hgraph),
    graph_flow_eq k m T hT A hgraph]

include hgraph in
theorem graph_displacement_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    (displacement T hT A t (graphLinear k m x)).1 =
      displacement T hT (graphCoefficient k m T A) t x := by
  rw [displacement_eq,displacement_eq]
  change ((flowData T hT A).flow 0 t (graphLinear k m x)-graphLinear k m x).1 = _
  rw [graph_flow_cover k m T hT A hgraph]
  rfl

include hgraph in
theorem graph_forward_contDiff (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (graphFlow k m (flowData T hT A) 0 t) := by
  have he : graphFlow k m (flowData T hT A) 0 t =
      (flowData T hT (graphCoefficient k m T A)).forward t :=
    funext (graph_flow_eq k m T hT A hgraph 0 t)
  rw [he]
  exact forward_contDiff T hT (graphCoefficient k m T A) t

variable (hdiv : ∀ t z,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) z).toLinearMap =
      0)

include hgraph hdiv in
theorem graphCoefficient_trace_zero (t : Icc (0 : ℝ) T) (x : Vector3) :
    LinearMap.trace ℝ Vector3
      (fderiv ℝ ((graphCoefficient k m T A).field t : Vector3 → Vector3) x).toLinearMap=0 :=
  graphVelocity_trace_zero k m (A.field t) ((A.smooth t).differentiable (by simp))
    (hgraph t) (hdiv t) x

include hgraph hdiv in
theorem graph_forward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (graphFlow k m (flowData T hT A) 0 t) volume volume := by
  have he : graphFlow k m (flowData T hT A) 0 t =
      (flowData T hT (graphCoefficient k m T A)).forward t :=
    funext (graph_flow_eq k m T hT A hgraph 0 t)
  rw [he]
  exact forward_measurePreserving T hT (graphCoefficient k m T A)
    (graphCoefficient_trace_zero k m T A hgraph hdiv) volume t

include hgraph hdiv in
theorem graph_backward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (graphFlow k m (flowData T hT A) t 0) volume volume := by
  have he : graphFlow k m (flowData T hT A) t 0 =
      (flowData T hT (graphCoefficient k m T A)).backward t :=
    funext (graph_flow_eq k m T hT A hgraph t 0)
  rw [he]
  exact backward_measurePreserving T hT (graphCoefficient k m T A)
    (graphCoefficient_trace_zero k m T A hgraph hdiv) volume t

end EulerGraphInvariantFlow
