/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HessianCoreCancellationTrace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.MetricTensorCurvatureAction

/-!
# Metric specialization of the traced Hessian cancellation

This module specializes the traced second-order Ricci--DeTurck Hessian
calculation to a `C²` Riemannian metric.  It keeps the background Hessian
trace explicit and writes every curvature term of the induced covariant-two-
tensor connection as the usual curvature action in the two metric slots.
It does not identify a full Ricci--DeTurck right-hand side or introduce a
reaction term.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
local notation "T₃" => (fun y : M => TM y →L[ℝ] T₂ y)

/-! The Hessian regularity hypothesis is a statement in the total space of a
three-times covariant tensor bundle.  These local instances record its two
nested continuous-linear-map bundle constructions. -/
local instance metricHessianOneFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₁ y) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricHessianOneFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₁ y) :=
  ContinuousLinearMap.toNormedSpace
local instance metricHessianOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance metricHessianOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance metricHessianOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance metricHessianOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance metricHessianTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance metricHessianTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance metricHessianTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance metricHessianTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance metricHessianTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance metricHessianTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance metricHessianTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance metricHessianTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance metricHessianThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance metricHessianThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance metricHessianThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance metricHessianThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance metricHessianThreeTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance metricHessianThreeFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance metricHessianThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance metricHessianThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- The traced, cleared-denominator Hessian cancellation for a `C²` metric.
The right-hand side retains the traced background Hessian and expands each
induced covariant-two-tensor curvature term in its two metric slots. -/
theorem hessianCoreCancellation_trace_metric_clearedDenominator
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative cov 1]
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov g.toSection y)) x)
    (hT : cov.torsion = 0)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x))
    (u v : TM x) :
    (Finset.univ.sum (fun i : ι =>
      (-2 : ℝ) *
          (covariantHessianTwoTensor cov g.toSection x (b i) u v (b i) +
            covariantHessianTwoTensor cov g.toSection x (b i) v u (b i) -
            covariantHessianTwoTensor cov g.toSection x (b i) (b i) v u -
            covariantHessianTwoTensor cov g.toSection x u v (b i) (b i)) +
        (2 * covariantHessianTwoTensor cov g.toSection x u (b i) (b i) v -
          covariantHessianTwoTensor cov g.toSection x u v (b i) (b i)) +
        (2 * covariantHessianTwoTensor cov g.toSection x v (b i) (b i) u -
          covariantHessianTwoTensor cov g.toSection x v u (b i) (b i)))) =
      2 * (Finset.univ.sum (fun i : ι =>
        covariantHessianTwoTensor cov g.toSection x (b i) (b i) u v)) +
        2 * (Finset.univ.sum (fun i : ι =>
          -g.toSection x (cov.curvatureTensor x u (b i) (b i)) v -
            g.toSection x (b i) (cov.curvatureTensor x u (b i) v))) +
        2 * (Finset.univ.sum (fun i : ι =>
          -g.toSection x (cov.curvatureTensor x v (b i) (b i)) u -
            g.toSection x (b i) (cov.curvatureTensor x v (b i) u))) +
        Finset.univ.sum (fun i : ι =>
          -g.toSection x (cov.curvatureTensor x u v (b i)) (b i) -
            g.toSection x (b i) (cov.curvatureTensor x u v (b i))) := by
  classical
  rw [hessianCoreCancellation_trace_clearedDenominator cov hfirst hT
    (fun y a b => g.symm y a b) b u v]
  simp_rw [covariantTwoTensor_curvatureAux_metric_toSection_apply cov g]

end CovariantDerivative
