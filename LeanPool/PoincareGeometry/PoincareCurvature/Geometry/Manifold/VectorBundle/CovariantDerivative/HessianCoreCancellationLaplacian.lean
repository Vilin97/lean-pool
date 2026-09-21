/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HessianCoreCancellationTrace

/-!
# The Laplacian form of the Ricci--DeTurck Hessian cancellation

This module rewrites the traced background Hessian in the exact
Ricci--DeTurck second-order cancellation as the intrinsic connection
Laplacian.  The induced-tensor curvature terms remain displayed as explicit
finite sums.  It does not introduce a reaction remainder or assert a
parabolic equation.
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

/-! The differentiability hypothesis is a statement in the total space of
covariant three-tensors.  Record the nested Hom-bundle instances locally so
this standalone corollary has the same concrete hypothesis as the traced
cancellation theorem it invokes. -/
local instance hessianLaplacianOneFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₁ y) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance hessianLaplacianOneFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₁ y) :=
  ContinuousLinearMap.toNormedSpace
local instance hessianLaplacianOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianLaplacianOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianLaplacianOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianLaplacianOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance hessianLaplacianTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance hessianLaplacianTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance hessianLaplacianTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance hessianLaplacianTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance hessianLaplacianTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianLaplacianTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianLaplacianTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianLaplacianTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance hessianLaplacianThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance hessianLaplacianThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance hessianLaplacianThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance hessianLaplacianThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance hessianLaplacianThreeTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianLaplacianThreeFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianLaplacianThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianLaplacianThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- The traced, cleared-denominator Ricci--DeTurck second-order cancellation
with its background Hessian trace written as the intrinsic connection
Laplacian.  The remaining three finite sums are the explicit curvature of
the induced covariant-two-tensor connection. -/
theorem hessianCoreCancellation_trace_clearedDenominator_eq_connectionLaplacian
    (cov : CovariantDerivative I E TM)
    {h : ∀ y : M, T₂ y} {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hT : cov.torsion = 0)
    (hsymm : ∀ y a b, h y a b = h y b a)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x))
    (u v : TM x) :
    (Finset.univ.sum (fun i : ι =>
      (-2 : ℝ) *
          (covariantHessianTwoTensor cov h x (b i) u v (b i) +
            covariantHessianTwoTensor cov h x (b i) v u (b i) -
            covariantHessianTwoTensor cov h x (b i) (b i) v u -
            covariantHessianTwoTensor cov h x u v (b i) (b i)) +
        (2 * covariantHessianTwoTensor cov h x u (b i) (b i) v -
          covariantHessianTwoTensor cov h x u v (b i) (b i)) +
        (2 * covariantHessianTwoTensor cov h x v (b i) (b i) u -
           covariantHessianTwoTensor cov h x v u (b i) (b i)))) =
      2 * connectionLaplacian cov h x u v +
        2 * (Finset.univ.sum (fun i : ι =>
          (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x u)
            (smoothExtend (I := I) (F := E) (V := TM) x (b i)) h x (b i) v)) +
        2 * (Finset.univ.sum (fun i : ι =>
          (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x v)
            (smoothExtend (I := I) (F := E) (V := TM) x (b i)) h x (b i) u)) +
        Finset.univ.sum (fun i : ι =>
          (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x u)
            (smoothExtend (I := I) (F := E) (V := TM) x v) h x (b i) (b i)) := by
  rw [connectionLaplacian_eq_sum_orthonormalBasis cov h x b]
  rw [sum_apply, sum_apply]
  exact hessianCoreCancellation_trace_clearedDenominator cov hfirst hT hsymm b u v

end CovariantDerivative
