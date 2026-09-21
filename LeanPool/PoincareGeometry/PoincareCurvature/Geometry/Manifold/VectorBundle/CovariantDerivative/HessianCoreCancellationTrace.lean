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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HessianCoreCancellation

/-!
# Tracing the Ricci--DeTurck Hessian core cancellation

This module takes the pointwise cleared-denominator Hessian cancellation and
traces it in an arbitrary finite orthonormal tangent frame.  The result keeps
the background Hessian trace and all induced-tensor curvature terms explicit.
It does not introduce a reaction remainder or assert a parabolic equation.
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

/-! The differentiability hypothesis for the pointwise cancellation lives in
the total space of covariant three-tensors.  The dependent Hom-bundle
instances are recorded locally so that this standalone trace theorem can
state that hypothesis without relying on implementation-local instances from
its imported source. -/
local instance hessianTraceOneFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₁ y) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance hessianTraceOneFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₁ y) :=
  ContinuousLinearMap.toNormedSpace
local instance hessianTraceOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianTraceOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianTraceOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianTraceOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance hessianTraceTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance hessianTraceTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance hessianTraceTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance hessianTraceTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance hessianTraceTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianTraceTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianTraceTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianTraceTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance hessianTraceThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance hessianTraceThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance hessianTraceThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance hessianTraceThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance hessianTraceThreeTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianTraceThreeFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianTraceThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianTraceThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- Tracing the cleared-denominator second-order Ricci--DeTurck cancellation
over any finite orthonormal tangent frame.  The first term on the right is
twice the traced background Hessian; the remaining three terms are the
explicit curvature of the induced covariant-two-tensor connection. -/
theorem hessianCoreCancellation_trace_clearedDenominator
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
      2 * (Finset.univ.sum (fun i : ι =>
        covariantHessianTwoTensor cov h x (b i) (b i) u v)) +
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
  classical
  calc
    _ = Finset.univ.sum (fun i : ι =>
        (2 * covariantHessianTwoTensor cov h x (b i) (b i) u v +
          2 * (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x u)
            (smoothExtend (I := I) (F := E) (V := TM) x (b i)) h x (b i) v +
          2 * (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x v)
            (smoothExtend (I := I) (F := E) (V := TM) x (b i)) h x (b i) u +
          (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x u)
            (smoothExtend (I := I) (F := E) (V := TM) x v) h x (b i) (b i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hessianCoreCancellation_summand_clearedDenominator cov hfirst hT hsymm
        (b i) u v
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

end CovariantDerivative
