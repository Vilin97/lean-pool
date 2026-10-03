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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearEvaluation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection

/-!
# Evaluation of the intrinsic connection Laplacian

The expanded BilinearAlong definitions are useful for local calculations,
whereas connectionLaplacian is the intrinsic induced-bundle contraction.
This file proves that the two presentations agree at a point. The
differentiability assumptions are deliberately explicit: these are evaluation
lemmas, not a replacement for a space-time regularity theorem.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] (T₂ x))

local instance connectionLaplacianIntrinsicCovectorNormedAddCommGroup :
    ∀ x : M, NormedAddCommGroup (TM x →L[ℝ] ℝ) :=
  fun _ => ContinuousLinearMap.toNormedAddCommGroup

local instance connectionLaplacianIntrinsicCovectorNormedSpace :
    ∀ x : M, NormedSpace ℝ (TM x →L[ℝ] ℝ) :=
  fun _ => ContinuousLinearMap.toNormedSpace

local instance connectionLaplacianIntrinsicTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance

local instance connectionLaplacianIntrinsicTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance

local instance connectionLaplacianIntrinsicTwoFiberNormedAddCommGroup :
    ∀ x : M, NormedAddCommGroup (T₂ x) :=
  fun _ => inferInstance

local instance connectionLaplacianIntrinsicTwoFiberNormedSpace :
    ∀ x : M, NormedSpace ℝ (T₂ x) :=
  fun _ => inferInstance

local instance connectionLaplacianIntrinsicThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance

local instance connectionLaplacianIntrinsicThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance

local instance connectionLaplacianIntrinsicThreeFiberNormedAddCommGroup :
    ∀ x : M, NormedAddCommGroup (T₃ x) :=
  fun _ => inferInstance

local instance connectionLaplacianIntrinsicThreeFiberNormedSpace :
    ∀ x : M, NormedSpace ℝ (T₃ x) :=
  fun _ => inferInstance

local instance connectionLaplacianIntrinsicScalarTopologicalSpace :
    TopologicalSpace (TotalSpace ℝ (Bundle.Trivial M ℝ)) :=
  Bundle.Trivial.topologicalSpace M ℝ

local instance connectionLaplacianIntrinsicScalarFiberBundle :
    FiberBundle ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.fiberBundle M ℝ

local instance connectionLaplacianIntrinsicScalarVectorBundle :
    VectorBundle ℝ ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.vectorBundle ℝ M ℝ

local instance connectionLaplacianIntrinsicScalarContMDiffVectorBundle :
    ContMDiffVectorBundle 2 ℝ (Bundle.Trivial M ℝ) I :=
  Bundle.Trivial.contMDiffVectorBundle ℝ

local instance connectionLaplacianIntrinsicCovectorTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)

local instance connectionLaplacianIntrinsicCovectorFiberBundle :
    FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)

local instance connectionLaplacianIntrinsicCovectorVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)

local instance connectionLaplacianIntrinsicCovectorContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance connectionLaplacianIntrinsicTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁

local instance connectionLaplacianIntrinsicTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁

local instance connectionLaplacianIntrinsicTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁

local instance connectionLaplacianIntrinsicTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance connectionLaplacianIntrinsicThreeTopologicalSpace :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂

local instance connectionLaplacianIntrinsicThreeFiberBundle :
    FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂

local instance connectionLaplacianIntrinsicThreeVectorBundle :
    VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂

local instance connectionLaplacianIntrinsicThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- The expanded first covariant derivative agrees with the induced-bundle
derivative on arbitrary differentiable fields at the evaluation point. -/
theorem covariantDerivativeBilinearAlong_eq_intrinsic
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} {X Y Z : ∀ x : M, TM x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    covariantDerivativeBilinearAlong cov h X Y Z x =
      covariantTwoTensorCovariantDerivative cov h x
        (X x) (Y x) (Z x) := by
  unfold covariantDerivativeBilinearAlong
  have hprod := realLineCovariantDerivative_bilinear cov hh hY hZ (X x)
  change
      mvfderiv (I := I) (fun p => h p (Y p) (Z p)) x (X x) =
        covariantTwoTensorCovariantDerivative cov h x (X x)
            (Y x) (Z x) +
          h x (cov Y x (X x)) (Z x) +
          h x (Y x) (cov Z x (X x)) at hprod
  linarith

/-! The traced version is kept separate from the pointwise Hessian bridge so
that callers can supply exactly the regularity data available for the tensor
they are tracing. -/

/-- The expanded, basis-evaluated connection Laplacian agrees with the
intrinsic connection Laplacian whenever the canonical Hessian evaluations
agree. -/
theorem connectionLaplacianBilinearApply_eq_connectionLaplacian
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} (x : M) (u v : TM x)
    (hsecond : ∀ i : Fin (Module.finrank ℝ (TM x)),
      secondCovariantDerivativeBilinearAlong cov h
          (smoothExtend (I := I) (F := E) (V := TM) x
            ((stdOrthonormalBasis ℝ (TM x)) i))
          (smoothExtend (I := I) (F := E) (V := TM) x
            ((stdOrthonormalBasis ℝ (TM x)) i))
          (smoothExtend (I := I) (F := E) (V := TM) x u)
          (smoothExtend (I := I) (F := E) (V := TM) x v) x =
        covariantHessianTwoTensor cov h x
          ((stdOrthonormalBasis ℝ (TM x)) i)
          ((stdOrthonormalBasis ℝ (TM x)) i) u v) :
    connectionLaplacianBilinearApply cov h x u v =
      connectionLaplacian cov h x u v := by
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  unfold connectionLaplacianBilinearApply
  rw [connectionLaplacian_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact hsecond i

end CovariantDerivative
