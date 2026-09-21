/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HessianCoreMetricCurvature

/-!
# The Hessian core in the Ricci--DeTurck principal-part calculation

This file puts the metric Hessian combination produced by the Ricci
connection-change derivative together with the two differentiated DeTurck
traces into the exact cleared-denominator form used by the generic Hessian
cancellation theorem.  The result is a pointwise identity: it neither
asserts a full Ricci--DeTurck equation nor hides the curvature terms.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
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

/-! These are the nested Hom-bundle instances required to state the genuine
first derivative of a covariant two-tensor.  They agree with the instances
used by `HessianCoreMetricCurvature`. -/
local instance standardDeTurckHessianOneFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₁ y) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance standardDeTurckHessianOneFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₁ y) :=
  ContinuousLinearMap.toNormedSpace
local instance standardDeTurckHessianOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance standardDeTurckHessianOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance standardDeTurckHessianOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance standardDeTurckHessianOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance standardDeTurckHessianTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance standardDeTurckHessianTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance standardDeTurckHessianTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance standardDeTurckHessianTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance standardDeTurckHessianTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance standardDeTurckHessianTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance standardDeTurckHessianTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance standardDeTurckHessianTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance standardDeTurckHessianThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance standardDeTurckHessianThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance standardDeTurckHessianThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance standardDeTurckHessianThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance standardDeTurckHessianThreeTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance standardDeTurckHessianThreeFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance standardDeTurckHessianThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance standardDeTurckHessianThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- The cleared-denominator Hessian combination arising after adding the
derivative part of the Ricci connection change to the two differentiated
DeTurck traces.  It is exactly the traced connection Laplacian core plus the
three explicit induced-curvature contractions. -/
theorem standardDeTurck_hessianPrincipalCore_eq
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
      (-2 : ℝ) * covariantHessianTwoTensor cov g.toSection x (b i) u v (b i) -
        2 * covariantHessianTwoTensor cov g.toSection x (b i) v u (b i) +
        2 * covariantHessianTwoTensor cov g.toSection x (b i) (b i) u v +
        2 * covariantHessianTwoTensor cov g.toSection x u (b i) v (b i) +
        covariantHessianTwoTensor cov g.toSection x u v (b i) (b i) +
        2 * covariantHessianTwoTensor cov g.toSection x v (b i) (b i) u -
        covariantHessianTwoTensor cov g.toSection x v u (b i) (b i))) =
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
  have hcore := hessianCoreCancellation_trace_metric_clearedDenominator
    cov g hfirst hT b u v
  have hsymm : ∀ y (a b : TM y),
      g.toSection y a b = g.toSection y b a := by
    intro y a b
    exact g.symm y a b
  have hswap (X₁ X₂ a b' : TM x) :
      covariantHessianTwoTensor cov g.toSection x X₁ X₂ a b' =
        covariantHessianTwoTensor cov g.toSection x X₁ X₂ b' a :=
    covariantHessianTwoTensor_swap (h := g.toSection) cov hsymm x X₁ X₂ a b'
  calc
    Finset.univ.sum (fun i : ι =>
        (-2 : ℝ) * covariantHessianTwoTensor cov g.toSection x (b i) u v (b i) -
          2 * covariantHessianTwoTensor cov g.toSection x (b i) v u (b i) +
          2 * covariantHessianTwoTensor cov g.toSection x (b i) (b i) u v +
          2 * covariantHessianTwoTensor cov g.toSection x u (b i) v (b i) +
          covariantHessianTwoTensor cov g.toSection x u v (b i) (b i) +
          2 * covariantHessianTwoTensor cov g.toSection x v (b i) (b i) u -
          covariantHessianTwoTensor cov g.toSection x v u (b i) (b i)) =
        Finset.univ.sum (fun i : ι =>
          (-2 : ℝ) *
              (covariantHessianTwoTensor cov g.toSection x (b i) u v (b i) +
                covariantHessianTwoTensor cov g.toSection x (b i) v u (b i) -
                covariantHessianTwoTensor cov g.toSection x (b i) (b i) v u -
                covariantHessianTwoTensor cov g.toSection x u v (b i) (b i)) +
            (2 * covariantHessianTwoTensor cov g.toSection x u (b i) (b i) v -
              covariantHessianTwoTensor cov g.toSection x u v (b i) (b i)) +
            (2 * covariantHessianTwoTensor cov g.toSection x v (b i) (b i) u -
              covariantHessianTwoTensor cov g.toSection x v u (b i) (b i))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hswap (b i) (b i) u v, hswap u (b i) v (b i)]
          ring
    _ = _ := hcore

end CovariantDerivative
