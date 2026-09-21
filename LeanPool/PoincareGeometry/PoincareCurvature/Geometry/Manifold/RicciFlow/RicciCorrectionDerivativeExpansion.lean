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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivitaCorrectionDerivative

/-!
# Hessian expansion of the derivative part of the Ricci connection change

This file isolates the derivative summand in the Ricci curvature change from
a torsion-free background connection to its Levi-Civita correction.  It
rewrites that summand through the covariant Hessian of the metric and the
metric-defect terms created by the non-metric background connection.  No
commutation of Hessian slots, cancellation, or reaction term is asserted.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-! The Hessian regularity premise lives in the three-times induced Hom
bundle.  Re-enable the exact local instance stack used by
`LeviCivitaCorrectionDerivative`, so this file shares its intrinsic bundle
representation instead of rebuilding an inequivalent one. -/
attribute [local instance]
  correctionDerivativeScalarTopologicalSpace
  correctionDerivativeScalarFiberBundle
  correctionDerivativeScalarVectorBundle
  correctionDerivativeScalarContMDiffVectorBundle
  correctionDerivativeOneFiberNormedAddCommGroup
  correctionDerivativeOneFiberNormedSpace
  correctionDerivativeOneTopologicalSpace
  correctionDerivativeOneFiberBundle
  correctionDerivativeOneVectorBundle
  correctionDerivativeOneContMDiffVectorBundle
  correctionDerivativeTwoModelNormedAddCommGroup
  correctionDerivativeTwoModelNormedSpace
  correctionDerivativeTwoFiberNormedAddCommGroup
  correctionDerivativeTwoFiberNormedSpace
  correctionDerivativeTwoTopologicalSpace
  correctionDerivativeTwoFiberBundle
  correctionDerivativeTwoVectorBundle
  correctionDerivativeTwoContMDiffVectorBundle
  correctionDerivativeThreeModelNormedAddCommGroup
  correctionDerivativeThreeModelNormedSpace
  correctionDerivativeThreeFiberNormedAddCommGroup
  correctionDerivativeThreeFiberNormedSpace
  correctionDerivativeThreeTopologicalSpace
  correctionDerivativeThreeFiberBundle
  correctionDerivativeThreeVectorBundle
  correctionDerivativeThreeContMDiffVectorBundle

/-- **Derivative portion of the Ricci connection-change trace.**

For `A = cov.leviCivitaCorrection`, this expands exactly
`-2 ∑ᵢ ⟪eᵢ, (∇_{eᵢ} A)(v,u) - (∇_u A)(v,eᵢ)⟫`.  The first six terms are the
two raw Hessian combinations; the final two retain the metric-defect
corrections.  The `hfirst` premise is the actual pointwise regularity needed
to form the covariant Hessian. -/
theorem neg_two_ricciConnectionChange_derivative_trace_eq_hessian_metricDefect
    (cov : CovariantDerivative I E TM) [ContMDiffCovariantDerivative cov 1]
    (hTorsionFree : cov.IsTorsionFree) {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov
          (riemannianMetricCovariantTwoTensor (I := I) (M := M)) y)) x)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TM x)) (u v : TM x) :
    (-2 : ℝ) * ∑ i, inner ℝ (b i)
        (covariantDerivativeOneForm cov cov.leviCivitaCorrection x (b i) v u -
          covariantDerivativeOneForm cov cov.leviCivitaCorrection x u v (b i)) =
      ∑ i,
        (- covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            (b i) u v (b i) -
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            (b i) v u (b i) +
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            (b i) (b i) u v +
          2 * cov.metricDefect x (cov.leviCivitaCorrection x v u) (b i) (b i) +
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            u (b i) v (b i) +
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            u v (b i) (b i) -
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            u (b i) (b i) v -
          2 * cov.metricDefect x (cov.leviCivitaCorrection x v (b i)) (b i) u) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hfirstTerm :=
    covariantDerivativeOneForm_leviCivitaCorrection_inner_eq_hessian_metricDefect
      (I := I) (E := E) (M := M) cov hTorsionFree hfirst (b i) v u (b i)
  have hsecondTerm :=
    covariantDerivativeOneForm_leviCivitaCorrection_inner_eq_hessian_metricDefect
      (I := I) (E := E) (M := M) cov hTorsionFree hfirst u v (b i) (b i)
  rw [inner_sub_right]
  have hfirstTerm' :
      2 * inner ℝ (b i)
        (covariantDerivativeOneForm cov cov.leviCivitaCorrection x (b i) v u) =
        covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            (b i) u v (b i) +
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            (b i) v u (b i) -
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            (b i) (b i) u v -
          2 * cov.metricDefect x (cov.leviCivitaCorrection x v u) (b i) (b i) := by
    calc
      2 * inner ℝ (b i)
          (covariantDerivativeOneForm cov cov.leviCivitaCorrection x (b i) v u) =
          2 * inner ℝ
            (covariantDerivativeOneForm cov cov.leviCivitaCorrection x (b i) v u) (b i) := by
            rw [real_inner_comm]
      _ = _ := hfirstTerm
  have hsecondTerm' :
      2 * inner ℝ (b i)
        (covariantDerivativeOneForm cov cov.leviCivitaCorrection x u v (b i)) =
        covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            u (b i) v (b i) +
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            u v (b i) (b i) -
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
            u (b i) (b i) v -
          2 * cov.metricDefect x (cov.leviCivitaCorrection x v (b i)) (b i) u := by
    calc
      2 * inner ℝ (b i)
          (covariantDerivativeOneForm cov cov.leviCivitaCorrection x u v (b i)) =
          2 * inner ℝ
            (covariantDerivativeOneForm cov cov.leviCivitaCorrection x u v (b i)) (b i) := by
            rw [real_inner_comm]
      _ = _ := hsecondTerm
  linarith

end CovariantDerivative
