/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# The metric defect as a covariant derivative of the metric tensor

This file records the pointwise convention bridge needed when a background
connection differentiates a Riemannian metric.  The repository writes the
metric defect with arguments `(v, w, u)`, whereas the induced covariant
derivative of a covariant two-tensor is written with arguments `(u, v, w)`.

Thus the theorem below says exactly that
`cov.metricDefect x v w u = (∇_u g)(v, w)`.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- If a covariant two-tensor field is the ambient Riemannian metric, its
induced covariant derivative is the metric defect.  The argument order on the
right is the repository's `(tensor slot, tensor slot, direction)` convention. -/
theorem covariantTwoTensorCovariantDerivative_apply_eq_metricDefect
    (cov : CovariantDerivative I E TM) (h : ∀ y : M, T₂ y) {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hmetric : ∀ y (a b : TM y), h y a b = inner ℝ a b)
    (X u v : TM x) :
    covariantTwoTensorCovariantDerivative cov h x X u v =
      cov.metricDefect x u v X := by
  rw [covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt cov hh X u v]
  have hu : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x u)) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hv : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x v)) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hdef := congrArg (fun f => f X)
    (cov.metricDefect_apply_sections hu hv)
  rw [metricDefectAux_apply] at hdef
  simpa only [hmetric, smoothExtend_apply] using hdef.symm

end CovariantDerivative
