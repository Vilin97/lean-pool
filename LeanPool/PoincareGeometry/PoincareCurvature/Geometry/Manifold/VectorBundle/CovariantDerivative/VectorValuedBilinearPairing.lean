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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConnectionChange
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.MetricDefectTensorDerivative

/-!
# Pairing a differentiated vector-valued bilinear tensor

This module records the affine Leibniz rule for the scalar pairing of a
vector-valued bilinear tensor with a moving tangent vector.  It makes the
metric-defect term explicit.
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
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCorr" =>
  (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x)

/-- Differentiating `⟪A(Z,Y), V⟫` along an arbitrary affine connection.
The first term is the induced covariant derivative of the vector-valued
bilinear tensor; the next three are the ordinary Leibniz terms, and the last
is the failure of the connection to preserve the metric. -/
theorem mvfderiv_inner_vectorValuedBilinear_apply
    (cov : CovariantDerivative I E TM)
    {A : ∀ y : M, TCorr y}
    {Y Z V : ∀ y : M, TM y} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y (A y)) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hV : MDiffAt (T% V) x) (u : TM x) :
    mvfderiv (I := I) (fun y => inner ℝ (A y (Z y) (Y y)) (V y)) x u =
      inner ℝ (covariantDerivativeOneForm cov A x u (Z x) (Y x)) (V x) +
        inner ℝ (A x (Z x) (cov Y x u)) (V x) +
        inner ℝ (A x (cov Z x u) (Y x)) (V x) +
        inner ℝ (A x (Z x) (Y x)) (cov V x u) +
        cov.metricDefect x (A x (Z x) (Y x)) (V x) u := by
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  have hP : MDiffAt (T% (fun y => A y (Z y) (Y y))) x :=
    (hA.clm_bundle_apply hZ).clm_bundle_apply hY
  have hDAraw := covariantDerivativeOneForm_apply_eq_along
    (I := I) cov A (X := X) (Y := Y) (Z := Z) hA hY hZ
  have hDAexpanded :
      covariantDerivativeOneForm cov A x u (Z x) (Y x) =
        cov (fun y => A y (Z y) (Y y)) x u -
          A x (Z x) (cov Y x u) - A x (cov Z x u) (Y x) := by
    simpa only [covariantDerivativeOneFormAlong, CovariantDerivative.along,
      X, smoothExtend_apply] using hDAraw
  have hDA :
      cov (fun y => A y (Z y) (Y y)) x u =
        covariantDerivativeOneForm cov A x u (Z x) (Y x) +
          A x (Z x) (cov Y x u) + A x (cov Z x u) (Y x) := by
    rw [hDAexpanded]
    abel
  have hdef := congrArg (fun q : TM x →L[ℝ] ℝ => q u)
    (cov.metricDefect_apply_sections hP hV)
  rw [metricDefectAux_apply, hDA] at hdef
  simp only [inner_add_left] at hdef
  linarith

/-- At a point where the two tensor inputs and the pairing vector are
covariantly stationary, only the derivative of the vector-valued tensor and
the metric-defect contribution remain. -/
theorem mvfderiv_inner_vectorValuedBilinear_apply_of_covariantDerivative_eq_zero
    (cov : CovariantDerivative I E TM)
    {A : ∀ y : M, TCorr y}
    {Y Z V : ∀ y : M, TM y} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y (A y)) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hV : MDiffAt (T% V) x)
    (hYzero : cov Y x = 0) (hZzero : cov Z x = 0) (hVzero : cov V x = 0)
    (u : TM x) :
    mvfderiv (I := I) (fun y => inner ℝ (A y (Z y) (Y y)) (V y)) x u =
      inner ℝ (covariantDerivativeOneForm cov A x u (Z x) (Y x)) (V x) +
        cov.metricDefect x (A x (Z x) (Y x)) (V x) u := by
  rw [mvfderiv_inner_vectorValuedBilinear_apply cov hA hY hZ hV u,
    hYzero, hZzero, hVzero]
  simp

end CovariantDerivative
