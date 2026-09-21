/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacianMaximum
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciNorm

/-!
# Scalar quantities for a time-dependent Riemannian metric

This module puts the intrinsic scalar Laplacian and squared Ricci norm on the
same time-slice metric used by the existing Ricci-flow API.  It also lifts the
pointwise trace estimate to time-dependent metrics.  The evolution identity
itself is deliberately not postulated here; it will be derived from metric
variation in the subsequent layer.
-/

@[expose] public noncomputable section
open Bundle Filter Topology
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

namespace TimeDependentRiemannianMetric

variable (g : TimeDependentRiemannianMetric (I := I) (M := M))

/-- The scalar Laplace--Beltrami operator at time `t`, using the metric `g t`
and the supplied connection slice. -/
def scalarLaplacian
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f : ℝ → M → ℝ) (t : ℝ) (x : M) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.scalarLaplacian (cov t) (f t) x

@[simp] lemma scalarLaplacian_apply
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f : ℝ → M → ℝ) (t : ℝ) (x : M) :
    g.scalarLaplacian cov f t x = (by
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.scalarLaplacian (cov t) (f t) x) := rfl

/-- The time-slice scalar Laplacian is nonnegative at a local spatial
minimum.  This is the intrinsic manifold statement, specialized to the
actual Riemannian metric at time `t`. -/
theorem scalarLaplacian_nonneg_of_isLocalMin [I.Boundaryless]
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f : ℝ → M → ℝ) (t : ℝ) {x : M}
    (hmin : IsLocalMin (f t) x)
    (hfNear : ∀ᶠ y in 𝓝 x, MDiffAt (f t) y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I) (f t) y)) x) :
    0 ≤ g.scalarLaplacian cov f t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  exact CovariantDerivative.scalarLaplacian_nonneg_of_isLocalMin
    (cov t) hmin hfNear hdf

/-- The squared Hilbert--Schmidt norm of the Ricci tensor at time `t`. -/
def ricciNormSq
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.ricciNormSq (cov := cov t) x

theorem scalarCurvature_sq_le_finrank_mul_ricciNormSq
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) :
    (g.scalarCurvature cov hcov t x) ^ 2 ≤
      (Module.finrank ℝ (TM x) : ℝ) * g.ricciNormSq cov hcov t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.scalarCurvature_sq_le_finrank_mul_ricciNormSq
    (cov := cov t) x

/-- In dimension three, `R² ≤ 3 |Ric|²`. -/
theorem scalarCurvature_sq_le_three_mul_ricciNormSq
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    (g.scalarCurvature cov hcov t x) ^ 2 ≤
      3 * g.ricciNormSq cov hcov t x := by
  simpa [hdim x] using
    g.scalarCurvature_sq_le_finrank_mul_ricciNormSq cov hcov t x

/-- In dimension three, the Ricci-flow scalar reaction dominates the sharp
Riccati reaction `(2/3) R²`. -/
theorem two_thirds_scalarCurvature_sq_le_two_mul_ricciNormSq
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    (2 / 3 : ℝ) * (g.scalarCurvature cov hcov t x) ^ 2 ≤
      2 * g.ricciNormSq cov hcov t x := by
  have h := g.scalarCurvature_sq_le_three_mul_ricciNormSq
    cov hcov hdim t x
  nlinarith

end TimeDependentRiemannianMetric
end CovariantDerivative
