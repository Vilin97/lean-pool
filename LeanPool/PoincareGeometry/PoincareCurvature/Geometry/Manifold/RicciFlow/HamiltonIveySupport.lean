/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySpectrum
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.FirstOrderParallelExtension

/-!
# Spacetime support for the least curvature eigenvalue

At a spacetime contact point, choose the genuine unit least eigenvector and
extend it smoothly in space while keeping that extension fixed in time.  Its
Rayleigh quotient is a spacetime upper support for the least curvature
eigenvalue wherever the evolving metric keeps the extension nonzero.

Joint continuity of the evolving metric square is an explicit analytic
premise; the spectral support and the contact equality are proved here.
-/

@[expose] public noncomputable section
open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The fixed-in-time smooth spatial extension of the least eigenvector
selected at `(t₀,x₀)`.  Its first covariant derivative for the contact-time
Levi-Civita connection vanishes at `x₀`. -/
def curvatureNuContactVectorField
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) : ∀ y : M, TM y :=
  by
    exact firstOrderParallelSmoothExtend
      (I := I) (F := E) (V := TM) (cov t₀) x₀
      (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)

/-- The contact vector field is covariantly stationary to first order at its
spatial contact point. -/
theorem covariantDerivative_curvatureNuContactVectorField_eq_zero
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    cov t₀ (g.curvatureNuContactVectorField
      cov hcov hLevi hdim t₀ x₀) x₀ = 0 := by
  unfold curvatureNuContactVectorField
  exact covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
    (I := I) (F := E) (V := TM) (cov t₀) x₀
      (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)

/-- The contact vector field is differentiable at its spatial contact point. -/
theorem curvatureNuContactVectorField_mdifferentiableAt
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    MDiffAt (T% (g.curvatureNuContactVectorField
      cov hcov hLevi hdim t₀ x₀)) x₀ := by
  unfold curvatureNuContactVectorField
  exact firstOrderParallelSmoothExtend_mdifferentiableAt
    (I := I) (F := E) (V := TM) (cov t₀) x₀
      (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)

/-- Metric compatibility and the first-order parallel construction force the
spatial differential of the contact vector's metric square to vanish. -/
theorem mvfderiv_curvatureNuContactMetricSquare_eq_zero
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (u : TM x₀) :
    mvfderiv (I := I)
      (fun y => (g t₀).inner y
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y))
      x₀ u = 0 := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  let V := g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀
  have hV : MDiffAt (T% V) x₀ := by
    exact g.curvatureNuContactVectorField_mdifferentiableAt
      cov hcov hLevi hdim t₀ x₀
  have hmetric := (hLevi t₀).2 hV hV u
  have hparallel := g.covariantDerivative_curvatureNuContactVectorField_eq_zero
    cov hcov hLevi hdim t₀ x₀
  change mvfderiv (I := I) (fun y => Inner.inner ℝ (V y) (V y)) x₀ u = 0
  rw [hmetric]
  rw [hparallel]
  simp

/-- The spacetime Rayleigh quotient obtained from the contact vector field. -/
def curvatureNuSpacetimeSupport
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (p : ℝ × M) : ℝ :=
  g.curvatureRayleighQuotient cov hcov p.1 p.2
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)

/-- The spacetime support touches the least curvature eigenvalue at its
contact point. -/
theorem curvatureNuSpacetimeSupport_eq_at_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, x₀) =
      g.curvatureNu cov hcov hLevi hdim t₀ x₀ := by
  rw [curvatureNuSpacetimeSupport, curvatureNuContactVectorField,
    firstOrderParallelSmoothExtend_apply_center]
  exact g.curvatureRayleighQuotient_curvatureNuEigenvector
    cov hcov hLevi hdim t₀ x₀

/-- Joint continuity of the contact field's metric square makes the
spacetime support valid on a full neighborhood of the contact point. -/
theorem curvatureNu_le_spacetimeSupport_eventually
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M)
    (hnormContinuous : ContinuousAt
      (fun p : ℝ × M => (g p.1).inner p.2
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2))
      (t₀, x₀)) :
    ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p := by
  have hbase : (g t₀).inner x₀
      (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
      (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀) = 1 := by
    rw [curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t₀ x₀
  have hpositive : ∀ᶠ p in nhds (t₀, x₀),
      0 < (g p.1).inner p.2
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2) := by
    exact hnormContinuous.eventually
      (isOpen_Ioi.mem_nhds (by simpa [hbase]))
  filter_upwards [hpositive] with p hp
  exact g.curvatureNu_le_curvatureRayleighQuotient
    cov hcov hLevi hdim p.1 p.2 hp

end CovariantDerivative.TimeDependentRiemannianMetric
