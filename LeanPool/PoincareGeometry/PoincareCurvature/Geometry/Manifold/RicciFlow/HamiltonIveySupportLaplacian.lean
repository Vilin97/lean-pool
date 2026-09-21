/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySupportEvolution
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarEvolution
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearEvaluation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacianProduct

/-!
# Spatial Laplacian of the Hamilton--Ivey support

At a contact point the Rayleigh support is a quotient `a / d`, where `a` is
the curvature quadratic form and `d` is the evolving metric square of the
contact vector field.  On the open set where `d ≠ 0`, the identity

`support * d = a`

is exact.  Since `d = 1` and `dd = 0` at the contact point, the scalar
Laplacian product rule gives

`Δ support = Δa - ν Δd`.

This file proves that cancellation without assuming it as a PDE premise.
The remaining bridge is to identify the right-hand side with the connection
Laplacian of the curvature tensor on the contact eigenvector.
-/

@[expose] public noncomputable section
open Bundle Set Filter Topology
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
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

local instance supportLaplacianTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance supportLaplacianTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance

/-- The genuine Ricci tensor, continuously bundled on the finite-dimensional
tangent fibre. -/
def ricciCurvatureContinuous
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) : T₂ x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let L : TM x →ₗ[ℝ] (TM x →L[ℝ] ℝ) :=
    { toFun := fun u => LinearMap.toContinuousLinearMap
        (CovariantDerivative.ricciCurvature (cov := cov t) x u)
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro c u
        ext w
        simp }
  exact LinearMap.toContinuousLinearMap L

@[simp] theorem ricciCurvatureContinuous_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    g.ricciCurvatureContinuous cov hcov t x u v =
      g.ricciCurvature cov hcov t x u v := by
  rfl

/-- The genuine covariant two-tensor corresponding to the three-dimensional
Ricci-complement curvature endomorphism: `R g - 2 Ric`. -/
def curvatureOperatorTwoTensor
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) : T₂ x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact g.scalarCurvature cov hcov t x • (g t).inner x -
    (2 : ℝ) • g.ricciCurvatureContinuous cov hcov t x

@[simp] theorem curvatureOperatorTwoTensor_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    g.curvatureOperatorTwoTensor cov hcov t x u v =
      g.scalarCurvature cov hcov t x * (g t).inner x u v -
        2 * g.ricciCurvature cov hcov t x u v := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  simp [curvatureOperatorTwoTensor]

/-- The contact curvature tensor shifted by its least eigenvalue. -/
def curvatureNuShiftedContactTwoTensor
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (y : M) : T₂ y := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  exact g.curvatureOperatorTwoTensor cov hcov t₀ y -
    g.curvatureNu cov hcov hLevi hdim t₀ x₀ • (g t₀).inner y

@[simp] theorem curvatureNuShiftedContactTwoTensor_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ y : M) (u v : TM y) :
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀ y u v =
      g.curvatureOperatorTwoTensor cov hcov t₀ y u v -
        g.curvatureNu cov hcov hLevi hdim t₀ x₀ *
          (g t₀).inner y u v := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  simp [curvatureNuShiftedContactTwoTensor]

/-- The covariant curvature two-tensor is exactly the metric lowering of the
three-dimensional Ricci-complement curvature endomorphism. -/
theorem curvatureOperatorTwoTensor_eq_inner_curvatureEndomorphismApply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M) (u v : TM x) :
    g.curvatureOperatorTwoTensor cov hcov t x u v =
      (g t).inner x u (g.curvatureEndomorphismApply cov hcov t x v) := by
  rw [g.curvatureOperatorTwoTensor_apply]
  rw [g.inner_curvatureEndomorphismApply_bilinear]
  rw [g.ricciCurvature_symm_of_isLeviCivita cov hcov hLevi t x u v]

/-- The curvature two-tensor is symmetric for the Levi--Civita connection. -/
theorem curvatureOperatorTwoTensor_symm
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M) (u v : TM x) :
    g.curvatureOperatorTwoTensor cov hcov t x u v =
      g.curvatureOperatorTwoTensor cov hcov t x v u := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  simp only [curvatureOperatorTwoTensor_apply]
  rw [g.ricciCurvature_symm_of_isLeviCivita cov hcov hLevi t x u v]
  have hinner : (g t).inner x u v = (g t).inner x v u := by
    change Inner.inner ℝ u v = Inner.inner ℝ v u
    exact (real_inner_comm u v).symm
  rw [hinner]

/-- The spatial denominator of the contact Rayleigh quotient. -/
def curvatureNuContactMetricSquare
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (y : M) : ℝ :=
  (g t₀).inner y
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y)
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y)

/-- The spatial numerator of the contact Rayleigh quotient. -/
def curvatureNuContactNumerator
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (y : M) : ℝ :=
  let V := g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y
  (g t₀).inner y V (g.curvatureEndomorphismApply cov hcov t₀ y V)

@[simp] theorem curvatureNuContactMetricSquare_apply_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀ x₀ = 1 := by
  unfold curvatureNuContactMetricSquare curvatureNuContactVectorField
  rw [firstOrderParallelSmoothExtend_apply_center]
  exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t₀ x₀

/-- On every point where the denominator is nonzero, the support times its
denominator is exactly its curvature numerator. -/
theorem curvatureNuSpacetimeSupport_mul_metricSquare
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ y : M)
    (hden : g.curvatureNuContactMetricSquare
      cov hcov hLevi hdim t₀ x₀ y ≠ 0) :
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, y) *
        g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀ y =
      g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀ y := by
  unfold curvatureNuSpacetimeSupport curvatureRayleighQuotient
    curvatureNuContactMetricSquare curvatureNuContactNumerator
  exact div_mul_cancel₀ _ hden

/-- The spatial differential of the contact denominator vanishes. -/
theorem scalarDifferential_curvatureNuContactMetricSquare_eq_zero
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    scalarDifferential (I := I)
      (g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀) x₀ = 0 := by
  ext u
  exact g.mvfderiv_curvatureNuContactMetricSquare_eq_zero
    cov hcov hLevi hdim t₀ x₀ u

/-- The curvature quadratic form shifted by `ν` times the metric annihilates
the contact eigenvector in every tested direction.  This is the algebraic
fact that cancels the second spatial jet of the extended vector field. -/
theorem curvatureNu_shiftedContactKernel
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (w : TM x₀) :
    (g t₀).inner x₀ w
        (g.curvatureEndomorphismApply cov hcov t₀ x₀
          (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)) -
      g.curvatureNu cov hcov hLevi hdim t₀ x₀ *
        (g t₀).inner x₀ w
          (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀) = 0 := by
  rw [g.curvatureEndomorphismApply_curvatureNuEigenvector
    cov hcov hLevi hdim t₀ x₀]
  rw [map_smul]
  ring

/-- The shifted contact curvature tensor is symmetric. -/
theorem curvatureNuShiftedContactTwoTensor_symm
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ y : M) (u v : TM y) :
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀ y u v =
      g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀ y v u := by
  rw [g.curvatureNuShiftedContactTwoTensor_apply,
    g.curvatureNuShiftedContactTwoTensor_apply]
  rw [g.curvatureOperatorTwoTensor_symm cov hcov hLevi t₀ y u v]
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  have hinner : (g t₀).inner y u v = (g t₀).inner y v u := by
    change Inner.inner ℝ u v = Inner.inner ℝ v u
    exact (real_inner_comm u v).symm
  rw [hinner]

/-- The shifted tensor annihilates the contact eigenvector in its right slot. -/
theorem curvatureNuShiftedContactTwoTensor_kernel_right
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (w : TM x₀) :
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀ x₀ w
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀) = 0 := by
  rw [g.curvatureNuShiftedContactTwoTensor_apply]
  rw [g.curvatureOperatorTwoTensor_eq_inner_curvatureEndomorphismApply
    cov hcov hLevi]
  unfold curvatureNuContactVectorField
  rw [firstOrderParallelSmoothExtend_apply_center]
  exact g.curvatureNu_shiftedContactKernel cov hcov hLevi hdim t₀ x₀ w

/-- The shifted tensor also annihilates the contact eigenvector in its left
slot, by its geometrically proved symmetry. -/
theorem curvatureNuShiftedContactTwoTensor_kernel_left
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (w : TM x₀) :
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀ x₀
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀) w = 0 := by
  rw [g.curvatureNuShiftedContactTwoTensor_symm]
  exact g.curvatureNuShiftedContactTwoTensor_kernel_right
    cov hcov hLevi hdim t₀ x₀ w

/-- The numerator minus `ν` times the metric denominator is precisely the
shifted curvature tensor evaluated twice on the contact field. -/
theorem curvatureNuContactNumerator_sub_nu_mul_metricSquare
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ y : M) :
    g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀ y -
        g.curvatureNu cov hcov hLevi hdim t₀ x₀ *
          g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀ y =
      g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀ y
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y) := by
  rw [g.curvatureNuShiftedContactTwoTensor_apply]
  rw [g.curvatureOperatorTwoTensor_eq_inner_curvatureEndomorphismApply
    cov hcov hLevi]
  rfl

/-- **Contact quotient-Laplacian identity.**  The assumptions are only the
second-order regularity needed to form the three scalar Laplacians and an open
neighborhood on which the contact vector remains nonzero.  The quotient
cancellation itself is proved. -/
theorem scalarLaplacian_curvatureNuSpacetimeSupport_eq
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (U : Set M)
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hden : ∀ y ∈ U, g.curvatureNuContactMetricSquare
      cov hcov hLevi hdim t₀ x₀ y ≠ 0)
    (hq : ∀ᶠ y in 𝓝 x₀, MDiffAt
      (fun z => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t₀ x₀ (t₀, z)) y)
    (hd : ∀ y, MDiffAt
      (g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀) y)
    (hDq : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (fun z => g.curvatureNuSpacetimeSupport
            cov hcov hLevi hdim t₀ x₀ (t₀, z)) y)) x₀)
    (hDd : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (g.curvatureNuContactMetricSquare
            cov hcov hLevi hdim t₀ x₀) y)) x₀)
    (hDa : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (g.curvatureNuContactNumerator
            cov hcov hLevi hdim t₀ x₀) y)) x₀) :
    g.scalarLaplacian cov
        (fun _ y => g.curvatureNuSpacetimeSupport
          cov hcov hLevi hdim t₀ x₀ (t₀, y)) t₀ x₀ =
      g.scalarLaplacian cov
          (fun _ => g.curvatureNuContactNumerator
            cov hcov hLevi hdim t₀ x₀) t₀ x₀ -
        g.curvatureNu cov hcov hLevi hdim t₀ x₀ *
          g.scalarLaplacian cov
            (fun _ => g.curvatureNuContactMetricSquare
              cov hcov hLevi hdim t₀ x₀) t₀ x₀ := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  let q : M → ℝ := fun y => g.curvatureNuSpacetimeSupport
    cov hcov hLevi hdim t₀ x₀ (t₀, y)
  let d : M → ℝ :=
    g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀
  let a : M → ℝ :=
    g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀
  have hDprod : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (q * d) y)) x₀ := by
    have hsum : MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          ((q • scalarDifferential (I := I) d +
            d • scalarDifferential (I := I) q) y)) x₀ := by
      exact mdifferentiableAt_add_section
        ((hq.self_of_nhds).smul_section hDd)
        ((hd x₀).smul_section hDq)
    have hchain : ∀ᶠ y in 𝓝 x₀,
        scalarDifferential (I := I) (q * d) y =
          (q • scalarDifferential (I := I) d +
            d • scalarDifferential (I := I) q) y := by
      filter_upwards [hq] with y hqy
      exact scalarDifferential_mul (I := I) hqy (hd y)
    have hsections :
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I) (q * d) y)) =ᶠ[𝓝 x₀]
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          ((q • scalarDifferential (I := I) d +
            d • scalarDifferential (I := I) q) y)) := by
      filter_upwards [hchain] with y hy
      rw [hy]
    exact hsum.congr_of_eventuallyEq hsections
  have hcongr : CovariantDerivative.scalarLaplacian (cov t₀) (q * d) x₀ =
      CovariantDerivative.scalarLaplacian (cov t₀) a x₀ := by
    apply scalarLaplacian_congr_on_open (cov t₀) hU hx₀
    · intro y hy
      exact g.curvatureNuSpacetimeSupport_mul_metricSquare
        cov hcov hLevi hdim t₀ x₀ y (hden y hy)
    · exact hDprod
    · exact hDa
  have hprod :=
    scalarLaplacian_mul_of_second_differential_eq_zero_of_eventually_mdifferentiableAt
      (cov t₀) hq (Filter.Eventually.of_forall hd) hDq hDd
      (g.scalarDifferential_curvatureNuContactMetricSquare_eq_zero
        cov hcov hLevi hdim t₀ x₀)
  have hq0 : q x₀ = g.curvatureNu cov hcov hLevi hdim t₀ x₀ := by
    exact g.curvatureNuSpacetimeSupport_eq_at_contact
      cov hcov hLevi hdim t₀ x₀
  have hd0 : d x₀ = 1 := by
    exact g.curvatureNuContactMetricSquare_apply_contact
      cov hcov hLevi hdim t₀ x₀
  dsimp [q, d, a] at hcongr ⊢
  dsimp [q, d] at hprod hq0 hd0
  rw [hq0, hd0, one_mul] at hprod
  linarith

/-- **Geometric contact-Laplacian bridge.**  The scalar Laplacian of the
Hamilton--Ivey support is the connection Laplacian of the genuine shifted
curvature two-tensor evaluated on the contact eigenvector.  Only ordinary
second-order regularity is assumed; the quotient cancellation, eigenvector
kernel cancellation, and tensor identification are all proved above. -/
theorem scalarLaplacian_curvatureNuSpacetimeSupport_eq_connectionLaplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (U : Set M)
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hden : ∀ y ∈ U, g.curvatureNuContactMetricSquare
      cov hcov hLevi hdim t₀ x₀ y ≠ 0)
    (hq : ∀ᶠ y in 𝓝 x₀, MDiffAt
      (fun z => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t₀ x₀ (t₀, z)) y)
    (hd : ∀ y, MDiffAt
      (g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀) y)
    (ha : ∀ y, MDiffAt
      (g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀) y)
    (hDq : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (fun z => g.curvatureNuSpacetimeSupport
            cov hcov hLevi hdim t₀ x₀ (t₀, z)) y)) x₀)
    (hDd : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (g.curvatureNuContactMetricSquare
            cov hcov hLevi hdim t₀ x₀) y)) x₀)
    (hDa : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (g.curvatureNuContactNumerator
            cov hcov hLevi hdim t₀ x₀) y)) x₀)
    (hh : ∀ y, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        (g.curvatureNuShiftedContactTwoTensor
          cov hcov hLevi hdim t₀ x₀ z)) y)
    (hV : ∀ y, MDiffAt
      (T% (g.curvatureNuContactVectorField
        cov hcov hLevi hdim t₀ x₀)) y)
    (hfirst : letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
      letI : ∀ x, NormedAddCommGroup (T₂ x) := fun _ => inferInstance
      letI : ∀ x, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
      MDiffAt
        (fun y => TotalSpace.mk'
          (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
          (E := T₃) y
          (covariantTwoTensorCovariantDerivative (cov t₀)
            (g.curvatureNuShiftedContactTwoTensor
              cov hcov hLevi hdim t₀ x₀) y)) x₀)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (fun z =>
            g.curvatureNuShiftedContactTwoTensor
                cov hcov hLevi hdim t₀ x₀ z
              (g.curvatureNuContactVectorField
                cov hcov hLevi hdim t₀ x₀ z)
              (g.curvatureNuContactVectorField
                cov hcov hLevi hdim t₀ x₀ z)) y)) x₀)
    (hsecondV : ∀ z : TM x₀, MDiffAt
      (T% (fun y => cov t₀
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀) y
        (smoothExtend (I := I) (F := E) (V := TM) x₀ z y))) x₀) :
    letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (T₂ x) := fun _ => inferInstance
    letI : ∀ x, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
    g.scalarLaplacian cov
        (fun _ y => g.curvatureNuSpacetimeSupport
          cov hcov hLevi hdim t₀ x₀ (t₀, y)) t₀ x₀ =
      connectionLaplacian (cov t₀)
          (g.curvatureNuShiftedContactTwoTensor
            cov hcov hLevi hdim t₀ x₀) x₀
        (g.curvatureNuContactVectorField
          cov hcov hLevi hdim t₀ x₀ x₀)
        (g.curvatureNuContactVectorField
          cov hcov hLevi hdim t₀ x₀ x₀) := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  letI : ∀ x, NormedAddCommGroup (T₂ x) := fun _ => inferInstance
  letI : ∀ x, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
  let q : M → ℝ := fun y => g.curvatureNuSpacetimeSupport
    cov hcov hLevi hdim t₀ x₀ (t₀, y)
  let d : M → ℝ :=
    g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀
  let a : M → ℝ :=
    g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀
  let V : ∀ y : M, TM y :=
    g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀
  let A : ∀ y : M, T₂ y :=
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀
  let nu := g.curvatureNu cov hcov hLevi hdim t₀ x₀
  have hquot := g.scalarLaplacian_curvatureNuSpacetimeSupport_eq
    cov hcov hLevi hdim t₀ x₀ U hU hx₀ hden hq hd hDq hDd hDa
  have hlinear := scalarLaplacian_add_smul_const
    (cov t₀) (-nu) ha hd hDa hDd
  have heval : a + (-nu) • d = fun y => A y (V y) (V y) := by
    funext y
    dsimp [a, d, A, V, nu]
    simpa [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg] using
      g.curvatureNuContactNumerator_sub_nu_mul_metricSquare
        cov hcov hLevi hdim t₀ x₀ y
  have hbilinear :=
    scalarLaplacian_bilinear_self_eq_connectionLaplacian_of_contactKernel
      (cov t₀) A V x₀ hh hV hfirst hdf hsecondV
      (g.covariantDerivative_curvatureNuContactVectorField_eq_zero
        cov hcov hLevi hdim t₀ x₀)
      (g.curvatureNuShiftedContactTwoTensor_kernel_right
        cov hcov hLevi hdim t₀ x₀)
      (g.curvatureNuShiftedContactTwoTensor_kernel_left
        cov hcov hLevi hdim t₀ x₀)
  rw [← heval] at hbilinear
  dsimp [q, d, a, V, A, nu] at hquot hlinear hbilinear ⊢
  linarith

/-! The following structure packages exactly the geometric regularity data
used by the bridge above.  It is kept next to that theorem so the dependent
bundle instances for the first covariant derivative are elaborated in the
same context as the proved bridge, rather than reconstructed by a downstream
certificate. -/

structure HamiltonIveySupportLaplacianCertificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) where
  U : Set M
  hU : IsOpen U
  hx₀ : x₀ ∈ U
  hden : ∀ y ∈ U, g.curvatureNuContactMetricSquare
    cov hcov hLevi hdim t₀ x₀ y ≠ 0
  hq : ∀ᶠ y in 𝓝 x₀, MDiffAt
    (fun z => g.curvatureNuSpacetimeSupport
      cov hcov hLevi hdim t₀ x₀ (t₀, z)) y
  hd : ∀ y, MDiffAt
    (g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀) y
  ha : ∀ y, MDiffAt
    (g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀) y
  hDq : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (scalarDifferential (I := I)
        (fun z => g.curvatureNuSpacetimeSupport
          cov hcov hLevi hdim t₀ x₀ (t₀, z)) y)) x₀
  hDd : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (scalarDifferential (I := I)
        (g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀) y)) x₀
  hDa : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (scalarDifferential (I := I)
        (g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀) y)) x₀
  hh : ∀ y, MDiffAt
    (fun z => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
      (g.curvatureNuShiftedContactTwoTensor
        cov hcov hLevi hdim t₀ x₀ z)) y
  hV : ∀ y, MDiffAt
    (T% (g.curvatureNuContactVectorField
      cov hcov hLevi hdim t₀ x₀)) y
  hfirst : letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (T₂ x) := fun _ => inferInstance
    letI : ∀ x, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
    MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t₀)
          (g.curvatureNuShiftedContactTwoTensor
            cov hcov hLevi hdim t₀ x₀) y)) x₀
  hdf : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (scalarDifferential (I := I)
        (fun z =>
          g.curvatureNuShiftedContactTwoTensor
              cov hcov hLevi hdim t₀ x₀ z
            (g.curvatureNuContactVectorField
              cov hcov hLevi hdim t₀ x₀ z)
            (g.curvatureNuContactVectorField
              cov hcov hLevi hdim t₀ x₀ z)) y)) x₀
  hsecondV : ∀ z : TM x₀, MDiffAt
    (T% (fun y => cov t₀
      (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀) y
      (smoothExtend (I := I) (F := E) (V := TM) x₀ z y))) x₀

end CovariantDerivative.TimeDependentRiemannianMetric
