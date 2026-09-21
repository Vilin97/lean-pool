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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySupport
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence

/-!
# Time variation of the least-curvature support

The contact vector field used in the Hamilton--Ivey support construction is
fixed in time.  Consequently, along an actual Ricci flow its metric square
has the exact derivative `-2 Ric(V,V)`.  This file also rewrites the Rayleigh
support itself as `R - 2 Ric(V,V) / |V|^2`, directly from the genuine
Ricci-complement curvature endomorphism.
-/

@[expose] public noncomputable section
open Bundle Set
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

/-- Bilinear form of the Ricci-complement curvature endomorphism.  This is
the unspecialized identity behind the Rayleigh numerator. -/
theorem inner_curvatureEndomorphismApply_bilinear
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    (g t).inner x u (g.curvatureEndomorphismApply cov hcov t x v) =
      g.scalarCurvature cov hcov t x * (g t).inner x u v -
        2 * g.ricciCurvature cov hcov t x v u := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change Inner.inner ℝ u
      (CovariantDerivative.ricciComplementEndomorphism (cov t) x v) = _
  have hraised : Inner.inner ℝ u
      (CovariantDerivative.raisedRicciEndomorphism (cov t) x v) =
      CovariantDerivative.ricciCurvature (cov := cov t) x v u := by
    rw [real_inner_comm]
    exact CovariantDerivative.inner_raisedRicciEndomorphism (cov t) x v u
  rw [CovariantDerivative.ricciComplementEndomorphism_apply]
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  rw [hraised]
  rfl

/-- The numerator of the curvature Rayleigh quotient is the scalar-curvature
term minus twice the genuine Ricci quadratic form. -/
theorem inner_curvatureEndomorphismApply_eq_scalarCurvature_mul_inner_sub_ricci
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) (v : TM x) :
    (g t).inner x v (g.curvatureEndomorphismApply cov hcov t x v) =
      g.scalarCurvature cov hcov t x * (g t).inner x v v -
        2 * g.ricciCurvature cov hcov t x v v := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change Inner.inner ℝ v
      (CovariantDerivative.ricciComplementEndomorphism (cov t) x v) = _
  calc
    Inner.inner ℝ v
        (CovariantDerivative.ricciComplementEndomorphism (cov t) x v) =
        Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x v) v :=
      real_inner_comm _ _
    _ = CovariantDerivative.scalarCurvature (cov := cov t) x * ‖v‖ ^ 2 -
        2 * CovariantDerivative.ricciCurvature (cov := cov t) x v v :=
      CovariantDerivative.inner_ricciComplementEndomorphism (cov t) x v
    _ = _ := by
      rw [← real_inner_self_eq_norm_sq]
      rfl

/-- The Rayleigh quotient of the actual three-dimensional curvature
endomorphism is scalar curvature minus twice the normalized Ricci quadratic
form. -/
theorem curvatureRayleighQuotient_eq_scalarCurvature_sub_ricci
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (x : M) (v : TM x)
    (hv : (g t).inner x v v ≠ 0) :
    g.curvatureRayleighQuotient cov hcov t x v =
      g.scalarCurvature cov hcov t x -
        2 * g.ricciCurvature cov hcov t x v v /
          (g t).inner x v v := by
  rw [curvatureRayleighQuotient]
  rw [g.inner_curvatureEndomorphismApply_eq_scalarCurvature_mul_inner_sub_ricci
    cov hcov t x v]
  field_simp [hv]

/-- On the genuine least-curvature eigenvector, twice the Ricci quadratic
form is `R - nu`.  In dimension three this is equivalently `lambda + mu`. -/
theorem two_mul_ricci_curvatureNuEigenvector_eq_lambda_add_mu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    2 * g.ricciCurvature cov hcov t x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x)
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x) =
      g.curvatureLambda cov hcov hLevi hdim t x +
        g.curvatureMu cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  change 2 * CovariantDerivative.ricciCurvature (cov := cov t) x
      (g.curvatureNuEigenvector cov hcov hLevi hdim t x)
      (g.curvatureNuEigenvector cov hcov hLevi hdim t x) = _
  let v := g.curvatureNuEigenvector cov hcov hLevi hdim t x
  have hv : (g t).inner x v v = 1 := by
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hq := g.curvatureRayleighQuotient_eq_scalarCurvature_sub_ricci
    cov hcov t x v (by rw [hv]; norm_num)
  rw [g.curvatureRayleighQuotient_curvatureNuEigenvector
    cov hcov hLevi hdim t x, hv, div_one] at hq
  change g.curvatureNu cov hcov hLevi hdim t x =
    g.scalarCurvature cov hcov t x -
      2 * g.ricciCurvature cov hcov t x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x)
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x) at hq
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x
  change g.curvatureLambda cov hcov hLevi hdim t x +
    g.curvatureMu cov hcov hLevi hdim t x +
      g.curvatureNu cov hcov hLevi hdim t x =
        CovariantDerivative.scalarCurvature (cov := cov t) x at hsum
  dsimp [v] at hq
  calc
    2 * CovariantDerivative.ricciCurvature (cov := cov t) x
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x)
        (g.curvatureNuEigenvector cov hcov hLevi hdim t x) =
        2 * LinearMap.trace ℝ (TM x)
          (CovariantDerivative.ricciEndomorphism (cov := cov t) x
            (g.curvatureNuEigenvector cov hcov hLevi hdim t x)
            (g.curvatureNuEigenvector cov hcov hLevi hdim t x)) := by rfl
    _ = _ := by linarith

/-- Along a genuine Ricci flow, the metric square of any fixed tangent
vector has time derivative `-2 Ric(v,v)`. -/
theorem hasDerivAt_inner_self_of_isRicciFlowOn
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M) (v : TM x) :
    HasDerivAt (fun τ => (g τ).inner x v v)
      (-2 * g.ricciCurvature cov hcov t x v v) t := by
  have hmetric := hflow.2.1 ht x v v
  have heq := hflow.2.2 ht x v v
  change HasDerivAt (fun τ => (g τ).inner x v v) (gdot t x v v) t at hmetric
  rw [heq] at hmetric
  simpa [RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor]
    using hmetric

/-- The denominator of the spacetime least-eigenvalue support therefore has
the exact Ricci-flow derivative at its contact point. -/
theorem hasDerivAt_curvatureNuContactMetricSquare
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (x₀ : M) :
    HasDerivAt
      (fun τ => (g τ).inner x₀
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀))
      (-2 * g.ricciCurvature cov hcov t₀ x₀
        (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)
        (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)) t₀ := by
  simpa [curvatureNuContactVectorField,
    firstOrderParallelSmoothExtend_apply_center] using
    g.hasDerivAt_inner_self_of_isRicciFlowOn cov hcov gdot s hflow ht₀ x₀
      (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)

/-- At the contact point, the time derivative of the genuine spacetime
Rayleigh support is reduced to the time derivatives of scalar curvature and
the Ricci tensor.  The `-4 Ric(V,V)^2` term is forced by the evolving metric
in the quotient denominator. -/
theorem hasDerivAt_curvatureNuSpacetimeSupport_time_of_isRicciFlowOn
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (x₀ : M)
    (scalarVelocity ricciVelocity : ℝ)
    (hscalar : HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x₀) scalarVelocity t₀)
    (hricci : HasDerivAt
      (fun τ => g.ricciCurvature cov hcov τ x₀
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀))
      ricciVelocity t₀) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t₀ x₀ (τ, x₀))
      (scalarVelocity - 2 * ricciVelocity -
        4 * (g.ricciCurvature cov hcov t₀ x₀
          (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)
          (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)) ^ 2) t₀ := by
  let V : TM x₀ :=
    g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀
  let d : ℝ → ℝ := fun τ => (g τ).inner x₀ V V
  let R : ℝ → ℝ := fun τ => g.scalarCurvature cov hcov τ x₀
  let r : ℝ → ℝ := fun τ => g.ricciCurvature cov hcov τ x₀ V V
  have hV : V = g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀ := by
    simp [V, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hd0 : d t₀ = 1 := by
    simp only [d, hV]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t₀ x₀
  have hd : HasDerivAt d (-2 * r t₀) t₀ := by
    simpa [d, r] using
      g.hasDerivAt_inner_self_of_isRicciFlowOn
        cov hcov gdot s hflow ht₀ x₀ V
  have hR : HasDerivAt R scalarVelocity t₀ := by simpa [R] using hscalar
  have hr : HasDerivAt r ricciVelocity t₀ := by simpa [r, V] using hricci
  have hnum := (hR.mul hd).sub (hr.const_mul 2)
  have hquot := hnum.div hd (by simpa [hd0])
  have hfun : (fun τ => g.curvatureNuSpacetimeSupport
      cov hcov hLevi hdim t₀ x₀ (τ, x₀)) =
      (fun τ => (R τ * d τ - 2 * r τ) / d τ) := by
    funext τ
    rw [curvatureNuSpacetimeSupport, curvatureRayleighQuotient]
    rw [g.inner_curvatureEndomorphismApply_eq_scalarCurvature_mul_inner_sub_ricci
      cov hcov τ x₀ V]
  rw [hfun]
  apply hquot.congr_deriv
  have hr0 : r t₀ = g.ricciCurvature cov hcov t₀ x₀
      (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)
      (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀) := by
    simp [r, hV]
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [hd0, hr0]
  ring

/-- The same contact-time derivative in curvature-eigenvalue form.  This is
the normalization used by the three-dimensional Hamilton--Ivey reaction
calculation. -/
theorem hasDerivAt_curvatureNuSpacetimeSupport_time_eigenvalue_form
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (x₀ : M)
    (scalarVelocity ricciVelocity : ℝ)
    (hscalar : HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x₀) scalarVelocity t₀)
    (hricci : HasDerivAt
      (fun τ => g.ricciCurvature cov hcov τ x₀
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀))
      ricciVelocity t₀) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t₀ x₀ (τ, x₀))
      (scalarVelocity - 2 * ricciVelocity -
        (g.curvatureLambda cov hcov hLevi hdim t₀ x₀ +
          g.curvatureMu cov hcov hLevi hdim t₀ x₀) ^ 2) t₀ := by
  have h := g.hasDerivAt_curvatureNuSpacetimeSupport_time_of_isRicciFlowOn
    cov hcov hLevi hdim gdot s hflow ht₀ x₀ scalarVelocity ricciVelocity
    hscalar hricci
  apply h.congr_deriv
  have hRic := g.two_mul_ricci_curvatureNuEigenvector_eq_lambda_add_mu
    cov hcov hLevi hdim t₀ x₀
  rw [← hRic]
  ring

end CovariantDerivative.TimeDependentRiemannianMetric
