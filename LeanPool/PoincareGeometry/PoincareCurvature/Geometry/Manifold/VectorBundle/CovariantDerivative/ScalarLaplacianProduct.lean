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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacian

/-!
# Product rules for the scalar Laplacian

The scalar differential and Hessian satisfy their intrinsic Leibniz rules.
Tracing the Hessian gives the Laplace--Beltrami product rule, together with the
critical-factor specialization used for Rayleigh quotients at a contact point.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- Leibniz rule for the intrinsic scalar differential. -/
theorem scalarDifferential_mul {f g : M → ℝ} {x : M}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    scalarDifferential (I := I) (f * g) x =
      f x • scalarDifferential (I := I) g x +
        g x • scalarDifferential (I := I) f x := by
  exact mvfderiv_mul (I := I) hf hg

/-- Pointwise Hessian Leibniz rule.  The two cross terms retain their order,
so no torsion or Hessian-symmetry premise is needed. -/
theorem scalarHessian_mul_apply
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hg : ∀ y, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x)
    (u v : TM x) :
    scalarHessian cov (f * g) x u v =
      f x * scalarHessian cov g x u v +
      scalarDifferential (I := I) f x u * scalarDifferential (I := I) g x v +
      g x * scalarHessian cov f x u v +
      scalarDifferential (I := I) g x u * scalarDifferential (I := I) f x v := by
  have hdiff : scalarDifferential (I := I) (f * g) =
      f • scalarDifferential (I := I) g +
        g • scalarDifferential (I := I) f := by
    funext y
    exact scalarDifferential_mul (I := I) (hf y) (hg y)
  have hfdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((f • scalarDifferential (I := I) g) y)) x :=
    (hf x).smul_section hdg
  have hgdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((g • scalarDifferential (I := I) f) y)) x :=
    (hg x).smul_section hdf
  have hadd := (covectorCovariantDerivative cov).isCovariantDerivativeOn.add
    hfdg hgdf (x := x)
  have hleft := (covectorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
    hdg (hf x) (x := x)
  have hright := (covectorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
    hdf (hg x) (x := x)
  have hadd_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hadd
  have hleft_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hleft
  have hright_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hright
  unfold scalarHessian
  rw [hdiff, hadd_uv]
  simp only [add_apply]
  rw [hleft_uv, hright_uv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have hfdu : (d% f x) u = scalarDifferential (I := I) f x u := rfl
  have hgdu : (d% g x) u = scalarDifferential (I := I) g x u := rfl
  rw [hfdu, hgdu]
  ring

/-- Local-neighborhood version of the scalar-Hessian product rule.  Only
regularity near the base point is needed; this is the form used when an
outer nonlinear profile is defined on an open range such as `q < 0`. -/
theorem scalarHessian_mul_apply_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hg : ∀ᶠ y in 𝓝 x, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x)
    (u v : TM x) :
    scalarHessian cov (f * g) x u v =
      f x * scalarHessian cov g x u v +
      scalarDifferential (I := I) f x u * scalarDifferential (I := I) g x v +
      g x * scalarHessian cov f x u v +
      scalarDifferential (I := I) g x u * scalarDifferential (I := I) f x v := by
  have hf₀ : MDiffAt f x := hf.self_of_nhds
  have hg₀ : MDiffAt g x := hg.self_of_nhds
  have hfdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((f • scalarDifferential (I := I) g) y)) x :=
    hf₀.smul_section hdg
  have hgdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((g • scalarDifferential (I := I) f) y)) x :=
    hg₀.smul_section hdf
  have hsum := mdifferentiableAt_add_section hfdg hgdf
  have hchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) (f * g) y =
        (f • scalarDifferential (I := I) g +
          g • scalarDifferential (I := I) f) y := by
    filter_upwards [hf, hg] with y hfy hgy
    exact scalarDifferential_mul (I := I) hfy hgy
  have hsections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (f * g) y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((f • scalarDifferential (I := I) g +
          g • scalarDifferential (I := I) f) y)) := by
    filter_upwards [hchain] with y hy
    rw [hy]
  have hproduct := hsum.congr_of_eventuallyEq hsections
  have hconn := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := (covectorCovariantDerivative cov).isCovariantDerivativeOnUniv)
    hproduct hsum Filter.univ_mem hchain
  have hadd := (covectorCovariantDerivative cov).isCovariantDerivativeOn.add
    hfdg hgdf (x := x)
  have hleft := (covectorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
    hdg hf₀ (x := x)
  have hright := (covectorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
    hdf hg₀ (x := x)
  have hconn_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hconn
  have hadd_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hadd
  have hleft_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hleft
  have hright_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hright
  unfold scalarHessian
  rw [hconn_uv, hadd_uv]
  simp only [add_apply]
  rw [hleft_uv, hright_uv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  have hfdu : (d% f x) u = scalarDifferential (I := I) f x u := rfl
  have hgdu : (d% g x) u = scalarDifferential (I := I) g x u := rfl
  rw [hfdu, hgdu]
  ring

/-- Local-neighborhood additivity of the scalar Hessian. -/
theorem scalarHessian_add_apply_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hg : ∀ᶠ y in 𝓝 x, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x)
    (u v : TM x) :
    scalarHessian cov (f + g) x u v =
      scalarHessian cov f x u v + scalarHessian cov g x u v := by
  have hf₀ : MDiffAt f x := hf.self_of_nhds
  have hg₀ : MDiffAt g x := hg.self_of_nhds
  have hsum := mdifferentiableAt_add_section hdf hdg
  have hchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) (f + g) y =
        scalarDifferential (I := I) f y +
          scalarDifferential (I := I) g y := by
    filter_upwards [hf, hg] with y hfy hgy
    ext w
    change mvfderiv (I := I) (f + g) y w = _
    rw [mvfderiv_add (I := I) hfy hgy]
    rfl
  have hsections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (f + g) y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y +
          scalarDifferential (I := I) g y)) := by
    filter_upwards [hchain] with y hy
    rw [hy]
  have hsum' := hsum.congr_of_eventuallyEq hsections
  have hconn := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := (covectorCovariantDerivative cov).isCovariantDerivativeOnUniv)
    hsum' hsum Filter.univ_mem hchain
  have hadd := (covectorCovariantDerivative cov).isCovariantDerivativeOn.add
    hdf hdg (x := x)
  have hconnUV := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hconn
  have haddUV := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hadd
  unfold scalarHessian
  rw [hconnUV, haddUV]
  simp only [add_apply]

/-- Local-neighborhood Laplace--Beltrami product rule. -/
theorem scalarLaplacian_add_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hg : ∀ᶠ y in 𝓝 x, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x) :
    scalarLaplacian cov (f + g) x =
      scalarLaplacian cov f x + scalarLaplacian cov g x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (f + g) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b]
  simp_rw [scalarHessian_add_apply_of_eventually_mdifferentiableAt
    cov hf hg hdf hdg]
  exact Finset.sum_add_distrib

/-- Adding a spatial constant does not change the scalar Laplacian, under
the local regularity hypotheses used by the maximum principle. -/
theorem scalarLaplacian_add_const_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) {f : M → ℝ} {x : M} (c : ℝ)
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x) :
    scalarLaplacian cov (fun y => f y + c) x =
      scalarLaplacian cov f x := by
  have hzero (y : M) :
      scalarDifferential (I := I) (fun _ : M => c) y = 0 := by
    ext u
    simp only [scalarDifferential_apply]
    rw [mvfderiv_const]
  have hdfConst : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (fun _ : M => c) y)) x := by
    have hz :
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I) (fun _ : M => c) y)) =
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y 0) := by
      funext y
      congr 1
      exact hzero y
    rw [hz]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
      (F := E →L[ℝ] ℝ) (E := T₁) (x := x)
  change scalarLaplacian cov
    (f + (fun _ : M => c)) x = scalarLaplacian cov f x
  rw [scalarLaplacian_add_of_eventually_mdifferentiableAt
    cov hf (Filter.Eventually.of_forall fun y => mdifferentiableAt_const)
      hdf hdfConst]
  rw [scalarLaplacian_const]
  simp

/-- Local-neighborhood homogeneity of the scalar Hessian under a constant
scalar. -/
theorem scalarHessian_smul_const_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) (c : ℝ) {f : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (u v : TM x) :
    scalarHessian cov (c • f) x u v =
      c * scalarHessian cov f x u v := by
  have hf₀ : MDiffAt f x := hf.self_of_nhds
  have hchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) (c • f) y =
        (c • scalarDifferential (I := I) f) y := by
    filter_upwards [hf] with y hfy
    ext w
    simp only [scalarDifferential_apply, Pi.smul_apply, smul_apply]
    change mvfderiv (I := I) ((fun _ : M => c) * f) y w =
      c * mvfderiv (I := I) f y w
    rw [mvfderiv_mul (I := I) mdifferentiableAt_const hfy]
    rw [mvfderiv_const]
    simp
  have hsections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (c • f) y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((c • scalarDifferential (I := I) f) y)) := by
    filter_upwards [hchain] with y hy
    rw [hy]
  let hscaled : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((c • scalarDifferential (I := I) f) y)) x :=
    (mdifferentiableAt_const : MDiffAt (fun _ : M => c) x).smul_section hdf
  have hdf' := hscaled.congr_of_eventuallyEq hsections
  have hconn' := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := (covectorCovariantDerivative cov).isCovariantDerivativeOnUniv)
    hdf' hscaled Filter.univ_mem hchain
  have hconn :=
    (covectorCovariantDerivative cov).isCovariantDerivativeOn.smul_const c hdf
  unfold scalarHessian
  rw [hconn', hconn]
  simp [smul_eq_mul]

/-- Local-neighborhood homogeneity of the Laplacian under a constant scalar. -/
theorem scalarLaplacian_smul_const_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) (c : ℝ) {f : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x) :
    scalarLaplacian cov (c • f) x = c * scalarLaplacian cov f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  have hf₀ : MDiffAt f x := hf.self_of_nhds
  have hchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) (c • f) y =
        (c • scalarDifferential (I := I) f) y := by
    filter_upwards [hf] with y hfy
    ext v
    simp only [scalarDifferential_apply, Pi.smul_apply, smul_apply]
    change mvfderiv (I := I) ((fun _ : M => c) * f) y v =
      c * mvfderiv (I := I) f y v
    rw [mvfderiv_mul (I := I) mdifferentiableAt_const hfy]
    rw [mvfderiv_const]
    simp
  have hsections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (c • f) y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((c • scalarDifferential (I := I) f) y)) := by
    filter_upwards [hchain] with y hy
    rw [hy]
  have hdf' : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (c • f) y)) x := by
    exact ((mdifferentiableAt_const : MDiffAt (fun _ : M => c) x).smul_section
      hdf).congr_of_eventuallyEq hsections
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (c • f) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_smul_const_of_eventually_mdifferentiableAt
    cov c hf hdf]
  simp [b, smul_apply, Finset.mul_sum]

/-- Local-neighborhood scalar Laplace--Beltrami product rule. -/
theorem scalarLaplacian_mul_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hg : ∀ᶠ y in 𝓝 x, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x) :
    scalarLaplacian cov (f * g) x =
      f x * scalarLaplacian cov g x +
        (∑ i : Fin (Module.finrank ℝ (TM x)),
          scalarDifferential (I := I) f x
            (stdOrthonormalBasis ℝ (TM x) i) *
          scalarDifferential (I := I) g x
            (stdOrthonormalBasis ℝ (TM x) i)) +
        g x * scalarLaplacian cov f x +
        (∑ i : Fin (Module.finrank ℝ (TM x)),
          scalarDifferential (I := I) g x
            (stdOrthonormalBasis ℝ (TM x) i) *
          scalarDifferential (I := I) f x
            (stdOrthonormalBasis ℝ (TM x) i)) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (f * g) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_mul_apply_of_eventually_mdifferentiableAt
    cov hf hg hdf hdg]
  simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, b]

/-- Local-neighborhood product rule at a critical point of the second
factor.  This is the quotient form of the product rule: only eventual
differentiability near the base point is required. -/
theorem scalarLaplacian_mul_of_second_differential_eq_zero_of_eventually_mdifferentiableAt
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hg : ∀ᶠ y in 𝓝 x, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x)
    (hgcritical : scalarDifferential (I := I) g x = 0) :
    scalarLaplacian cov (f * g) x =
      f x * scalarLaplacian cov g x + g x * scalarLaplacian cov f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (f * g) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_mul_apply_of_eventually_mdifferentiableAt
    cov hf hg hdf hdg]
  simp only [hgcritical, zero_apply, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Full scalar Laplace--Beltrami product rule.  Both gradient cross terms
are retained separately, so the formula needs no symmetry assumption on the
scalar Hessian. -/
theorem scalarLaplacian_mul
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hg : ∀ y, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x) :
    scalarLaplacian cov (f * g) x =
      f x * scalarLaplacian cov g x +
        (∑ i : Fin (Module.finrank ℝ (TM x)),
          scalarDifferential (I := I) f x
            (stdOrthonormalBasis ℝ (TM x) i) *
          scalarDifferential (I := I) g x
            (stdOrthonormalBasis ℝ (TM x) i)) +
        g x * scalarLaplacian cov f x +
        (∑ i : Fin (Module.finrank ℝ (TM x)),
          scalarDifferential (I := I) g x
            (stdOrthonormalBasis ℝ (TM x) i) *
          scalarDifferential (I := I) f x
          (stdOrthonormalBasis ℝ (TM x) i)) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (f * g) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_mul_apply cov hf hg hdf hdg]
  simp [Finset.sum_add_distrib, Finset.mul_sum, b]

/-- At a critical point of the second factor, the scalar Laplacian product
rule has no gradient cross term. -/
theorem scalarLaplacian_mul_of_second_differential_eq_zero
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hg : ∀ y, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x)
    (hgcritical : scalarDifferential (I := I) g x = 0) :
    scalarLaplacian cov (f * g) x =
      f x * scalarLaplacian cov g x + g x * scalarLaplacian cov f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (f * g) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_mul_apply cov hf hg hdf hdg]
  simp only [hgcritical, zero_apply, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Scalar Laplacians agree when the functions agree on an open neighborhood
and both differential sections are differentiable at the base point.  This is
the second-order germ principle needed when a quotient identity holds only on
the open set where its denominator is nonzero. -/
theorem scalarLaplacian_congr_on_open
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {U : Set M} {x : M}
    (hU : IsOpen U) (hx : x ∈ U) (hfg : ∀ y ∈ U, f y = g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x) :
    scalarLaplacian cov f x = scalarLaplacian cov g x := by
  have hdiff : ∀ᶠ y in nhds x,
      scalarDifferential (I := I) f y = scalarDifferential (I := I) g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hfg_y : f =ᶠ[nhds y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hfg z hz
    exact hfg_y.mfderiv_eq
  have hcov := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := (covectorCovariantDerivative cov).isCovariantDerivativeOnUniv)
    hdf hdg Filter.univ_mem hdiff
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov f x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b]
  apply Finset.sum_congr rfl
  intro i _
  unfold scalarHessian
  rw [hcov]

end CovariantDerivative
