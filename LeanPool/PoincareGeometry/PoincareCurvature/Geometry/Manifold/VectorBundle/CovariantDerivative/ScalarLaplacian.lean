/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# The scalar Laplace--Beltrami operator

This file constructs the scalar Hessian and Laplace--Beltrami operator from
the same induced-connection machinery used by the connection Laplacian on
covariant two-tensors.  For a scalar function `f`, its differential is the
section `df` of the cotangent bundle obtained from ordinary manifold
differentiation.  The Hessian is the covariant derivative `∇(df)`, and the
Laplacian is its metric trace.

The construction is intrinsic: the contraction uses the basis-independent
canonical covariant metric tensor.  The orthonormal-basis formula below is a
proved evaluation theorem rather than the definition of the operator.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
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

/-- The intrinsic differential of a scalar function, viewed as a cotangent
section. -/
def scalarDifferential (f : M → ℝ) (x : M) : T₁ x :=
  realLineCovariantDerivative (I := I) (M := M) f x

@[simp]
theorem scalarDifferential_apply (f : M → ℝ) (x : M) (u : TM x) :
    scalarDifferential (I := I) f x u = mvfderiv (I := I) f x u :=
  rfl

/-- The scalar Hessian `∇(df)`.  Its two arguments are respectively the
covariant-derivative direction and the cotangent slot. -/
def scalarHessian (cov : CovariantDerivative I E TM)
    (f : M → ℝ) (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  covectorCovariantDerivative cov (scalarDifferential (I := I) f) x

/-- Expanded intrinsic formula for the scalar Hessian at a point where `df`
is differentiable as a cotangent section. -/
theorem scalarHessian_apply_of_mdifferentiableAt
    (cov : CovariantDerivative I E TM) (f : M → ℝ) {x : M}
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (u v : TM x) :
    scalarHessian cov f x u v =
      mvfderiv (I := I) (fun y =>
        scalarDifferential (I := I) f y
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) x u
      - scalarDifferential (I := I) f x
          (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x u) := by
  simp only [scalarHessian, covectorCovariantDerivative,
    inducedHomCovariantDerivative, dif_pos hdf, inducedHomAtOfMDiff_apply,
    realLineCovariantDerivative, trivialCovariantDerivative_apply]

/-- At a critical point the connection correction in the scalar Hessian
vanishes. -/
theorem scalarHessian_apply_of_mdifferentiableAt_of_differential_eq_zero
    (cov : CovariantDerivative I E TM) (f : M → ℝ) {x : M}
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hcritical : scalarDifferential (I := I) f x = 0)
    (u v : TM x) :
    scalarHessian cov f x u v =
      mvfderiv (I := I) (fun y =>
        scalarDifferential (I := I) f y
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) x u := by
  rw [scalarHessian_apply_of_mdifferentiableAt cov f hdf u v, hcritical]
  simp

/-- The scalar Laplace--Beltrami operator `tr_g(∇²f)`, with the heat
equation sign convention `+∑ᵢ ∂ᵢ²`. -/
def scalarLaplacian (cov : CovariantDerivative I E TM)
    (f : M → ℝ) (x : M) : ℝ :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B := scalarHessian cov f x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (B u).toLinearMap
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro c u
        ext w
        simp }
  TensorProduct.lift L (InnerProductSpace.canonicalCovariantTensor (TM x))

/-- Evaluation of the scalar Laplacian using any orthonormal basis. -/
theorem scalarLaplacian_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    scalarLaplacian cov f x =
      ∑ i, scalarHessian cov f x (b i) (b i) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [scalarLaplacian,
    InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) b, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

@[simp]
theorem scalarLaplacian_apply
    (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M) :
    scalarLaplacian cov f x =
      letI : FiniteDimensional ℝ (TM x) :=
        VectorBundle.finiteDimensional ℝ E TM x
      let b := stdOrthonormalBasis ℝ (TM x)
      ∑ i : Fin (Module.finrank ℝ (TM x)),
        scalarHessian cov f x (b i) (b i) := by
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov f x
    (stdOrthonormalBasis ℝ (TM x))]

/-- A spatially constant scalar has zero Laplace--Beltrami operator. -/
@[simp] theorem scalarLaplacian_const
    (cov : CovariantDerivative I E TM) (c : ℝ) (x : M) :
    scalarLaplacian cov (fun _ : M => c) x = 0 := by
  have hzero (y : M) :
      scalarDifferential (I := I) (fun _ : M => c) y = 0 := by
    ext u
    simp only [scalarDifferential_apply]
    rw [mvfderiv_const]
  have hdf : MDiffAt
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
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (fun _ : M => c) x
    (stdOrthonormalBasis ℝ (TM x))]
  apply Finset.sum_eq_zero
  intro i hi
  rw [scalarHessian_apply_of_mdifferentiableAt_of_differential_eq_zero
    cov (fun _ : M => c) hdf (hzero x)]
  simp [hzero]
  rw [mvfderiv_const]
  simp

/-- The scalar differential is additive on differentiable functions. -/
theorem scalarDifferential_add {f k : M → ℝ}
    (hf : ∀ y, MDiffAt f y) (hk : ∀ y, MDiffAt k y) :
    scalarDifferential (I := I) (f + k) =
      scalarDifferential (I := I) f + scalarDifferential (I := I) k := by
  funext y
  ext u
  simp only [scalarDifferential_apply, Pi.add_apply, add_apply]
  rw [mvfderiv_add (I := I) (hf y) (hk y)]
  rfl

/-- The scalar differential commutes with multiplication by a constant. -/
theorem scalarDifferential_smul_const (c : ℝ) {f : M → ℝ}
    (hf : ∀ y, MDiffAt f y) :
    scalarDifferential (I := I) (c • f) =
      c • scalarDifferential (I := I) f := by
  funext y
  ext u
  simp only [scalarDifferential_apply, Pi.smul_apply, smul_apply]
  change mvfderiv (I := I) ((fun _ : M => c) * f) y u =
    c * mvfderiv (I := I) f y u
  have hc : MDiffAt (fun _ : M => c) y := mdifferentiableAt_const
  rw [mvfderiv_mul (I := I) hc (hf y)]
  rw [mvfderiv_const]
  simp

/-- The scalar Hessian is additive under the regularity needed by its
covariant-derivative definition. -/
theorem scalarHessian_add
    (cov : CovariantDerivative I E TM) {f k : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hk : ∀ y, MDiffAt k y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdk : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) k y)) x) :
    scalarHessian cov (f + k) x =
      scalarHessian cov f x + scalarHessian cov k x := by
  unfold scalarHessian
  rw [scalarDifferential_add hf hk]
  exact (covectorCovariantDerivative cov).isCovariantDerivativeOn.add hdf hdk

/-- The scalar Hessian is homogeneous under multiplication by a constant. -/
theorem scalarHessian_smul_const
    (cov : CovariantDerivative I E TM) (c : ℝ) {f : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x) :
    scalarHessian cov (c • f) x = c • scalarHessian cov f x := by
  unfold scalarHessian
  rw [scalarDifferential_smul_const c hf]
  exact (covectorCovariantDerivative cov).isCovariantDerivativeOn.smul_const c hdf

/-- Additivity of the scalar Laplacian. -/
theorem scalarLaplacian_add
    (cov : CovariantDerivative I E TM) {f k : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hk : ∀ y, MDiffAt k y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdk : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) k y)) x) :
    scalarLaplacian cov (f + k) x =
      scalarLaplacian cov f x + scalarLaplacian cov k x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (f + k) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov k x b]
  simp_rw [scalarHessian_add cov hf hk hdf hdk, add_apply]
  exact Finset.sum_add_distrib

/-- Homogeneity of the scalar Laplacian under multiplication by a constant. -/
theorem scalarLaplacian_smul_const
    (cov : CovariantDerivative I E TM) (c : ℝ) {f : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x) :
    scalarLaplacian cov (c • f) x = c * scalarLaplacian cov f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (c • f) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_smul_const cov c hf hdf, smul_apply]
  exact (Finset.mul_sum _ _ _).symm

/-- Combined affine linearity form used for geometric support functions. -/
theorem scalarLaplacian_add_smul_const
    (cov : CovariantDerivative I E TM) (c : ℝ) {f k : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hk : ∀ y, MDiffAt k y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdk : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) k y)) x) :
    scalarLaplacian cov (f + c • k) x =
      scalarLaplacian cov f x + c * scalarLaplacian cov k x := by
  have hck : ∀ y, MDiffAt (c • k) y := by
    intro y
    exact (mdifferentiableAt_const : MDiffAt (fun _ : M => c) y).smul (hk y)
  have hdck : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (c • k) y)) x := by
    rw [scalarDifferential_smul_const c hk]
    exact (mdifferentiableAt_const : MDiffAt (fun _ : M => c) x).smul_section hdk
  rw [scalarLaplacian_add cov hf hck hdf hdck]
  rw [scalarLaplacian_smul_const cov c hk hdk]

end CovariantDerivative
