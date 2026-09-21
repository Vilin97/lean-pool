/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHom
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# The connection Laplacian on covariant two-tensors

This file defines the geometric operator required by the tensor heat equation.
For a covariant two-tensor `h`, the first covariant derivative is

`(∇_X h)(Y,Z) = X(h(Y,Z)) - h(∇_XY,Z) - h(Y,∇_XZ)`.

The covariant Hessian differentiates this `(0,3)`-tensor in all three tensor
slots.  The connection Laplacian is its trace in the first two slots against
an orthonormal basis of the tangent fibre.  The sign convention therefore
agrees with the positive-coordinate expression `∑_i ∂_i²` used by the
Euclidean heat kernel in `TensorHeatEuclidean`.

The primary operator is constructed by applying the induced hom-bundle
connection three times and tracing the genuine covariant Hessian.  The
expanded along-fields formulas later in the file are retained as useful
evaluation lemmas, not as the definition of the operator.
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

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

/-! ## Intrinsic induced tensor connections -/

/-- The flat connection on the trivial real line bundle. -/
def realLineCovariantDerivative : CovariantDerivative I ℝ T₀ :=
  trivialCovariantDerivative (I := I) (M := M) ℝ

/-- The connection induced by `cov` on the cotangent bundle. -/
def covectorCovariantDerivative (cov : CovariantDerivative I E TM) :
    CovariantDerivative I (E →L[ℝ] ℝ) T₁ :=
  inducedHomCovariantDerivative (I := I) (M := M) (F₁ := E) (F₂ := ℝ)
    (V₁ := TM) (V₂ := T₀) cov realLineCovariantDerivative

/-- The connection induced by `cov` on covariant two-tensors. -/
def covariantTwoTensorCovariantDerivative (cov : CovariantDerivative I E TM) :
    CovariantDerivative I (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  inducedHomCovariantDerivative (I := I) (M := M) (F₁ := E)
    (F₂ := E →L[ℝ] ℝ) (V₁ := TM) (V₂ := T₁)
    cov (covectorCovariantDerivative cov)

/-- Expanded evaluation formula for the induced connection on covariant
two-tensors.  It is the intrinsic identity
`(∇_X h)(u,v) = X(h(u,v)) - h(∇_X u,v) - h(u,∇_X v)`, with the fibre vectors
extended by the canonical smooth extensions. -/
theorem covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
    (cov : CovariantDerivative I E TM) {h : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (X u v : TM x) :
    covariantTwoTensorCovariantDerivative cov h x X u v =
      mvfderiv (I := I) (fun y =>
        h y (smoothExtend (I := I) (F := E) (V := TM) x u y)
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) x X
      - h x (cov (smoothExtend (I := I) (F := E) (V := TM) x u) x X) v
      - h x u (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x X) := by
  have hu : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x u)) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hv : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x v)) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hhu : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (h y (smoothExtend (I := I) (F := E) (V := TM) x u y))) x :=
    hh.clm_bundle_apply hu
  simp only [covariantTwoTensorCovariantDerivative, covectorCovariantDerivative,
    inducedHomCovariantDerivative, dif_pos hh, dif_pos hhu,
    inducedHomAtOfMDiff_apply]
  change
    (mvfderiv (I := I) (fun y =>
        h y (smoothExtend (I := I) (F := E) (V := TM) x u y)
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) x X -
      h x (smoothExtend (I := I) (F := E) (V := TM) x u x)
        (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x X)) -
      h x (cov (smoothExtend (I := I) (F := E) (V := TM) x u) x X) v = _
  rw [smoothExtend_apply]
  ring

/-- The induced tensor connection preserves symmetry in the final two
covariant slots. -/
theorem covariantTwoTensorCovariantDerivative_swap
    (cov : CovariantDerivative I E TM) {h : ∀ x : M, T₂ x}
    (hsymm : ∀ x u v, h x u v = h x v u)
    (x : M) (X u v : TM x) :
    covariantTwoTensorCovariantDerivative cov h x X u v =
      covariantTwoTensorCovariantDerivative cov h x X v u := by
  classical
  by_cases hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x
  · rw [covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
      cov hh X u v,
      covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
        cov hh X v u]
    have hfun :
        (fun y => h y
          (smoothExtend (I := I) (F := E) (V := TM) x u y)
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) =
        (fun y => h y
          (smoothExtend (I := I) (F := E) (V := TM) x v y)
          (smoothExtend (I := I) (F := E) (V := TM) x u y)) := by
      funext y
      exact hsymm y _ _
    rw [hfun, hsymm x
      (cov (smoothExtend (I := I) (F := E) (V := TM) x u) x X) v,
      hsymm x u
        (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x X)]
    ring
  · simp [covariantTwoTensorCovariantDerivative,
      inducedHomCovariantDerivative, hh]

-- Naming the depth-two operator-space instances prevents typeclass search
-- from looping when it constructs the next hom bundle.
local instance covariantTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance covariantTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance covariantTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance covariantTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance

/-- The connection induced by `cov` on covariant three-tensors. -/
def covariantThreeTensorCovariantDerivative (cov : CovariantDerivative I E TM) :
    CovariantDerivative I (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  inducedHomCovariantDerivative (I := I) (M := M) (F₁ := E)
    (F₂ := E →L[ℝ] (E →L[ℝ] ℝ)) (V₁ := TM) (V₂ := T₂)
    cov (covariantTwoTensorCovariantDerivative cov)

/-- The genuine covariant Hessian `∇²h`, obtained by differentiating `h` with
the induced tensor connection and then differentiating the resulting
covariant three-tensor with its induced connection. -/
def covariantHessianTwoTensor (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (x : M) : TM x →L[ℝ] TM x →L[ℝ] T₂ x :=
  covariantThreeTensorCovariantDerivative cov
    (covariantTwoTensorCovariantDerivative cov h) x

/-- Expanded intrinsic formula for the covariant Hessian of a covariant
two-tensor.  The correction term in each of the three covariant slots is
visible explicitly. -/
theorem covariantHessianTwoTensor_apply_of_mdifferentiableAt
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (X₁ X₂ u v : TM x) :
    covariantHessianTwoTensor cov h x X₁ X₂ u v =
      mvfderiv (I := I) (fun y =>
        covariantTwoTensorCovariantDerivative cov h y
          (smoothExtend (I := I) (F := E) (V := TM) x X₂ y)
          (smoothExtend (I := I) (F := E) (V := TM) x u y)
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) x X₁
      - covariantTwoTensorCovariantDerivative cov h x
          (cov (smoothExtend (I := I) (F := E) (V := TM) x X₂) x X₁) u v
      - covariantTwoTensorCovariantDerivative cov h x X₂
          (cov (smoothExtend (I := I) (F := E) (V := TM) x u) x X₁) v
      - covariantTwoTensorCovariantDerivative cov h x X₂ u
          (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x X₁) := by
  have hX₂ : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x X₂)) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x X₂).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hsection : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (covariantTwoTensorCovariantDerivative cov h y
          (smoothExtend (I := I) (F := E) (V := TM) x X₂ y))) x :=
    hfirst.clm_bundle_apply hX₂
  simp only [covariantHessianTwoTensor, covariantThreeTensorCovariantDerivative,
    inducedHomCovariantDerivative, dif_pos hfirst, inducedHomAtOfMDiff_apply]
  rw [sub_apply, sub_apply,
    covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
      cov hsection X₁ u v, smoothExtend_apply]
  ring

/-- The covariant Hessian of a symmetric covariant two-tensor remains
symmetric in the two tensor slots that are not traced. -/
theorem covariantHessianTwoTensor_swap
    (cov : CovariantDerivative I E TM) {h : ∀ x : M, T₂ x}
    (hsymm : ∀ x u v, h x u v = h x v u)
    (x : M) (X₁ X₂ u v : TM x) :
    covariantHessianTwoTensor cov h x X₁ X₂ u v =
      covariantHessianTwoTensor cov h x X₁ X₂ v u := by
  classical
  by_cases hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x
  · rw [covariantHessianTwoTensor_apply_of_mdifferentiableAt
      cov h hfirst X₁ X₂ u v,
      covariantHessianTwoTensor_apply_of_mdifferentiableAt
        cov h hfirst X₁ X₂ v u]
    have hfun :
        (fun y => covariantTwoTensorCovariantDerivative cov h y
          (smoothExtend (I := I) (F := E) (V := TM) x X₂ y)
          (smoothExtend (I := I) (F := E) (V := TM) x u y)
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) =
        (fun y => covariantTwoTensorCovariantDerivative cov h y
          (smoothExtend (I := I) (F := E) (V := TM) x X₂ y)
          (smoothExtend (I := I) (F := E) (V := TM) x v y)
          (smoothExtend (I := I) (F := E) (V := TM) x u y)) := by
      funext y
      exact covariantTwoTensorCovariantDerivative_swap cov hsymm y _ _ _
    rw [hfun,
      covariantTwoTensorCovariantDerivative_swap cov hsymm x
        (cov (smoothExtend (I := I) (F := E) (V := TM) x X₂) x X₁) u v,
      covariantTwoTensorCovariantDerivative_swap cov hsymm x X₂
        (cov (smoothExtend (I := I) (F := E) (V := TM) x u) x X₁) v,
      covariantTwoTensorCovariantDerivative_swap cov hsymm x X₂ u
        (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x X₁)]
    ring
  · simp [covariantHessianTwoTensor, covariantThreeTensorCovariantDerivative,
      inducedHomCovariantDerivative, hfirst]

/-- The intrinsic connection Laplacian `tr_g(∇²h)`, with the `+∑ᵢ ∇²_{eᵢ,eᵢ}`
sign convention.  The contraction is defined from the basis-independent
canonical metric tensor. -/
def connectionLaplacian (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (x : M) : T₂ x :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B := covariantHessianTwoTensor cov h x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] T₂ x :=
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

/-- Evaluation of the intrinsic metric contraction using any orthonormal
basis.  This is the explicit basis-independence theorem for the definition. -/
theorem connectionLaplacian_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    connectionLaplacian cov h x =
      ∑ i, covariantHessianTwoTensor cov h x (b i) (b i) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [connectionLaplacian, InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) b,
    map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

@[simp]
theorem connectionLaplacian_apply (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (x : M) (u v : TM x) :
    connectionLaplacian cov h x u v =
      letI : FiniteDimensional ℝ (TM x) :=
        VectorBundle.finiteDimensional ℝ E TM x
      let b := stdOrthonormalBasis ℝ (TM x)
      ∑ i : Fin (Module.finrank ℝ (TM x)),
        covariantHessianTwoTensor cov h x (b i) (b i) u v := by
  rw [connectionLaplacian_eq_sum_orthonormalBasis cov h x
    (stdOrthonormalBasis ℝ (TM x))]
  simp

/-- The intrinsic connection Laplacian preserves symmetric covariant
two-tensors. -/
theorem connectionLaplacian_swap (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} (hsymm : ∀ x u v, h x u v = h x v u)
    (x : M) (u v : TM x) :
    connectionLaplacian cov h x u v = connectionLaplacian cov h x v u := by
  rw [connectionLaplacian_apply, connectionLaplacian_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact covariantHessianTwoTensor_swap cov hsymm x _ _ u v

/-- The covariant derivative of a covariant two-tensor, evaluated on global
vector fields.  The argument order is direction, first tensor slot, second
tensor slot. -/
def covariantDerivativeBilinearAlong (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (X Y Z : ∀ x : M, TM x) (x : M) : ℝ :=
  mvfderiv (I := I) (fun p => h p (Y p) (Z p)) x (X x)
    - h x (cov Y x (X x)) (Z x)
    - h x (Y x) (cov Z x (X x))

/-- The covariant Hessian of a covariant two-tensor, evaluated on four global
vector fields.  This is `∇(∇h)` with the connection correction in every
covariant slot of `∇h`. -/
def secondCovariantDerivativeBilinearAlong (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (X₁ X₂ Y Z : ∀ x : M, TM x) (x : M) : ℝ :=
  mvfderiv (I := I)
      (fun p => covariantDerivativeBilinearAlong cov h X₂ Y Z p) x (X₁ x)
    - covariantDerivativeBilinearAlong cov h (cov.along X₁ X₂) Y Z x
    - covariantDerivativeBilinearAlong cov h X₂ (cov.along X₁ Y) Z x
    - covariantDerivativeBilinearAlong cov h X₂ Y (cov.along X₁ Z) x

/-- The connection Laplacian (rough Laplacian with `+∑∂²` sign) of a
covariant two-tensor, evaluated on two tangent vectors at a point.  All fibre
vectors are extended by the canonical smooth extensions used in the curvature
development, and the covariant Hessian is traced over an orthonormal basis. -/
def connectionLaplacianBilinearApply (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (x : M) (u v : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  let U := smoothExtend (I := I) (F := E) (V := TM) x u
  let V := smoothExtend (I := I) (F := E) (V := TM) x v
  ∑ i : Fin (Module.finrank ℝ (TM x)),
    let e := smoothExtend (I := I) (F := E) (V := TM) x (b i)
    secondCovariantDerivativeBilinearAlong cov h e e U V x

/-- Covariant differentiation preserves symmetry in the two tensor slots. -/
theorem covariantDerivativeBilinearAlong_swap (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} (hsymm : ∀ x u v, h x u v = h x v u)
    (X Y Z : ∀ x : M, TM x) (x : M) :
    covariantDerivativeBilinearAlong cov h X Y Z x =
    covariantDerivativeBilinearAlong cov h X Z Y x := by
  have hfun : (fun p => h p (Y p) (Z p)) = (fun p => h p (Z p) (Y p)) := by
    funext p
    exact hsymm p (Y p) (Z p)
  have hleft := hsymm x (cov Y x (X x)) (Z x)
  have hright := hsymm x (Y x) (cov Z x (X x))
  unfold covariantDerivativeBilinearAlong
  rw [hfun, hleft, hright]
  ring

/-- The covariant Hessian preserves symmetry in the final two tensor slots. -/
theorem secondCovariantDerivativeBilinearAlong_swap (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} (hsymm : ∀ x u v, h x u v = h x v u)
    (X₁ X₂ Y Z : ∀ x : M, TM x) (x : M) :
    secondCovariantDerivativeBilinearAlong cov h X₁ X₂ Y Z x =
      secondCovariantDerivativeBilinearAlong cov h X₁ X₂ Z Y x := by
  have hfun :
      (fun p => covariantDerivativeBilinearAlong cov h X₂ Y Z p) =
        (fun p => covariantDerivativeBilinearAlong cov h X₂ Z Y p) := by
    funext p
    exact covariantDerivativeBilinearAlong_swap cov hsymm X₂ Y Z p
  have h₁ := covariantDerivativeBilinearAlong_swap cov hsymm (cov.along X₁ X₂) Y Z x
  have h₂ := covariantDerivativeBilinearAlong_swap cov hsymm X₂ (cov.along X₁ Y) Z x
  have h₃ := covariantDerivativeBilinearAlong_swap cov hsymm X₂ Y (cov.along X₁ Z) x
  unfold secondCovariantDerivativeBilinearAlong
  rw [hfun, h₁, h₂, h₃]
  ring

/-- The intrinsic connection Laplacian sends symmetric covariant two-tensors
to symmetric bilinear forms. -/
theorem connectionLaplacianBilinearApply_swap (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} (hsymm : ∀ x u v, h x u v = h x v u)
    (x : M) (u v : TM x) :
    connectionLaplacianBilinearApply cov h x u v =
      connectionLaplacianBilinearApply cov h x v u := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  unfold connectionLaplacianBilinearApply
  apply Finset.sum_congr rfl
  intro i _
  exact secondCovariantDerivativeBilinearAlong_swap cov hsymm _ _ _ _ x

end CovariantDerivative
