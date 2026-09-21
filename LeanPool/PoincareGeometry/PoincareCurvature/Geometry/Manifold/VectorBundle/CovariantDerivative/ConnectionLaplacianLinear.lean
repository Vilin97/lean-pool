/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# Linearity of the connection Laplacian on its genuine second-order domain

The raw `CovariantDerivative` API is linear only at points where the section
being differentiated is differentiable. Consequently the connection
Laplacian is not definitionally a linear map on all set-theoretic sections.
This file records the precise geometric domain on which it is linear: a
covariant two-tensor and its first covariant derivative must both be
manifold-differentiable.

This is the operator-theoretic bridge needed before constructing the tensor
heat semigroup. No linearity or differential identity is hidden in a
hypothesis: the pointwise additivity and homogeneity below are derived twice
from the covariant-derivative laws and then passed through the intrinsic metric
trace defining `connectionLaplacian`.
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
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

-- Keep the nested operator-space instances explicit.  Without these names,
-- deterministic typeclass search can loop while elaborating the induced
-- tensor bundles in a clean `lake build`.
local instance linearCovOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance linearCovOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance linearCovTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance linearCovTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance linearCovThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance linearCovThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance linearCovOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := inferInstance
local instance linearCovOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := inferInstance
local instance linearCovTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance linearCovTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance linearCovThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance linearCovThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance
local instance linearCovThreeFiberAddCommGroup (x : M) :
    AddCommGroup (T₃ x) := ContinuousLinearMap.addCommGroup
local instance linearCovThreeFiberModule (x : M) :
    Module ℝ (T₃ x) := ContinuousLinearMap.module

/-- The induced connection on covariant two-tensors is pointwise additive on
differentiable sections. -/
theorem covariantTwoTensorCovariantDerivative_add
    (cov : CovariantDerivative I E TM) {h k : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hk : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (k y)) x) :
    covariantTwoTensorCovariantDerivative cov (h + k) x =
      covariantTwoTensorCovariantDerivative cov h x +
        covariantTwoTensorCovariantDerivative cov k x := by
  exact (covariantTwoTensorCovariantDerivative cov).isCovariantDerivativeOn.add hh hk

/-- The induced connection on covariant two-tensors is pointwise homogeneous
under a constant scalar on differentiable sections. -/
theorem covariantTwoTensorCovariantDerivative_smul_const
    (cov : CovariantDerivative I E TM) (c : ℝ) {h : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x) :
    covariantTwoTensorCovariantDerivative cov (c • h) x =
      c • covariantTwoTensorCovariantDerivative cov h x := by
  simpa using
    (covariantTwoTensorCovariantDerivative cov).isCovariantDerivativeOn.smul_const c hh

/-- The genuine covariant Hessian is additive once both first covariant
derivatives are differentiable at the point. -/
theorem covariantHessianTwoTensor_add
    (cov : CovariantDerivative I E TM) {h k : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hk : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov k y)) x)
    (hfirstAdd : covariantTwoTensorCovariantDerivative cov (h + k) =
      covariantTwoTensorCovariantDerivative cov h +
        covariantTwoTensorCovariantDerivative cov k) :
    covariantHessianTwoTensor cov (h + k) x =
      covariantHessianTwoTensor cov h x + covariantHessianTwoTensor cov k x := by
  unfold covariantHessianTwoTensor
  rw [hfirstAdd]
  exact (covariantThreeTensorCovariantDerivative cov).isCovariantDerivativeOn.add hh hk

/-- The genuine covariant Hessian is homogeneous under constant scalars once
the first covariant derivative is differentiable. -/
theorem covariantHessianTwoTensor_smul_const
    (cov : CovariantDerivative I E TM) (c : ℝ) {h : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hfirstSmul : covariantTwoTensorCovariantDerivative cov (c • h) =
      c • covariantTwoTensorCovariantDerivative cov h) :
    covariantHessianTwoTensor cov (c • h) x =
      c • covariantHessianTwoTensor cov h x := by
  unfold covariantHessianTwoTensor
  rw [hfirstSmul]
  simpa using
    (covariantThreeTensorCovariantDerivative cov).isCovariantDerivativeOn.smul_const c hh

/-- Intrinsic connection-Laplacian additivity, obtained by tracing the
additive covariant Hessian. -/
theorem connectionLaplacian_add
    (cov : CovariantDerivative I E TM) {h k : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hk : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov k y)) x)
    (hfirstAdd : covariantTwoTensorCovariantDerivative cov (h + k) =
      covariantTwoTensorCovariantDerivative cov h +
        covariantTwoTensorCovariantDerivative cov k) :
    connectionLaplacian cov (h + k) x =
      connectionLaplacian cov h x + connectionLaplacian cov k x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [connectionLaplacian_eq_sum_orthonormalBasis cov (h + k) x b,
    connectionLaplacian_eq_sum_orthonormalBasis cov h x b,
    connectionLaplacian_eq_sum_orthonormalBasis cov k x b]
  simp_rw [covariantHessianTwoTensor_add cov hh hk hfirstAdd, add_apply]
  exact Finset.sum_add_distrib

/-- Intrinsic connection-Laplacian homogeneity, obtained by tracing the
homogeneous covariant Hessian. -/
theorem connectionLaplacian_smul_const
    (cov : CovariantDerivative I E TM) (c : ℝ) {h : ∀ x : M, T₂ x} {x : M}
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hfirstSmul : covariantTwoTensorCovariantDerivative cov (c • h) =
      c • covariantTwoTensorCovariantDerivative cov h) :
    connectionLaplacian cov (c • h) x = c • connectionLaplacian cov h x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [connectionLaplacian_eq_sum_orthonormalBasis cov (c • h) x b,
    connectionLaplacian_eq_sum_orthonormalBasis cov h x b]
  simp_rw [covariantHessianTwoTensor_smul_const cov c hh hfirstSmul, smul_apply]
  exact Finset.smul_sum.symm

/-- The genuine second-order domain of the connection Laplacian: the tensor
section and its first covariant derivative are differentiable everywhere. -/
def ConnectionLaplacianDomain (cov : CovariantDerivative I E TM) :
    Submodule ℝ (∀ x : M, T₂ x) where
  carrier := {h | (∀ x, MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x) ∧
    (∀ x, MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)}
  zero_mem' := by
    constructor
    · intro x
      exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
        (F := E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) (x := x)
    · intro x
      have hz : covariantTwoTensorCovariantDerivative cov
          (0 : ∀ x : M, T₂ x) = 0 :=
        CovariantDerivative.zero (covariantTwoTensorCovariantDerivative cov)
      rw [hz]
      exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
        (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) (x := x)
  add_mem' := by
    intro h k hh hk
    constructor
    · intro x
      exact mdifferentiableAt_add_section (hh.1 x) (hk.1 x)
    · intro x
      have heq : covariantTwoTensorCovariantDerivative cov (h + k) =
          covariantTwoTensorCovariantDerivative cov h +
            covariantTwoTensorCovariantDerivative cov k := by
        funext y
        exact covariantTwoTensorCovariantDerivative_add cov (hh.1 y) (hk.1 y)
      rw [heq]
      exact mdifferentiableAt_add_section (hh.2 x) (hk.2 x)
  smul_mem' := by
    intro c h hh
    constructor
    · intro x
      have hc : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
      exact hc.smul_section (hh.1 x)
    · intro x
      have heq : covariantTwoTensorCovariantDerivative cov (c • h) =
          c • covariantTwoTensorCovariantDerivative cov h := by
        funext y
        exact covariantTwoTensorCovariantDerivative_smul_const cov c (hh.1 y)
      rw [heq]
      have hc : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
      exact hc.smul_section (hh.2 x)

/-- The intrinsic connection Laplacian at a point, bundled as a linear map on
its genuine second-order domain. -/
def connectionLaplacianLinearMapAt (cov : CovariantDerivative I E TM) (x : M) :
    ConnectionLaplacianDomain cov →ₗ[ℝ] T₂ x where
  toFun h := connectionLaplacian cov h.1 x
  map_add' := by
    intro h k
    apply connectionLaplacian_add cov (h.2.2 x) (k.2.2 x)
    funext y
    exact covariantTwoTensorCovariantDerivative_add cov (h.2.1 y) (k.2.1 y)
  map_smul' := by
    intro c h
    apply connectionLaplacian_smul_const cov c (h.2.2 x)
    funext y
    exact covariantTwoTensorCovariantDerivative_smul_const cov c (h.2.1 y)

@[simp]
theorem connectionLaplacianLinearMapAt_apply
    (cov : CovariantDerivative I E TM) (x : M) (h : ConnectionLaplacianDomain cov) :
    connectionLaplacianLinearMapAt cov x h = connectionLaplacian cov h.1 x :=
  rfl

/-- The intrinsic connection Laplacian as a linear map from its genuine
second-order domain to (not necessarily regular) tensor sections. -/
def connectionLaplacianLinearMap (cov : CovariantDerivative I E TM) :
    ConnectionLaplacianDomain cov →ₗ[ℝ] (∀ x : M, T₂ x) where
  toFun h := fun x => connectionLaplacian cov h.1 x
  map_add' := by
    intro h k
    funext x
    change (connectionLaplacianLinearMapAt cov x) (h + k) =
      (connectionLaplacianLinearMapAt cov x) h +
        (connectionLaplacianLinearMapAt cov x) k
    exact (connectionLaplacianLinearMapAt cov x).map_add h k
  map_smul' := by
    intro c h
    funext x
    change (connectionLaplacianLinearMapAt cov x) (c • h) =
      c • (connectionLaplacianLinearMapAt cov x) h
    exact (connectionLaplacianLinearMapAt cov x).map_smul c h

@[simp]
theorem connectionLaplacianLinearMap_apply
    (cov : CovariantDerivative I E TM) (h : ConnectionLaplacianDomain cov) (x : M) :
    connectionLaplacianLinearMap cov h x = connectionLaplacian cov h.1 x :=
  rfl

/-- Pointwise symmetric covariant two-tensor sections, without a regularity
condition. -/
def SymmetricCovariantTwoTensorSections : Submodule ℝ (∀ x : M, T₂ x) where
  carrier := {h | ∀ x u v, h x u v = h x v u}
  zero_mem' := by simp
  add_mem' := by
    intro h k hh hk x u v
    simp only [Pi.add_apply, add_apply]
    rw [hh x u v, hk x u v]
  smul_mem' := by
    intro c h hh x u v
    simp only [Pi.smul_apply, smul_apply]
    rw [hh x u v]

@[simp]
theorem mem_SymmetricCovariantTwoTensorSections_iff {h : ∀ x : M, T₂ x} :
    h ∈ (SymmetricCovariantTwoTensorSections (I := I) (M := M)) ↔
      ∀ x u v, h x u v = h x v u :=
  Iff.rfl

/-- The second-order domain restricted to symmetric covariant two-tensors. -/
def SymmetricConnectionLaplacianDomain (cov : CovariantDerivative I E TM) :
    Submodule ℝ (∀ x : M, T₂ x) :=
  ConnectionLaplacianDomain cov ⊓
    SymmetricCovariantTwoTensorSections (I := I) (M := M)

/-- The intrinsic connection Laplacian as a genuine linear operator from
twice covariantly differentiable symmetric tensors to symmetric tensors. -/
def symmetricConnectionLaplacianLinearMap (cov : CovariantDerivative I E TM) :
    SymmetricConnectionLaplacianDomain cov →ₗ[ℝ]
      SymmetricCovariantTwoTensorSections (I := I) (M := M) where
  toFun h := ⟨fun x => connectionLaplacian cov h.1 x,
    fun x u v => connectionLaplacian_swap cov h.2.2 x u v⟩
  map_add' := by
    intro h k
    apply Subtype.ext
    funext x
    change (connectionLaplacianLinearMapAt cov x)
        (⟨h.1, h.2.1⟩ + ⟨k.1, k.2.1⟩) =
      (connectionLaplacianLinearMapAt cov x) ⟨h.1, h.2.1⟩ +
        (connectionLaplacianLinearMapAt cov x) ⟨k.1, k.2.1⟩
    exact (connectionLaplacianLinearMapAt cov x).map_add
      ⟨h.1, h.2.1⟩ ⟨k.1, k.2.1⟩
  map_smul' := by
    intro c h
    apply Subtype.ext
    funext x
    change (connectionLaplacianLinearMapAt cov x) (c • ⟨h.1, h.2.1⟩) =
      c • (connectionLaplacianLinearMapAt cov x) ⟨h.1, h.2.1⟩
    exact (connectionLaplacianLinearMapAt cov x).map_smul c ⟨h.1, h.2.1⟩

@[simp]
theorem symmetricConnectionLaplacianLinearMap_apply
    (cov : CovariantDerivative I E TM)
    (h : SymmetricConnectionLaplacianDomain cov) (x : M) :
    (symmetricConnectionLaplacianLinearMap cov h).1 x = connectionLaplacian cov h.1 x :=
  rfl

end CovariantDerivative
