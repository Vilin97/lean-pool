/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HomEvaluation

/-!
# Covariant differentiation of evaluated bilinear forms

This file proves the intrinsic Leibniz rule for a covariant two-tensor
evaluated on a moving tangent field.  It is the first-order input for the
contact-Hessian calculation in the Hamilton--Ivey tensor maximum principle.
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

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

local instance bilinearEvalTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance bilinearEvalTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance bilinearEvalTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance bilinearEvalTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance

/-- Intrinsic Leibniz rule for evaluating a covariant three-tensor on three
independently moving tangent fields. -/
theorem realLineCovariantDerivative_trilinear
    (cov : CovariantDerivative I E TM)
    {A : ∀ x : M, T₃ x} {X U V : ∀ x : M, TM x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y (A y)) x)
    (hX : MDiffAt (T% X) x) (hU : MDiffAt (T% U) x)
    (hV : MDiffAt (T% V) x) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => A y (X y) (U y) (V y)) x u =
      covariantThreeTensorCovariantDerivative cov A x u
          (X x) (U x) (V x) +
        A x (cov X x u) (U x) (V x) +
        A x (X x) (cov U x u) (V x) +
        A x (X x) (U x) (cov V x u) := by
  let φ : ∀ y : M, T₂ y := fun y => A y (X y)
  let ψ : ∀ y : M, T₁ y := fun y => φ y (U y)
  have hφ : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (φ y)) x :=
    hA.clm_bundle_apply hX
  have hψ : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (ψ y)) x :=
    hφ.clm_bundle_apply hU
  have houter :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] (E →L[ℝ] ℝ)) _ _ _ _ _ _
      TM T₂ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covariantTwoTensorCovariantDerivative cov) A X x hA hX u
  have houterUV := congrArg (fun q : T₂ x => q (U x) (V x)) houter
  have hmiddle :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covectorCovariantDerivative cov) φ U x hφ hU u
  have hmiddleV := congrArg (fun q : T₁ x => q (V x)) hmiddle
  have hinner :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (realLineCovariantDerivative (I := I) (M := M)) ψ V x hψ hV u
  change covariantThreeTensorCovariantDerivative cov A x u
      (X x) (U x) (V x) = _ at houterUV
  change covariantTwoTensorCovariantDerivative cov φ x u
      (U x) (V x) = _ at hmiddleV
  change covectorCovariantDerivative cov ψ x u (V x) = _ at hinner
  change realLineCovariantDerivative (I := I) (M := M)
      (fun y => A y (X y) (U y) (V y)) x u = _
  dsimp [φ, ψ] at houterUV hmiddleV hinner
  simp only [sub_apply] at houterUV hmiddleV
  rw [hinner] at hmiddleV
  rw [hmiddleV] at houterUV
  linarith

/-- When all three moving fields are covariantly stationary at the evaluation
point, differentiating their trilinear contraction differentiates only the
tensor. -/
theorem realLineCovariantDerivative_trilinear_of_covariantDerivative_eq_zero
    (cov : CovariantDerivative I E TM)
    {A : ∀ x : M, T₃ x} {X U V : ∀ x : M, TM x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y (A y)) x)
    (hX : MDiffAt (T% X) x) (hU : MDiffAt (T% U) x)
    (hV : MDiffAt (T% V) x)
    (hXzero : cov X x = 0) (hUzero : cov U x = 0)
    (hVzero : cov V x = 0) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => A y (X y) (U y) (V y)) x u =
      covariantThreeTensorCovariantDerivative cov A x u
        (X x) (U x) (V x) := by
  rw [realLineCovariantDerivative_trilinear cov hA hX hU hV u,
    hXzero, hUzero, hVzero]
  simp

/-- Intrinsic Leibniz rule for evaluating a covariant two-tensor on two
independently moving tangent fields. -/
theorem realLineCovariantDerivative_bilinear
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} {U V : ∀ x : M, TM x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => h y (U y) (V y)) x u =
      covariantTwoTensorCovariantDerivative cov h x u (U x) (V x) +
        h x (cov U x u) (V x) + h x (U x) (cov V x u) := by
  let φ : ∀ y : M, T₁ y := fun y => h y (U y)
  have hφ : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (φ y)) x :=
    hh.clm_bundle_apply hU
  have houter :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covectorCovariantDerivative cov) h U x hh hU u
  have houterV := congrArg (fun q : T₁ x => q (V x)) houter
  have hinner :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (realLineCovariantDerivative (I := I) (M := M)) φ V x hφ hV u
  change covariantTwoTensorCovariantDerivative cov h x u (U x) (V x) = _ at houterV
  change covectorCovariantDerivative cov φ x u (V x) = _ at hinner
  change realLineCovariantDerivative (I := I) (M := M)
      (fun y => h y (U y) (V y)) x u = _
  dsimp [φ] at houterV hinner
  simp only [sub_apply] at houterV
  rw [hinner] at houterV
  linarith

/-- Intrinsic Leibniz rule when the same moving tangent field is used in both
slots. -/
theorem realLineCovariantDerivative_bilinear_self
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} {V : ∀ x : M, TM x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hV : MDiffAt (T% V) x) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => h y (V y) (V y)) x u =
      covariantTwoTensorCovariantDerivative cov h x u (V x) (V x) +
        h x (cov V x u) (V x) + h x (V x) (cov V x u) := by
  exact realLineCovariantDerivative_bilinear cov hh hV hV u

/-- If the moving field is covariantly stationary at the evaluation point,
only the covariant derivative of the tensor contributes. -/
theorem realLineCovariantDerivative_bilinear_self_of_covariantDerivative_eq_zero
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} {V : ∀ x : M, TM x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hV : MDiffAt (T% V) x) (hparallel : cov V x = 0) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => h y (V y) (V y)) x u =
      covariantTwoTensorCovariantDerivative cov h x u (V x) (V x) := by
  rw [realLineCovariantDerivative_bilinear_self cov hh hV u, hparallel]
  simp

/-- At a first-order parallel contact field, the scalar Hessian of an
evaluated two-tensor equals the covariant Hessian of the tensor, provided the
two-tensor annihilates the contact vector in both slots.  The kernel
hypotheses are exactly what removes the second jet of the chosen extension. -/
theorem scalarHessian_bilinear_self_eq_covariantHessian_of_contactKernel
    (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (V : ∀ x : M, TM x) (x : M)
    (hh : ∀ y, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z (h z)) y)
    (hV : ∀ y, MDiffAt (T% V) y)
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (fun z => h z (V z) (V z)) y)) x)
    (hsecondV : ∀ z : TM x, MDiffAt
      (T% (fun y => cov V y
        (smoothExtend (I := I) (F := E) (V := TM) x z y))) x)
    (hparallel : cov V x = 0)
    (hkernelLeft : ∀ w : TM x, h x w (V x) = 0)
    (hkernelRight : ∀ w : TM x, h x (V x) w = 0)
    (u z : TM x) :
    scalarHessian cov (fun y => h y (V y) (V y)) x u z =
      covariantHessianTwoTensor cov h x u z (V x) (V x) := by
  let f : M → ℝ := fun y => h y (V y) (V y)
  let A : ∀ y : M, T₃ y :=
    covariantTwoTensorCovariantDerivative cov h
  let W : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x z
  let D : ∀ y : M, TM y := fun y => cov V y (W y)
  let q₁ : M → ℝ := fun y => A y (W y) (V y) (V y)
  let q₂ : M → ℝ := fun y => h y (D y) (V y)
  let q₃ : M → ℝ := fun y => h y (V y) (D y)
  have hW : ∀ y, MDiffAt (T% W) y := by
    intro y
    exact ((smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x z).of_le (by simp) y).mdifferentiableAt one_ne_zero
  have hDx : MDiffAt (T% D) x := by
    simpa [D, W] using hsecondV z
  have hDzero : D x = 0 := by
    simp [D, W, hparallel]
  have heval : (fun y => scalarDifferential (I := I) f y (W y)) =
      q₁ + q₂ + q₃ := by
    funext y
    have hy := realLineCovariantDerivative_bilinear_self
      cov (hh y) (hV y) (W y)
    change scalarDifferential (I := I) f y (W y) = _ at hy
    simpa [f, A, D, q₁, q₂, q₃] using hy
  have htermOne : MDiffAt q₁ x := by
    have hAW := hfirst.clm_bundle_apply (hW x)
    have hAWV := hAW.clm_bundle_apply (hV x)
    have htotal := hAWV.clm_bundle_apply (hV x)
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I q₁ (FiberBundle.mem_baseSet_trivializationAt' x)).mp htotal
    simpa [Bundle.Trivial.eq_trivialization M ℝ, q₁, A] using ht
  have htermTwo : MDiffAt q₂ x := by
    have hhD := (hh x).clm_bundle_apply hDx
    have htotal := hhD.clm_bundle_apply (hV x)
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I q₂ (FiberBundle.mem_baseSet_trivializationAt' x)).mp htotal
    simpa [Bundle.Trivial.eq_trivialization M ℝ, q₂] using ht
  have htermThree : MDiffAt q₃ x := by
    have hhV := (hh x).clm_bundle_apply (hV x)
    have htotal := hhV.clm_bundle_apply hDx
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I q₃ (FiberBundle.mem_baseSet_trivializationAt' x)).mp htotal
    simpa [Bundle.Trivial.eq_trivialization M ℝ, q₃] using ht
  have hOne := realLineCovariantDerivative_trilinear
    cov hfirst (hW x) (hV x) (hV x) u
  have hTwo := realLineCovariantDerivative_bilinear
    cov (hh x) hDx (hV x) u
  have hThree := realLineCovariantDerivative_bilinear
    cov (hh x) (hV x) hDx u
  have hCorrection :=
    realLineCovariantDerivative_bilinear_self_of_covariantDerivative_eq_zero
      cov (hh x) (hV x) hparallel (cov W x u)
  have hCorrection' : scalarDifferential (I := I) f x (cov W x u) =
      A x (cov W x u) (V x) (V x) := by
    simpa [f, A, scalarDifferential, realLineCovariantDerivative] using hCorrection
  have hCorrection'' : mvfderiv (I := I) f x (cov W x u) =
      A x (cov W x u) (V x) (V x) := by
    simpa only [scalarDifferential_apply] using hCorrection'
  rw [scalarHessian_apply_of_mdifferentiableAt cov f hdf u z]
  change mvfderiv (I := I)
      (fun y => scalarDifferential (I := I) f y (W y)) x u -
      scalarDifferential (I := I) f x (cov W x u) = _
  rw [heval]
  rw [mvfderiv_add (I := I) (htermOne.add htermTwo) htermThree,
    mvfderiv_add (I := I) htermOne htermTwo]
  change realLineCovariantDerivative (I := I) (M := M)
      q₁ x u +
      realLineCovariantDerivative (I := I) (M := M)
        q₂ x u +
      realLineCovariantDerivative (I := I) (M := M)
        q₃ x u -
      scalarDifferential (I := I) f x (cov W x u) = _
  dsimp [q₁, q₂, q₃]
  rw [hOne, hTwo, hThree, hCorrection'']
  rw [hDzero, hparallel]
  simp only [zero_apply, map_zero, zero_add]
  rw [hkernelLeft, hkernelRight]
  simp [A, W, covariantHessianTwoTensor, smoothExtend_apply]

/-- Metric trace of the contact-Hessian identity: the scalar Laplacian of the
evaluated quadratic form is the connection Laplacian of the underlying
two-tensor evaluated on the contact vector. -/
theorem scalarLaplacian_bilinear_self_eq_connectionLaplacian_of_contactKernel
    (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (V : ∀ x : M, TM x) (x : M)
    (hh : ∀ y, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z (h z)) y)
    (hV : ∀ y, MDiffAt (T% V) y)
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (fun z => h z (V z) (V z)) y)) x)
    (hsecondV : ∀ z : TM x, MDiffAt
      (T% (fun y => cov V y
        (smoothExtend (I := I) (F := E) (V := TM) x z y))) x)
    (hparallel : cov V x = 0)
    (hkernelLeft : ∀ w : TM x, h x w (V x) = 0)
    (hkernelRight : ∀ w : TM x, h x (V x) w = 0) :
    scalarLaplacian cov (fun y => h y (V y) (V y)) x =
      connectionLaplacian cov h x (V x) (V x) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov
      (fun y => h y (V y) (V y)) x b,
    connectionLaplacian_eq_sum_orthonormalBasis cov h x b]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact scalarHessian_bilinear_self_eq_covariantHessian_of_contactKernel
    cov h V x hh hV hfirst hdf hsecondV hparallel
      hkernelLeft hkernelRight (b i) (b i)

end CovariantDerivative
