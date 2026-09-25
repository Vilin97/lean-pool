/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicVariation

/-! # Hamilton Ivey Operator Laplacian -/

@[expose] public section

open Bundle FiberBundle
open scoped Manifold ContDiff

noncomputable section
namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
local notation "T₃" => (fun y : M => TM y →L[ℝ] T₂ y)
local notation "T₄" => (fun y : M => TM y →L[ℝ] T₃ y)

local instance operatorLaplacianTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance operatorLaplacianTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance operatorLaplacianCovectorFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₁ y) := inferInstance
local instance operatorLaplacianCovectorFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₁ y) := inferInstance
local instance operatorLaplacianThreeModelNormedAddCommGroup :
    NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance operatorLaplacianThreeModelNormedSpace :
    NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance operatorLaplacianTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance operatorLaplacianTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance operatorLaplacianThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance operatorLaplacianThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance operatorLaplacianFourModelNormedAddCommGroup :
    NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))) :=
  inferInstance
local instance operatorLaplacianFourModelNormedSpace :
    NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))) :=
  inferInstance
local instance operatorLaplacianFourFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₄ y) := inferInstance
local instance operatorLaplacianFourFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₄ y) := inferInstance

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local instance operatorLaplacianScalarTopologicalSpace :
    TopologicalSpace (TotalSpace ℝ (Bundle.Trivial M ℝ)) :=
  Bundle.Trivial.topologicalSpace M ℝ
local instance operatorLaplacianScalarFiberBundle :
    FiberBundle ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.fiberBundle M ℝ
local instance operatorLaplacianScalarVectorBundle :
    VectorBundle ℝ ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.vectorBundle ℝ M ℝ
local instance operatorLaplacianScalarContMDiffVectorBundle :
    ContMDiffVectorBundle 2 ℝ (Bundle.Trivial M ℝ) I :=
  Bundle.Trivial.contMDiffVectorBundle ℝ

local instance operatorLaplacianCovectorTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance operatorLaplacianCovectorFiberBundle :
    FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance operatorLaplacianCovectorVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance operatorLaplacianCovectorContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance operatorLaplacianTwoTopologicalSpace :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance operatorLaplacianTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance operatorLaplacianTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance operatorLaplacianTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance operatorLaplacianThreeTopologicalSpace :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance operatorLaplacianThreeFiberBundle :
    FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance operatorLaplacianThreeVectorBundle :
    VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance operatorLaplacianThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

theorem mdifferentiableAt_scalarTensorLeibnizTerm
    (f : M → ℝ) (h : ∀ y : M, T₂ y) {x : M}
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (h y)) x) :
    MDifferentiableAt I
      (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y (scalarTensorLeibnizTerm f h y)) x := by
  classical
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E
  refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM) (F₁ := E)
    (s := fun y => scalarTensorLeibnizTerm f h y) x b ?_
  intro i
  let frame : ∀ y : M, TM y := fun y => e.localFrame b i y
  have hx : x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hframe : MDiffAt (T% frame) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : ℕ∞)) (i := i) (hx := hx)).mdifferentiableAt
      one_ne_zero
  have hscalar : MDiffAt
      (fun y => scalarDifferential (I := I) f y (frame y)) x := by
    have h := hdf.clm_bundle_apply hframe
    have ht :=
      ((trivializationAt ℝ T₀ x).mdifferentiableAt_section_iff
        I (fun y => scalarDifferential (I := I) f y (frame y))
        (FiberBundle.mem_baseSet_trivializationAt' x)).mp h
    simpa [Bundle.Trivial.eq_trivialization M ℝ, frame] using ht
  have hproduct : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        ((scalarDifferential (I := I) f y (frame y)) • h y)) x :=
    hscalar.smul_section hh
  simpa [scalarTensorLeibnizTerm, ContinuousLinearMap.smulRight_apply,
    frame] using hproduct

theorem covariantThreeTensorCovariantDerivative_scalarTensor_metric
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (f : M → ℝ) {x : M}
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (u z a b : TM x) :
    covariantThreeTensorCovariantDerivative cov
        (scalarTensorLeibnizTerm f
          (riemannianMetricCovariantTwoTensor (I := I) (M := M))) x
        u z a b =
      scalarHessian cov f x u z *
        riemannianMetricCovariantTwoTensor (I := I) (M := M) x a b := by
  let G : ∀ y : M, T₂ y :=
    riemannianMetricCovariantTwoTensor (I := I) (M := M)
  let W : ∀ y : M, TM y :=
    firstOrderParallelSmoothExtend cov x z
  let U : ∀ y : M, TM y :=
    firstOrderParallelSmoothExtend cov x a
  let V : ∀ y : M, TM y :=
    firstOrderParallelSmoothExtend cov x b
  have hG : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (G y)) x := by
    exact riemannianMetricCovariantTwoTensor_mdifferentiableAt
      (I := I) (E := E) (M := M) x
  have hW : MDiffAt (T% W) x := by
    exact firstOrderParallelSmoothExtend_mdifferentiableAt
      (I := I) (F := E) (V := TM) cov x z
  have hU : MDiffAt (T% U) x := by
    exact firstOrderParallelSmoothExtend_mdifferentiableAt
      (I := I) (F := E) (V := TM) cov x a
  have hV : MDiffAt (T% V) x := by
    exact firstOrderParallelSmoothExtend_mdifferentiableAt
      (I := I) (F := E) (V := TM) cov x b
  have hWzero : cov W x = 0 := by
    exact covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
      (I := I) (F := E) (V := TM) cov x z
  have hUzero : cov U x = 0 := by
    exact covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
      (I := I) (F := E) (V := TM) cov x a
  have hVzero : cov V x = 0 := by
    exact covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
      (I := I) (F := E) (V := TM) cov x b
  have hA : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (scalarTensorLeibnizTerm f G y)) x :=
    mdifferentiableAt_scalarTensorLeibnizTerm f G hdf hG
  have hdfW : MDiffAt
      (fun y => scalarDifferential (I := I) f y (W y)) x := by
    have h := hdf.clm_bundle_apply hW
    have ht :=
      ((trivializationAt ℝ T₀ x).mdifferentiableAt_section_iff
        I (fun y => scalarDifferential (I := I) f y (W y))
        (FiberBundle.mem_baseSet_trivializationAt' x)).mp h
    simpa [Bundle.Trivial.eq_trivialization M ℝ, W] using ht
  have hGU : MDifferentiableAt I
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (G y (U y))) x := by
    have h := hG.clm_bundle_apply hU
    simpa [Bundle.Trivial.eq_trivialization M ℝ, G, U] using h
  have hGUV : MDiffAt
      (fun y => G y (U y) (V y)) x := by
    have h := hGU.clm_bundle_apply hV
    have ht :=
      ((trivializationAt ℝ T₀ x).mdifferentiableAt_section_iff
        I (fun y => G y (U y) (V y))
        (FiberBundle.mem_baseSet_trivializationAt' x)).mp h
    simpa [Bundle.Trivial.eq_trivialization M ℝ, G, U, V] using ht
  have hmetricDerivative :
      realLineCovariantDerivative (I := I) (M := M)
          (fun y => G y (U y) (V y)) x u = 0 := by
    have h := realLineCovariantDerivative_bilinear cov hG hU hV u
    have hzero := covariantTwoTensorCovariantDerivative_riemannianMetric_eq_zero
      (I := I) (E := E) (M := M) cov hmetric x u (U x) (V x)
    rw [hzero, hUzero, hVzero] at h
    simpa [G] using h
  have hproductDerivative :
      realLineCovariantDerivative (I := I) (M := M)
          (fun y => scalarDifferential (I := I) f y (W y) *
            G y (U y) (V y)) x u =
        realLineCovariantDerivative (I := I) (M := M)
            (fun y => scalarDifferential (I := I) f y (W y)) x u *
              G x (U x) (V x) +
          scalarDifferential (I := I) f x (W x) *
            realLineCovariantDerivative (I := I) (M := M)
              (fun y => G y (U y) (V y)) x u := by
    change mvfderiv (I := I)
        (fun y => scalarDifferential (I := I) f y (W y) *
          G y (U y) (V y)) x u = _
    have hfun :
        (fun y => scalarDifferential (I := I) f y (W y) *
          G y (U y) (V y)) =
        (fun y => scalarDifferential (I := I) f y (W y)) *
          (fun y => G y (U y) (V y)) := by
      funext y
      rfl
    rw [hfun]
    have hm := mvfderiv_mul (I := I) hdfW hGUV
    have hm' := congrArg (fun L => L u) hm
    simpa [realLineCovariantDerivative,
      ContinuousLinearMap.smulRight_apply, Pi.mul_apply, mul_comm,
      add_comm, add_left_comm, add_assoc] using hm'
  have hHessianW :
      realLineCovariantDerivative (I := I) (M := M)
          (fun y => scalarDifferential (I := I) f y (W y)) x u =
        scalarHessian cov f x u z := by
    have h := @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (realLineCovariantDerivative (I := I) (M := M))
      (fun y => scalarDifferential (I := I) f y) W x hdf hW u
    change scalarHessian cov f x u (W x) =
      realLineCovariantDerivative (I := I) (M := M)
          (fun y => scalarDifferential (I := I) f y (W y)) x u -
        scalarDifferential (I := I) f x (cov W x u) at h
    rw [hWzero] at h
    simpa [W] using h.symm
  have htrilinear := realLineCovariantDerivative_trilinear_of_covariantDerivative_eq_zero
    cov hA hW hU hV hWzero hUzero hVzero u
  have htrilinear' :
      covariantThreeTensorCovariantDerivative cov
          (scalarTensorLeibnizTerm f G) x u z a b =
        realLineCovariantDerivative (I := I) (M := M)
          (fun y => scalarDifferential (I := I) f y (W y) *
            G y (U y) (V y)) x u := by
    simpa [G, W, U, V, scalarTensorLeibnizTerm,
      ContinuousLinearMap.smulRight_apply] using htrilinear.symm
  rw [htrilinear', hproductDerivative, hHessianW, hmetricDerivative]
  simp [G, W, U, V]

theorem connectionLaplacian_smul_riemannianMetric
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (f : M → ℝ) {x : M}
    (hf : ∀ y : M, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (u v : TM x) :
    connectionLaplacian cov
        (f • riemannianMetricCovariantTwoTensor (I := I) (M := M)) x u v =
      scalarLaplacian cov f x *
        riemannianMetricCovariantTwoTensor (I := I) (M := M) x u v := by
  let G : ∀ y : M, T₂ y :=
    riemannianMetricCovariantTwoTensor (I := I) (M := M)
  have hG : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z (G z)) y := by
    intro y
    exact riemannianMetricCovariantTwoTensor_mdifferentiableAt
      (I := I) (E := E) (M := M) y
  have hGderiv :
      covariantTwoTensorCovariantDerivative cov G = 0 := by
    funext y
    ext X a b
    exact covariantTwoTensorCovariantDerivative_riemannianMetric_eq_zero
      (I := I) (E := E) (M := M) cov hmetric y X a b
  have hfirst : MDifferentiableAt I
      (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov G y)) x := by
    rw [hGderiv]
    exact mdifferentiableAt_zeroSection
      (𝕜 := ℝ)
      (F := E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
      (E := T₃) (B := M) (EB := E) (HB := H) (IB := I) (x := x)
  have hHessianG :
      covariantHessianTwoTensor cov G x = 0 := by
    unfold covariantHessianTwoTensor
    rw [hGderiv]
    simp [covariantThreeTensorCovariantDerivative,
      inducedHomCovariantDerivative]
  have hrem : MDifferentiableAt I
      (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (scalarTensorLeibnizTerm f G y)) x :=
    mdifferentiableAt_scalarTensorLeibnizTerm f G hdf (hG x)
  have hprod := covariantHessianTwoTensor_smul_function
    cov hG hf hfirst hrem
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [connectionLaplacian_eq_sum_orthonormalBasis cov
    (f • G) x b, scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp only [sum_apply]
  calc
    ∑ i, ((((covariantHessianTwoTensor cov (f • G) x) (b i))
        (b i)) u) v =
      ∑ i, ((scalarHessian cov f x (b i) (b i)) *
        G x u v) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hprodEval := congrArg (fun B => B (b i) (b i) u v) hprod
      have htrilinear := covariantThreeTensorCovariantDerivative_scalarTensor_metric
        cov hmetric f hdf (b i) (b i) u v
      have htrilinear' :
          covariantThreeTensorCovariantDerivative cov
              (scalarTensorLeibnizTerm f G) x (b i) (b i) u v =
            scalarHessian cov f x (b i) (b i) * G x u v := by
        simpa [G] using htrilinear
      have hzeroH :
          (((f x • covariantHessianTwoTensor cov G x) (b i))
              (b i) u) v = 0 := by
        rw [hHessianG]
        simp
      have hzeroD :
          (((((d% f x).smulRight
              (covariantTwoTensorCovariantDerivative cov G x)) (b i))
                (b i)) u) v = 0 := by
        rw [hGderiv]
        simp [ContinuousLinearMap.smulRight_apply]
      rw [hprodEval]
      simp only [add_apply]
      rw [hzeroH, hzeroD]
      simp only [zero_add, add_zero]
      rw [htrilinear']
    _ = (∑ i, ((scalarHessian cov f x) (b i)) (b i)) *
        G x u v := by
      rw [Finset.sum_mul]

end CovariantDerivative
