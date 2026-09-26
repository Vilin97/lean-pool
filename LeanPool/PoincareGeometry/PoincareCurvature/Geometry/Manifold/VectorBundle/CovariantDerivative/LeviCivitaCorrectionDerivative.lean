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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.MetricDefectTensorDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivitaCorrectionKoszul
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConnectionChange
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.FirstOrderParallelExtension
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearEvaluation

/-!
# Covariant derivative of the Levi-Civita correction

For a torsion-free affine background connection, differentiating the Koszul
formula for its Levi-Civita correction expresses the covariant derivative of
that correction through the covariant Hessian of the metric and the one
metric-defect term caused by differentiating the metric pairing.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-! The nested induced tensor bundles are not synthesized through the two
successive continuous-linear-map constructions.  Name their inherited
bundle structures locally so the Hessian regularity hypothesis is stated in
the same intrinsic bundle as `covariantHessianTwoTensor`. -/
local instance correctionDerivativeScalarTopologicalSpace :
    TopologicalSpace (TotalSpace ℝ (Bundle.Trivial M ℝ)) :=
  Bundle.Trivial.topologicalSpace M ℝ
local instance correctionDerivativeScalarFiberBundle :
    FiberBundle ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.fiberBundle M ℝ
local instance correctionDerivativeScalarVectorBundle :
    VectorBundle ℝ ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.vectorBundle ℝ M ℝ
local instance correctionDerivativeScalarContMDiffVectorBundle :
    ContMDiffVectorBundle 2 ℝ (Bundle.Trivial M ℝ) I :=
  Bundle.Trivial.contMDiffVectorBundle ℝ

local instance correctionDerivativeOneFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₁ y) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance correctionDerivativeOneFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₁ y) :=
  ContinuousLinearMap.toNormedSpace
local instance correctionDerivativeOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance correctionDerivativeOneFiberBundle :
    FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance correctionDerivativeOneVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance correctionDerivativeOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance correctionDerivativeTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance correctionDerivativeTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance correctionDerivativeTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance correctionDerivativeTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance correctionDerivativeTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance correctionDerivativeTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance correctionDerivativeTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance correctionDerivativeTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance correctionDerivativeThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance correctionDerivativeThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance correctionDerivativeThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance correctionDerivativeThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance correctionDerivativeThreeTopologicalSpace :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance correctionDerivativeThreeFiberBundle :
    FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance correctionDerivativeThreeVectorBundle :
    VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance correctionDerivativeThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- Differentiating the torsion-free Koszul formula for the explicit
Levi-Civita correction.  The first three terms are the covariant Hessian of
the ambient metric tensor; the final metric-defect term is the correction
from differentiating the output pairing with a non-metric background
connection. -/
theorem covariantDerivativeOneForm_leviCivitaCorrection_inner_eq_hessian_metricDefect
    (cov : CovariantDerivative I E TM) [ContMDiffCovariantDerivative cov 1]
    (hTorsionFree : cov.IsTorsionFree) {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov
          (riemannianMetricCovariantTwoTensor (I := I) (M := M)) y)) x)
    (X v u w : TM x) :
    2 * inner ℝ
        (covariantDerivativeOneForm cov cov.leviCivitaCorrection x X v u) w =
      covariantHessianTwoTensor cov
          (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X u v w +
        covariantHessianTwoTensor cov
          (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X v u w -
        covariantHessianTwoTensor cov
          (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X w u v -
        2 * cov.metricDefect x (cov.leviCivitaCorrection x v u) w X := by
  let U : ∀ y : M, TM y :=
    firstOrderParallelSmoothExtend (I := I) (F := E) (V := TM) cov x u
  let V : ∀ y : M, TM y :=
    firstOrderParallelSmoothExtend (I := I) (F := E) (V := TM) cov x v
  let W : ∀ y : M, TM y :=
    firstOrderParallelSmoothExtend (I := I) (F := E) (V := TM) cov x w
  let B : ∀ y : M, T₃ y :=
    covariantTwoTensorCovariantDerivative cov
      (riemannianMetricCovariantTwoTensor (I := I) (M := M))
  let q₀ : M → ℝ := fun y =>
    inner ℝ (cov.leviCivitaCorrection y (V y) (U y)) (W y)
  let q₁ : M → ℝ := fun y => B y (U y) (V y) (W y)
  let q₂ : M → ℝ := fun y => B y (V y) (U y) (W y)
  let q₃ : M → ℝ := fun y => B y (W y) (U y) (V y)
  have hU : MDiffAt (T% U) x := by
    simpa [U] using
      (firstOrderParallelSmoothExtend_mdifferentiableAt
        (I := I) (F := E) (V := TM) cov x u)
  have hV : MDiffAt (T% V) x := by
    simpa [V] using
      (firstOrderParallelSmoothExtend_mdifferentiableAt
        (I := I) (F := E) (V := TM) cov x v)
  have hW : MDiffAt (T% W) x := by
    simpa [W] using
      (firstOrderParallelSmoothExtend_mdifferentiableAt
        (I := I) (F := E) (V := TM) cov x w)
  have hUx : U x = u := by simp [U]
  have hVx : V x = v := by simp [V]
  have hWx : W x = w := by simp [W]
  have hUzero : cov U x = 0 := by
    simpa [U] using
      (covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
        (I := I) (F := E) (V := TM) cov x u)
  have hVzero : cov V x = 0 := by
    simpa [V] using
      (covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
        (I := I) (F := E) (V := TM) cov x v)
  have hWzero : cov W x = 0 := by
    simpa [W] using
      (covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
        (I := I) (F := E) (V := TM) cov x w)
  have hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := fun z : M =>
        TM z →L[ℝ] TM z →L[ℝ] TM z) y (cov.leviCivitaCorrection y)) x := by
    exact (contMDiff_leviCivitaCorrection_section
      (I := I) (E := E) (cov := cov) x).mdifferentiableAt one_ne_zero
  have hP : MDiffAt (T% (fun y =>
      cov.leviCivitaCorrection y (V y) (U y))) x :=
    (hA.clm_bundle_apply hV).clm_bundle_apply hU
  have hq₀ : MDiffAt q₀ x := by
    simpa [q₀] using mdiffAt_inner_sections hP hW
  have scalar_mdiff_of_total {f : M → ℝ}
      (hf : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
        (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (f y)) x) :
      MDiffAt f x := by
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I f (FiberBundle.mem_baseSet_trivializationAt' x)).mp hf
    simpa [Bundle.Trivial.eq_trivialization M ℝ] using ht
  have hq₁ : MDiffAt q₁ x := by
    apply scalar_mdiff_of_total
    simpa [q₁, B] using ((hfirst.clm_bundle_apply hU).clm_bundle_apply hV)
      |>.clm_bundle_apply hW
  have hq₂ : MDiffAt q₂ x := by
    apply scalar_mdiff_of_total
    simpa [q₂, B] using ((hfirst.clm_bundle_apply hV).clm_bundle_apply hU)
      |>.clm_bundle_apply hW
  have hq₃ : MDiffAt q₃ x := by
    apply scalar_mdiff_of_total
    simpa [q₃, B] using ((hfirst.clm_bundle_apply hW).clm_bundle_apply hU)
      |>.clm_bundle_apply hV
  have hB_apply (y : M) (a b c : TM y) :
      B y a b c = cov.metricDefect y b c a := by
    dsimp [B]
    exact covariantTwoTensorCovariantDerivative_apply_eq_metricDefect cov
      (riemannianMetricCovariantTwoTensor (I := I) (M := M))
      (riemannianMetricCovariantTwoTensor_mdifferentiableAt (I := I) (E := E) y)
      (fun z p q => rfl) a b c
  have hKoszul : (fun y => 2 * q₀ y) = q₁ + q₂ - q₃ := by
    funext y
    dsimp [q₀, q₁, q₂, q₃]
    rw [leviCivitaCorrection_inner_of_isTorsionFree cov hTorsionFree]
    rw [← hB_apply y (U y) (V y) (W y),
      ← hB_apply y (V y) (U y) (W y),
      ← hB_apply y (W y) (U y) (V y)]
  have hH₁raw := realLineCovariantDerivative_trilinear
    cov (A := B) (X := U) (U := V) (V := W) hfirst hU hV hW X
  have hH₂raw := realLineCovariantDerivative_trilinear
    cov (A := B) (X := V) (U := U) (V := W) hfirst hV hU hW X
  have hH₃raw := realLineCovariantDerivative_trilinear
    cov (A := B) (X := W) (U := U) (V := V) hfirst hW hU hV X
  rw [hUzero, hVzero, hWzero] at hH₁raw hH₂raw hH₃raw
  have hH₁ : mvfderiv (I := I) q₁ x X =
      covariantHessianTwoTensor cov
        (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X u v w := by
    simpa [q₁, B, covariantHessianTwoTensor, hUx, hVx, hWx,
      realLineCovariantDerivative, trivialCovariantDerivative_apply] using hH₁raw
  have hH₂ : mvfderiv (I := I) q₂ x X =
      covariantHessianTwoTensor cov
        (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X v u w := by
    simpa [q₂, B, covariantHessianTwoTensor, hUx, hVx, hWx,
      realLineCovariantDerivative, trivialCovariantDerivative_apply] using hH₂raw
  have hH₃ : mvfderiv (I := I) q₃ x X =
      covariantHessianTwoTensor cov
        (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X w u v := by
    simpa [q₃, B, covariantHessianTwoTensor, hUx, hVx, hWx,
      realLineCovariantDerivative, trivialCovariantDerivative_apply] using hH₃raw
  have hconstDeriv : mvfderiv (I := I) (fun _ : M => (2 : ℝ)) x = 0 := by
    rw [mvfderiv_const]
  have hScaleRaw := congrArg (fun L => L X)
    (mvfderiv_smul (I := I) (x := x)
      (a := fun _ : M => (2 : ℝ)) (g := q₀) mdifferentiableAt_const hq₀)
  have hScale : mvfderiv (I := I) (fun y => 2 * q₀ y) x X =
      2 * mvfderiv (I := I) q₀ x X := by
    have hScaleFunction : (fun _ : M => (2 : ℝ)) • q₀ =
        (fun y => 2 * q₀ y) := by
      funext y
      simp [smul_eq_mul]
    rw [hScaleFunction] at hScaleRaw
    rw [hconstDeriv] at hScaleRaw
    simpa [smul_eq_mul] using hScaleRaw
  have hKoszulDeriv := congrArg (fun f : M → ℝ => mvfderiv (I := I) f x X) hKoszul
  rw [hScale,
    mvfderiv_sub (hq₁.add hq₂) hq₃,
    mvfderiv_add hq₁ hq₂] at hKoszulDeriv
  simp only [add_apply, sub_apply] at hKoszulDeriv
  rw [hH₁, hH₂, hH₃] at hKoszulDeriv
  have hKoszulDeriv' :
      2 * mvfderiv (I := I) q₀ x X =
        covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X u v w +
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X v u w -
          covariantHessianTwoTensor cov
            (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X w u v := by
    exact hKoszulDeriv
  have hDAraw := covariantDerivativeOneForm_apply_eq_along
    (I := I) cov cov.leviCivitaCorrection
    (X := smoothExtend (I := I) (F := E) (V := TM) x X)
    (Y := U) (Z := V) hA hU hV
  have hDA :
      covariantDerivativeOneForm cov cov.leviCivitaCorrection x X v u =
        cov (fun y => cov.leviCivitaCorrection y (V y) (U y)) x X := by
    have hDAexpanded :
        covariantDerivativeOneForm cov cov.leviCivitaCorrection x X v u =
          cov (fun y => cov.leviCivitaCorrection y (V y) (U y)) x X -
            cov.leviCivitaCorrection x v (cov U x X) -
            cov.leviCivitaCorrection x (cov V x X) u := by
      simpa only [covariantDerivativeOneFormAlong, CovariantDerivative.along,
        smoothExtend_apply, hVx, hUx] using hDAraw
    rw [hUzero, hVzero] at hDAexpanded
    simpa using hDAexpanded
  have hDefect := congrArg (fun q => q X)
    (cov.metricDefect_apply_sections hP hW)
  rw [metricDefectAux_apply] at hDefect
  have hPair :
      inner ℝ (cov (fun y => cov.leviCivitaCorrection y (V y) (U y)) x X) w =
        mvfderiv (I := I) q₀ x X -
          cov.metricDefect x (cov.leviCivitaCorrection x v u) w X := by
    rw [hVx, hUx, hWx, hWzero] at hDefect
    have hDefect' :
        cov.metricDefect x (cov.leviCivitaCorrection x v u) w X =
          mvfderiv (I := I) q₀ x X -
            inner ℝ (cov (fun y => cov.leviCivitaCorrection y (V y) (U y)) x X) w := by
      simpa [q₀] using hDefect
    linarith
  rw [hDA]
  linarith

end CovariantDerivative
