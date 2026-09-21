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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.InducedHomCurvature
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHomRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection

/-!
# Curvature action on a metric two-tensor

This file isolates the pointwise tensorial identity saying that curvature of
the induced covariant-two-tensor connection acts with a minus sign in each
covariant slot.  It is intentionally independent of compactness and of
Ricci-flow data.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]
  [hContTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)

local instance metricCurvatureScalarTopologicalSpace :
    TopologicalSpace (TotalSpace ℝ (Bundle.Trivial M ℝ)) :=
  Bundle.Trivial.topologicalSpace M ℝ
local instance metricCurvatureScalarFiberBundle :
    FiberBundle ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.fiberBundle M ℝ
local instance metricCurvatureScalarVectorBundle :
    VectorBundle ℝ ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.vectorBundle ℝ M ℝ
local instance metricCurvatureScalarContMDiffVectorBundle :
    ContMDiffVectorBundle 2 ℝ (Bundle.Trivial M ℝ) I :=
  Bundle.Trivial.contMDiffVectorBundle ℝ

local instance metricCurvatureCovectorNormedAddCommGroup :
    ∀ y : M, NormedAddCommGroup (T₁ y) :=
  fun _ => ContinuousLinearMap.toNormedAddCommGroup
local instance metricCurvatureCovectorNormedSpace :
    ∀ y : M, NormedSpace ℝ (T₁ y) :=
  fun _ => ContinuousLinearMap.toNormedSpace
local instance metricCurvatureCovectorFiniteDimensional :
    ∀ y : M, FiniteDimensional ℝ (T₁ y) :=
  fun _ => inferInstance

local instance metricCurvatureTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance metricCurvatureTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance metricCurvatureTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance metricCurvatureTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance metricCurvatureTwoFiberTopologicalSpace (y : M) :
    TopologicalSpace (T₂ y) := inferInstance

local instance metricCurvatureOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance metricCurvatureOneFiberBundle :
    FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance metricCurvatureOneVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance metricCurvatureOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance metricCurvatureTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance metricCurvatureTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance metricCurvatureTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance metricCurvatureTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-! Curvature of the induced connection on covariant two-tensors acts with
the negative curvature action in each covariant slot.  The regularity in the
statement is exactly what is used to form the two curvature commutators. -/
theorem covariantTwoTensor_curvatureAux_apply_of_contMDiff
    (cov : CovariantDerivative I E TM)
    [hcov : ContMDiffCovariantDerivative cov 1]
    {h : ∀ y : M, T₂ y}
    (hh : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 2
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)))
    {X Y U V : ∀ y : M, TM y}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (Y y)))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (U y)))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (V y)))
    (x : M) :
    (covariantTwoTensorCovariantDerivative cov).curvatureAux X Y h x
    (U x) (V x) =
    -h x (cov.curvatureAux X Y U x) (V x) -
      h x (U x) (cov.curvatureAux X Y V x) := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) :=
    PoincareCurvature.instNormedAddCommGroupTangentSpace I
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) :=
    PoincareCurvature.instNormedSpaceTangentSpace I
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let cov₀ := realLineCovariantDerivative (I := I) (M := M)
  let hcov₀ : ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_realLine (I := I) (M := M)
  letI : ContMDiffCovariantDerivative cov₀ 1 := hcov₀
  let cov₁ := covectorCovariantDerivative (I := I) (M := M) cov
  let hcov₁ : ContMDiffCovariantDerivative cov₁ 1 := by
    dsimp [cov₁, covectorCovariantDerivative, cov₀,
      realLineCovariantDerivative, Bundle.Trivial]
    exact @CovariantDerivative.contMDiffCovariantDerivative_inducedHom
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM (Bundle.Trivial M ℝ) _ _ nTM sTM fTM _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      metricCurvatureScalarFiberBundle metricCurvatureScalarVectorBundle
      hContTangent metricCurvatureScalarContMDiffVectorBundle
      cov cov₀ hcov hcov₀
  letI : ContMDiffCovariantDerivative cov₁ 1 := hcov₁
  let cov₂ := covariantTwoTensorCovariantDerivative cov
  let hcov₂ : ContMDiffCovariantDerivative cov₂ 1 := by
    dsimp [cov₂, covariantTwoTensorCovariantDerivative, cov₁,
      covectorCovariantDerivative, cov₀, realLineCovariantDerivative,
      Bundle.Trivial]
    exact @CovariantDerivative.contMDiffCovariantDerivative_inducedHom
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _ nTM sTM fTM _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      metricCurvatureOneFiberBundle metricCurvatureOneVectorBundle
      hContTangent metricCurvatureOneContMDiffVectorBundle
      cov cov₁ hcov hcov₁
  letI : ContMDiffCovariantDerivative cov₂ 1 := hcov₂
  let ψ : ∀ y : M, T₁ y := fun y => h y (U y)
  let f : M → ℝ := fun y => ψ y (V y)
  have hX₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (X y)) :=
    hX.of_le (by norm_num)
  have hY₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (Y y)) :=
    hY.of_le (by norm_num)
  have hψ₂ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (ψ y)) := by
    simpa [ψ] using hh.clm_bundle_apply hU
  have hfTotal : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (f y)) := by
    simpa [f, ψ] using hψ₂.clm_bundle_apply hV
  have hf : ContMDiff I 𝓘(ℝ) 2 f := by
    intro y
    simpa [Bundle.Trivial.eq_trivialization M ℝ,
      Bundle.Trivial.trivialization_apply] using
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) y).contMDiffAt_section_iff
        (n := (2 : WithTop ℕ∞))
        (FiberBundle.mem_baseSet_trivializationAt' y)).mp (hfTotal y)
  have hhAt : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z (h z)) y := by
    intro y
    exact (hh y).mdifferentiableAt (by norm_num)
  have hψAt : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) z (ψ z)) y := by
    intro y
    exact (hψ₂ y).mdifferentiableAt (by norm_num)
  have hUAt : ∀ y : M, MDiffAt (T% U) y := by
    intro y
    exact (hU y).mdifferentiableAt (by norm_num)
  have hVAt : ∀ y : M, MDiffAt (T% V) y := by
    intro y
    exact (hV y).mdifferentiableAt (by norm_num)
  have hψAlongX : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along X ψ y)) :=
    cov₁.contMDiff_along (n := 1) hX₁ hψ₂
  have hψAlongY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along Y ψ y)) :=
    cov₁.contMDiff_along (n := 1) hY₁ hψ₂
  have hψAlongXAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along X ψ y)) x :=
    (hψAlongX x).mdifferentiableAt (by norm_num)
  have hψAlongYAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along Y ψ y)) x :=
    (hψAlongY x).mdifferentiableAt (by norm_num)
  have hUAlongX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along X U y)) :=
    cov.contMDiff_along (n := 1) hX₁ hU
  have hUAlongY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along Y U y)) :=
    cov.contMDiff_along (n := 1) hY₁ hU
  have hVAlongX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along X V y)) :=
    cov.contMDiff_along (n := 1) hX₁ hV
  have hVAlongY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along Y V y)) :=
    cov.contMDiff_along (n := 1) hY₁ hV
  have hUAlongXVecAt : MDiffAt (T% (cov.along X U)) x :=
    (hUAlongX x).mdifferentiableAt (by norm_num)
  have hUAlongYVecAt : MDiffAt (T% (cov.along Y U)) x :=
    (hUAlongY x).mdifferentiableAt (by norm_num)
  have hVAlongXAt : MDiffAt (T% (cov.along X V)) x :=
    (hVAlongX x).mdifferentiableAt (by norm_num)
  have hVAlongYAt : MDiffAt (T% (cov.along Y V)) x :=
    (hVAlongY x).mdifferentiableAt (by norm_num)
  have hψVAlongXAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (ψ y (cov.along X V y))) x :=
    (hψAt x).clm_bundle_apply hVAlongXAt
  have hψVAlongYAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (ψ y (cov.along Y V y))) x :=
    (hψAt x).clm_bundle_apply hVAlongYAt
  have hHAlongXSection : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along X h y)) :=
    cov₂.contMDiff_along (n := 1) hX₁ hh
  have hHAlongYSection : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along Y h y)) :=
    cov₂.contMDiff_along (n := 1) hY₁ hh
  have hHAlongXAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along X h y)) x :=
    (hHAlongXSection x).mdifferentiableAt (by norm_num)
  have hHAlongYAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along Y h y)) x :=
    (hHAlongYSection x).mdifferentiableAt (by norm_num)
  have hhAlongXUAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (h y (cov.along X U y))) x :=
    (hhAt x).clm_bundle_apply hUAlongXVecAt
  have hhAlongYUAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (h y (cov.along Y U y))) x :=
    (hhAt x).clm_bundle_apply hUAlongYVecAt
  have hfAlongX : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) 1
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along X f y)) :=
    cov₀.contMDiff_along (n := 1) hX₁ hfTotal
  have hfAlongY : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) 1
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along Y f y)) :=
    cov₀.contMDiff_along (n := 1) hY₁ hfTotal
  have hfAlongXAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along X f y)) x :=
    (hfAlongX x).mdifferentiableAt (by norm_num)
  have hfAlongYAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along Y f y)) x :=
    (hfAlongY x).mdifferentiableAt (by norm_num)
  have hInner := @curvatureAux_inducedHom_apply_at
    E _ _ H _ I M _ _ _ _ _ _
    E ℝ _ _ _ _ _ _
    TM (Bundle.Trivial M ℝ) _ _ nTM sTM fTM
    (fun _ : M => (inferInstance : NormedAddCommGroup ℝ))
    (fun _ : M => (inferInstance : NormedSpace ℝ ℝ))
    (fun _ : M => (inferInstance : FiniteDimensional ℝ ℝ))
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    metricCurvatureScalarFiberBundle metricCurvatureScalarVectorBundle
    hContTangent metricCurvatureScalarContMDiffVectorBundle
    cov cov₀ (φ := ψ) (σ := V) (X := X) (Y := Y) (x := x)
    hψAt hVAt hψAlongXAt hψAlongYAt
    hVAlongXAt hVAlongYAt hfAlongYAt hfAlongXAt
    hψVAlongXAt hψVAlongYAt
  have hflat : cov₀.curvatureAux X Y (fun y => ψ y (V y)) x = 0 := by
    have hscalar : ContMDiff I 𝓘(ℝ) 2 (fun y => ψ y (V y)) := by
      simpa [f] using hf
    have h := extDerivFun_lieBracket_commutator
      (I := I) (f := fun y => ψ y (V y)) (X := X) (Y := Y) (x := x)
      hscalar hX₁ hY₁
    change
      mvfderiv (I := I)
          (fun y => mvfderiv (I := I) (fun z => ψ z (V z)) y (Y y))
          x (X x) -
        mvfderiv (I := I)
          (fun y => mvfderiv (I := I) (fun z => ψ z (V z)) y (X y))
          x (Y x) -
        mvfderiv (I := I) (fun z => ψ z (V z)) x
          (VectorField.mlieBracket I X Y x) = 0
    exact h
  have hInner' :
      cov₁.curvatureAux X Y ψ x (V x) =
        -ψ x (cov.curvatureAux X Y V x) := by
    have hInner₀ :
        cov₁.curvatureAux X Y ψ x (V x) =
        cov₀.curvatureAux X Y (fun y => ψ y (V y)) x -
            ψ x (cov.curvatureAux X Y V x) := by
      exact hInner
    calc
      cov₁.curvatureAux X Y ψ x (V x) =
          cov₀.curvatureAux X Y (fun y => ψ y (V y)) x -
            ψ x (cov.curvatureAux X Y V x) := hInner₀
      _ = -ψ x (cov.curvatureAux X Y V x) := by
        simpa [hflat]
  have hOuter := @curvatureAux_inducedHom_apply_at
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] ℝ) _ _ _ _ _ _
    TM T₁ _ _ nTM sTM fTM
    metricCurvatureCovectorNormedAddCommGroup metricCurvatureCovectorNormedSpace _
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    metricCurvatureOneFiberBundle metricCurvatureOneVectorBundle
    hContTangent metricCurvatureOneContMDiffVectorBundle
    cov cov₁ (φ := h) (σ := U) (X := X) (Y := Y) (x := x)
    hhAt hUAt hHAlongXAt hHAlongYAt
    hUAlongXVecAt hUAlongYVecAt hψAlongYAt hψAlongXAt
    hhAlongXUAt hhAlongYUAt
  have hOuterV := congrArg (fun α : T₁ x => α (V x)) hOuter
  have hOuterAction :
      (covariantTwoTensorCovariantDerivative cov).curvatureAux X Y h x
          (U x) (V x) =
        (cov₁.curvatureAux X Y ψ x -
          h x (cov.curvatureAux X Y U x)) (V x) := by
    exact hOuterV
  calc
    (covariantTwoTensorCovariantDerivative cov).curvatureAux X Y h x
        (U x) (V x) =
      cov₁.curvatureAux X Y ψ x (V x) -
        h x (cov.curvatureAux X Y U x) (V x) := by
          simpa only [ContinuousLinearMap.sub_apply] using hOuterAction
    _ = -h x (cov.curvatureAux X Y U x) (V x) -
        h x (U x) (cov.curvatureAux X Y V x) := by
          rw [hInner']
          simp only [ψ]
          ring

/-- For a `C²` Riemannian metric viewed as a bilinear-form section, the
induced curvature has the usual negative action in its two covariant slots. -/
theorem covariantTwoTensor_curvatureAux_metric_toSection_apply_of_contMDiff
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative cov 1]
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    {X Y U V : ∀ y : M, TM y}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (Y y)))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (U y)))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y => TotalSpace.mk' E y (V y)))
    (x : M) :
    (covariantTwoTensorCovariantDerivative cov).curvatureAux X Y g.toSection x
      (U x) (V x) =
      -g.toSection x (cov.curvatureAux X Y U x) (V x) -
        g.toSection x (U x) (cov.curvatureAux X Y V x) := by
  exact covariantTwoTensor_curvatureAux_apply_of_contMDiff cov
    g.contMDiff_toSection hX hY hU hV x

/-- A fully pointwise version of the metric-curvature action.  The tangent
vectors are extended by the canonical smooth extension only to evaluate the
raw curvature commutator. -/
theorem covariantTwoTensor_curvatureAux_metric_toSection_apply
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative cov 1]
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (x : M) (X Y u v : TM x) :
    (covariantTwoTensorCovariantDerivative cov).curvatureAux
        (smoothExtend (I := I) (F := E) (V := TM) x X)
        (smoothExtend (I := I) (F := E) (V := TM) x Y)
        g.toSection x u v =
      -g.toSection x (cov.curvatureTensor x X Y u) v -
        g.toSection x u (cov.curvatureTensor x X Y v) := by
  simpa [CovariantDerivative.curvatureTensor_apply, smoothExtend_apply] using
    (covariantTwoTensor_curvatureAux_metric_toSection_apply_of_contMDiff
      cov g
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x X)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x Y)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u)
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v) x)

end CovariantDerivative
