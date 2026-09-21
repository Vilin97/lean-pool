/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicSliceAssembly

/-!
# C² regularity of the actual Hamilton--Ivey curvature operator

The three-dimensional lowered curvature operator is the scalar-curvature multiple of the metric
minus twice the actual Ricci tensor.  This module derives its C² regularity from the corresponding
slice fields instead of assuming regularity of the operator itself.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 4 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]
  [SigmaCompactSpace M] [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
local notation "T₃" => (fun y : M => TM y →L[ℝ] T₂ y)

/-- The actual lowered curvature-operator tensor is C² whenever its metric,
scalar-curvature, and actual Ricci fields are C² on the selected slice. -/
theorem HamiltonIveyCurvatureOperatorC2.of_sliceRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ)
    (hregularity : HamiltonIveyIntrinsicSliceRegularity g cov hcov hLevi t) :
    g.HamiltonIveyCurvatureOperatorC2 cov hcov hLevi hdim t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : IsContMDiffRiemannianBundle I 2 E TM := hregularity.metricC2
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    ContMDiffVectorBundle.continuousLinearMap
  have hmetric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) y ((g t).inner y)) := by
    rcases hregularity.metricC2.exists_contMDiff with ⟨q, hq, hqeq⟩
    convert hq using 1
    funext y
    congr 1
    ext u v
    exact hqeq y u v
  have hscalar : ContMDiff I 𝓘(ℝ) 2
      (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y) :=
    hregularity.scalarC2
  have hricci : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) :=
    hregularity.ricciC2
  let pointwiseSMul : ∀ y : M, SMul (M → ℝ) (T₂ y) := fun y =>
    ⟨fun f A => f y • A⟩
  letI : ∀ y : M, SMul (M → ℝ) (T₂ y) := pointwiseSMul
  have hscalarMetric := hscalar.smul_section hmetric
  have htwo : ContMDiff I 𝓘(ℝ) 2 (fun _ : M => (2 : ℝ)) :=
    contMDiff_const
  have htwoRicci := htwo.smul_section hricci
  have hoperatorRaw : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) y
        ((fun z => CovariantDerivative.scalarCurvature (cov := cov t) z) •
            (g t).inner y -
          (fun _ : M => (2 : ℝ)) •
            CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) := by
    exact hscalarMetric.sub_section htwoRicci
  have hscalarPointwise (y : M) :
      (fun z => CovariantDerivative.scalarCurvature (cov := cov t) z) •
          (g t).inner y =
        CovariantDerivative.scalarCurvature (cov := cov t) y • (g t).inner y := by
    change (pointwiseSMul y).smul
        (fun z => CovariantDerivative.scalarCurvature (cov := cov t) z)
        ((g t).inner y) = _
    rfl
  have htwoPointwise (y : M) :
      (fun _ : M => (2 : ℝ)) •
          CovariantDerivative.ricciCovariantTwoTensor (cov t) y =
        (2 : ℝ) • CovariantDerivative.ricciCovariantTwoTensor (cov t) y := by
    change (pointwiseSMul y).smul (fun _ : M => (2 : ℝ))
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y) = _
    rfl
  have hoperator : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) y
        (CovariantDerivative.scalarCurvature (cov := cov t) y • (g t).inner y -
          (2 : ℝ) • CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) := by
    simpa only [hscalarPointwise, htwoPointwise] using hoperatorRaw
  have hoperatorEq :
      (fun y => g.curvatureOperatorTwoTensor cov hcov t y) =
      (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y • (g t).inner y -
        (2 : ℝ) • CovariantDerivative.ricciCovariantTwoTensor (cov t) y) := by
    funext y
    ext u v
    simp [TimeDependentRiemannianMetric.curvatureOperatorTwoTensor,
      TimeDependentRiemannianMetric.ricciCurvatureContinuous_apply,
      CovariantDerivative.ricciCovariantTwoTensor_apply]
  have hoperator' : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) y (g.curvatureOperatorTwoTensor cov hcov t y)) := by
    intro y
    refine (hoperator y).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun z => by
      apply congrArg (fun A : T₂ z =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) z A)
      exact congrFun hoperatorEq z)
  simpa [HamiltonIveyCurvatureOperatorC2] using hoperator'

/-- Derive the operator C² field from the regularity record assembled from actual C³ connection
regularity on the selected slice and an actual C² metric slice. -/
theorem HamiltonIveyCurvatureOperatorC2.of_connectionC3At
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov) (t : ℝ)
    (hcov₂ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 2)
    (hcov₃t : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 3)
    (hmetric₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 2 E TM)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3) :
    g.HamiltonIveyCurvatureOperatorC2 cov hcov hLevi hdim t := by
  exact HamiltonIveyCurvatureOperatorC2.of_sliceRegularity g cov hcov hLevi hdim t
    (HamiltonIveyIntrinsicSliceRegularity.of_connectionC3At
      g cov hcov hLevi t hcov₂ hcov₃t hmetric₂)

/-- A C² actual operator section and the induced C¹ two-tensor connection give the pointwise
regularity package used by the Hamilton--Ivey evolution argument. -/
theorem HamiltonIveyCurvatureOperatorRegularity.of_sliceRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {t : ℝ} (hregularity : HamiltonIveyIntrinsicSliceRegularity g cov hcov hLevi t)
    (x : M) :
    g.HamiltonIveyCurvatureOperatorRegularity cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hC2 := HamiltonIveyCurvatureOperatorC2.of_sliceRegularity
    g cov hcov hLevi hdim t hregularity
  have hderivative : g.HamiltonIveyCurvatureOperatorDerivativeRegularity cov hcov t := by
    simpa [HamiltonIveyCurvatureOperatorDerivativeRegularity] using
      (CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_one
        (I := I) (E := E) (M := M) (cov t))
  exact HamiltonIveyCurvatureOperatorRegularity.of_contMDiff_two
    g cov hcov hLevi hdim hderivative x hC2

end CovariantDerivative.TimeDependentRiemannianMetric

end
