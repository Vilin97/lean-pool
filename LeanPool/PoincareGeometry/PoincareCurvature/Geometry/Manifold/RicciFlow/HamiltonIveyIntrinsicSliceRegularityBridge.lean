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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicGeometricEvolution

/-!
# A higher-regularity bridge for Hamilton--Ivey slice traces

The intrinsic trace calculation asks for differentiability of several actual
Ricci-derived fields.  This file records a reusable bridge from `C²`
regularity of the genuine Ricci two-tensor, together with the slice metric and
connection regularity, to that derived record.  The remaining geometric step
is to derive this `C²` regularity of Ricci from higher regularity of the
Levi-Civita connection.
-/

@[expose] public section

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
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)

local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
local notation "T₃" => (fun y : M => TM y →L[ℝ] T₂ y)

local instance sliceBridgeScalarTopologicalSpace :
    TopologicalSpace (TotalSpace ℝ (Bundle.Trivial M ℝ)) :=
  Bundle.Trivial.topologicalSpace M ℝ
local instance sliceBridgeScalarFiberBundle :
    FiberBundle ℝ (Bundle.Trivial M ℝ) := Bundle.Trivial.fiberBundle M ℝ
local instance sliceBridgeScalarVectorBundle :
    VectorBundle ℝ ℝ (Bundle.Trivial M ℝ) := Bundle.Trivial.vectorBundle ℝ M ℝ
local instance sliceBridgeScalarContMDiffVectorBundle :
    ContMDiffVectorBundle 2 ℝ (Bundle.Trivial M ℝ) I :=
  Bundle.Trivial.contMDiffVectorBundle ℝ

local instance sliceBridgeCovectorNormedAddCommGroup :
    ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ => ContinuousLinearMap.toNormedAddCommGroup
local instance sliceBridgeCovectorNormedSpace :
    ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ => ContinuousLinearMap.toNormedSpace
local instance sliceBridgeTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance sliceBridgeTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance sliceBridgeTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := ContinuousLinearMap.toNormedAddCommGroup
local instance sliceBridgeTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := ContinuousLinearMap.toNormedSpace
local instance sliceBridgeTwoFiberTopologicalSpace (y : M) :
    TopologicalSpace (T₂ y) := inferInstance
local instance sliceBridgeOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance sliceBridgeOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance sliceBridgeOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance sliceBridgeOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap
local instance sliceBridgeTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance sliceBridgeTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance sliceBridgeTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance sliceBridgeTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap
local instance sliceBridgeThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance sliceBridgeThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance sliceBridgeThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := ContinuousLinearMap.toNormedAddCommGroup
local instance sliceBridgeThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := ContinuousLinearMap.toNormedSpace
local instance sliceBridgeThreeFiberTopologicalSpace (y : M) :
    TopologicalSpace (T₃ y) := inferInstance
local instance sliceBridgeThreeTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance sliceBridgeThreeFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance sliceBridgeThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance sliceBridgeThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap
/-- If the genuine Ricci two-tensor is `C²` on a slice, all pointwise
differentiability fields required by the intrinsic Ricci trace calculation
follow from the actual induced tensor connection and Riemannian raising map.
No derivative of Ricci or trace-regularity field is supplied separately. -/
theorem intrinsicRicciTraceRegularity_of_ricciC2
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov) (t : ℝ)
    (hmetric₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 2 E TM)
    (hRicci₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M => TM z →L[ℝ] TM z →L[ℝ] ℝ) y
          (CovariantDerivative.ricciCovariantTwoTensor (cov t) y))) :
    ∀ x : M, intrinsicRicciTraceRegularity g cov hcov hLevi t x := by
  intro x
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : IsContMDiffRiemannianBundle I 2 E TM := hmetric₂
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hRicciRaised : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (CovariantDerivative.raisedRicciEndomorphism (cov t) z)) y := by
    intro y
    have hR : MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (CovariantDerivative.raisedCovariantTwoTensor
            (I := I) (E := E)
            (CovariantDerivative.ricciCovariantTwoTensor (cov t)) z)) y := by
      exact CovariantDerivative.raisedCovariantTwoTensor_mdifferentiableAt
        (I := I) (E := E) (M := M)
        ((hRicci₂ y).mdifferentiableAt (by norm_num))
    convert hR using 1 <;> ext z <;>
      simp [CovariantDerivative.raisedRicciEndomorphism,
        CovariantDerivative.raisedCovariantTwoTensor]
  have hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := fun z : M => TM z →L[ℝ] (TM z →L[ℝ] (TM z →L[ℝ] ℝ))) y
        (CovariantDerivative.covariantTwoTensorCovariantDerivative (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t)) y)) x := by
    let cov₂ := CovariantDerivative.covariantTwoTensorCovariantDerivative
      (I := I) (M := M) (cov t)
    letI : ContMDiffCovariantDerivative cov₂ 1 :=
      CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_one
        (I := I) (E := E) (M := M) (cov t)
    have hRicci₂' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        (1 + 1)
        (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M => TM z →L[ℝ] TM z →L[ℝ] ℝ)
          y (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) := by
      exact hRicci₂.of_le (by norm_num)
    have hRicci₂On : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        (1 + 1)
        (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M => TM z →L[ℝ] TM z →L[ℝ] ℝ)
          y (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) Set.univ := by
      simpa [contMDiffOn_univ] using hRicci₂'
    have hD :=
      (inferInstance : ContMDiffCovariantDerivative cov₂ 1).contMDiff.contMDiff
        hRicci₂On
    have hDx := (hD x (Set.mem_univ x)).contMDiffAt
      (isOpen_univ.mem_nhds (Set.mem_univ x))
    have hDx' := hDx.mdifferentiableAt (by norm_num)
    simpa [cov₂, CovariantDerivative.covariantTwoTensorCovariantDerivative] using hDx'
  have htraceDifferential : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun z : M => TM z →L[ℝ] ℝ) y
        (CovariantDerivative.scalarDifferential (I := I)
          (CovariantDerivative.covariantTwoTensorTraceFunction (I := I) (E := E)
            (CovariantDerivative.ricciCovariantTwoTensor (cov t))) y)) x := by
    exact CovariantDerivative.mdifferentiableAt_scalarDifferential_covariantTwoTensorTraceFunction
      (I := I) (E := E) (M := M) (cov := cov t) (hmetric := (hLevi t).2)
      (h := CovariantDerivative.ricciCovariantTwoTensor (cov t)) hRicciRaised hfirst
  have hsecondRaised : ∀ Y : TM x,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (CovariantDerivative.raisedCovariantTwoTensor (I := I) (E := E)
            (CovariantDerivative.covariantTwoTensorDerivativeAlong (cov t)
              (CovariantDerivative.ricciCovariantTwoTensor (cov t))
              (smoothExtend (I := I) (F := E) (V := TM) x Y)) z)) x := by
    intro Y
    have hY : MDiffAt (T% (smoothExtend (I := I) (F := E) (V := TM) x Y)) x :=
      ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x Y) x).mdifferentiableAt
        (by norm_num)
    have hDalong : MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun w : M => TM w →L[ℝ] TM w →L[ℝ] ℝ) z
          (CovariantDerivative.covariantTwoTensorDerivativeAlong (cov t)
            (CovariantDerivative.ricciCovariantTwoTensor (cov t))
            (smoothExtend (I := I) (F := E) (V := TM) x Y) z)) x := by
      have happly := hfirst.clm_bundle_apply hY
      simpa [CovariantDerivative.covariantTwoTensorDerivativeAlong] using happly
    exact CovariantDerivative.raisedCovariantTwoTensor_mdifferentiableAt
      (I := I) (E := E) (M := M) hDalong
  exact ⟨hRicciRaised, hfirst, htraceDifferential, hsecondRaised⟩

end CovariantDerivative.TimeDependentRiemannianMetric

end
