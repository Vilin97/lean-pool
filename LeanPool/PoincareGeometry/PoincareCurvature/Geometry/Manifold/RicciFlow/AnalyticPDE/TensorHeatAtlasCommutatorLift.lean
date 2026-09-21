/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasTransition
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasCorrection

/-!
# The genuine finite-atlas tensor-heat commutator lift

This file assembles the supported pairwise chart transports into one bounded
operator on the finite product of normalized forcing spaces.  Its physical
source reconstruction is proved to be exactly the intrinsic finite sum of
cutoff commutators.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ S T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "DW₂" => (E →L[ℝ] W₂)
local notation "D2W₂" => (E →L[ℝ] E →L[ℝ] W₂)

@[reducible] local instance atlasLiftFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup DW₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasLiftFirstDerivativeNormedSpace :
    NormedSpace ℝ DW₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasLiftSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup D2W₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasLiftSecondDerivativeNormedSpace :
    NormedSpace ℝ D2W₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasLiftScalarThirdNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance atlasLiftScalarThirdNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance atlasLiftThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance atlasLiftThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance atlasLiftThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasLiftThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasLiftThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

@[reducible] local instance atlasLiftFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance atlasLiftFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x

/-- The finite matrix of supported pair transports, summed in each target
chart. -/
def atlasCommutatorLiftL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    SourceSpace cov A →L[ℝ] SourceSpace cov A :=
  ContinuousLinearMap.pi fun j =>
    ∑ i : A.cover.Index,
      (supportedPairResidualTransportL cov A j i).comp
        (ContinuousLinearMap.proj i)

@[simp] theorem atlasCommutatorLiftL_apply
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) (j : A.cover.Index) :
    atlasCommutatorLiftL cov A q j =
      ∑ i : A.cover.Index, supportedPairResidualTransportL cov A j i (q i) := by
  simp [atlasCommutatorLiftL, ContinuousLinearMap.comp_apply]

/-- At a point of target piece `j`, the `j`-th output of the finite matrix
represents `r_j²` times the target-frame coordinates of the full intrinsic
atlas commutator. -/
theorem eval_atlasCommutatorLiftL_at_physical_point [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) (j : A.cover.Index)
    {t : ℝ} (ht : t ∈ Ioo t₀ A.commonTerminalTime) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M)) :
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    ParabolicC0AlphaBanach.evalCLM (sj, yj)
        (by simpa using A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht)
        (atlasCommutatorLiftL cov A q j) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (A.atlasCommutatorSlice cov q t x) := by
  dsimp only
  let sj := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (j : M)) t
  let yj := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  have hsj : sj ∈ Ioc t₀ T :=
    A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
  have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ T := by
    simpa [sj, yj] using hsj
  rw [atlasCommutatorLiftL_apply]
  rw [map_sum]
  simp_rw [eval_supportedPairResidualTransportL_at_physical_point
    cov A j _ _ ht hxj]
  rw [← Finset.smul_sum]
  congr 1
  unfold atlasCommutatorSlice intrinsicTensorPairCoordinates
  ext out
  simp

/-- One target chart reconstructs its partition function times the full
intrinsic commutator. -/
theorem physicalLocalSourceSlice_atlasCommutatorLiftL [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) (j : A.cover.Index)
    {t : ℝ} (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    A.physicalLocalSourceSlice cov j (atlasCommutatorLiftL cov A q j) t x =
      A.cover.partition j x • A.atlasCommutatorSlice cov q t x := by
  by_cases hψ : A.cover.partition j x = 0
  · simp [physicalLocalSourceSlice, cutoffLocalTensorOfMatrix, hψ]
  · have hxSupport : x ∈ Function.support (A.cover.partition j) := hψ
    have hxj : x ∈ (A.cover.pieces j : Set M) :=
      subset_closure hxSupport
    have hxPatch := A.cover.pieces_subset_domain j hxj
    have hxFrame : x ∈ (trivializationAt E TM (j : M)).baseSet :=
      A.patch_subset_trivialization (j : M) hxPatch
    apply continuousBilinearMap_ext_localFrame
      (I := I) (trivializationAt E TM (j : M)) b hxFrame
    intro p k
    rw [A.physicalLocalSourceSlice_localFrame cov j
      (atlasCommutatorLiftL cov A q j) t hxFrame p k]
    simp only [smul_apply, smul_eq_mul]
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    have hsj : sj ∈ Ioc t₀ T :=
      A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
    have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ T := by
      simpa [sj, yj] using hsj
    have heval := congrFun
      (eval_atlasCommutatorLiftL_at_physical_point cov A q j ht hxj) (k, p)
    have hrep : ParabolicC0AlphaBanach.representative
          (atlasCommutatorLiftL cov A q j) (sj, yj) (k, p) =
        A.radius (j : M) ^ 2 *
          A.atlasCommutatorSlice cov q t x
            ((trivializationAt E TM (j : M)).localFrame b p x)
            ((trivializationAt E TM (j : M)).localFrame b k x) := by
      rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
        (atlasCommutatorLiftL cov A q j) (sj, yj) hzj]
      simpa [sj, yj, intrinsicTensorPairCoordinates, smul_eq_mul] using heval
    change A.cover.partition j x *
        ((A.radius (j : M))⁻¹ ^ 2 *
          ParabolicC0AlphaBanach.representative
            (atlasCommutatorLiftL cov A q j) (sj, yj) (k, p)) = _
    rw [hrep]
    field_simp [ne_of_gt (A.radius_pos (j : M))]

/-- The physical reconstruction of the assembled bounded operator is the
genuine intrinsic atlas commutator. -/
theorem physicalAtlasSourceSlice_atlasCommutatorLiftL [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) {t : ℝ}
    (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    A.physicalAtlasSourceSlice cov (atlasCommutatorLiftL cov A q) t x =
      A.atlasCommutatorSlice cov q t x := by
  unfold physicalAtlasSourceSlice
  simp_rw [physicalLocalSourceSlice_atlasCommutatorLiftL cov A q _ ht x]
  rw [← Finset.sum_smul]
  have hpartition : ∑ j : A.cover.Index, A.cover.partition j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      A.cover.partition.sum_eq_one (Set.mem_univ x)
  rw [hpartition, one_smul]

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
