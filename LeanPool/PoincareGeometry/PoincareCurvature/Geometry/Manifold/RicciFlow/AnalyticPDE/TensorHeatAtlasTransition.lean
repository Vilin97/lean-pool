/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasCommutatorCoordinate
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasResidual

/-!
# Pairwise coordinate transitions for the tensor-heat atlas

This file constructs the two changes of coordinates needed to transport the
cutoff commutator of one atlas member into the forcing coordinates of
another: the radius-normalized spatial chart transition and the induced
change of covariant-two-tensor frame coordinates.
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

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "Bil₂" => (E →L[ℝ] E →L[ℝ] ℝ)

@[reducible] local instance atlasTransitionBilNormedAddCommGroup :
    NormedAddCommGroup Bil₂ :=
  CovariantDerivative.coordinateTwoModelNormedAddCommGroup
@[reducible] local instance atlasTransitionBilNormedSpace :
    NormedSpace ℝ Bil₂ :=
  CovariantDerivative.coordinateTwoModelNormedSpace
@[reducible] local instance atlasTransitionFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance atlasTransitionFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x

/-- The raw preferred-chart coordinate represented by a normalized spatial
coordinate in atlas member `i`. -/
def denormalizedTensorHeatCoordinate
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (y : E) : E :=
  (extChartAt I (i : M)) (i : M) + A.radius (i : M) • y

/-- The target-to-source normalized spatial coordinate change.  It is used
with `j` as the target forcing chart and `i` as the source commutator chart. -/
def normalizedSpatialTransition
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (y : E) : E :=
  (A.radius (i : M))⁻¹ •
    ((extChartAt I (i : M))
        ((extChartAt I (j : M)).symm
          (denormalizedTensorHeatCoordinate cov A j y)) -
      (extChartAt I (i : M)) (i : M))

/-- On an actual overlap point, the pairwise normalized transition sends the
`j`-coordinate of the point to its `i`-coordinate. -/
theorem normalizedSpatialTransition_normalizedTensorHeatCoordinate
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) {x : M}
    (hxj : x ∈ actualLocalTensorHeatPatch (I := I)
      (j : M) (A.radius (j : M))) :
    normalizedSpatialTransition cov A j i
        (normalizedTensorHeatCoordinate (I := I)
          (j : M) (A.radius (j : M)) x) =
      normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x := by
  have hrj : A.radius (j : M) ≠ 0 := ne_of_gt (A.radius_pos (j : M))
  have hraw : denormalizedTensorHeatCoordinate cov A j
      (normalizedTensorHeatCoordinate (I := I)
        (j : M) (A.radius (j : M)) x) =
      (extChartAt I (j : M)) x := by
    unfold denormalizedTensorHeatCoordinate normalizedTensorHeatCoordinate
    rw [smul_smul, mul_inv_cancel₀ hrj, one_smul, add_sub_cancel]
  unfold normalizedSpatialTransition
  rw [hraw, (extChartAt I (j : M)).left_inv hxj.1]
  rfl

/-- Raw `j`-chart coordinates on which the `j`-to-`i` chart transition and
both preferred tangent frames are valid. -/
def pairRawCoordinateDomain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : Set E :=
  (extChartAt I (j : M)).target ∩
    (extChartAt I (j : M)).symm ⁻¹'
      ((extChartAt I (i : M)).source ∩
        ((trivializationAt E TM (i : M)).baseSet ∩
          (trivializationAt E TM (j : M)).baseSet))

/-- Normalized target coordinates on which all pairwise transition data are
geometrically defined. -/
def pairNormalizedCoordinateDomain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : Set E :=
  denormalizedTensorHeatCoordinate cov A j ⁻¹'
    pairRawCoordinateDomain cov A j i

/-- Compact normalized overlap of the target partition piece with the
buffered support of the source member.  Pairwise transitions are kept exact
on this larger set, including every point where the later source mask can be
nonzero. -/
def pairNormalizedCoordinateCore
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : Set E :=
  normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) ''
    ((A.cover.pieces j : Set M) ∩
      tsupport (A.bufferedCutoff cov i).cutoff)

theorem isOpen_pairRawCoordinateDomain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    IsOpen (pairRawCoordinateDomain cov A j i) := by
  exact (continuousOn_extChartAt_symm (I := I) (j : M)).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := I) (j : M))
    ((isOpen_extChartAt_source (I := I) (i : M)).inter
      ((trivializationAt E TM (i : M)).open_baseSet.inter
        (trivializationAt E TM (j : M)).open_baseSet))

theorem contDiff_denormalizedTensorHeatCoordinate
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j : A.cover.Index) :
    ContDiff ℝ ∞ (denormalizedTensorHeatCoordinate cov A j) := by
  exact contDiff_const.add (contDiff_id.const_smul (A.radius (j : M)))

theorem isOpen_pairNormalizedCoordinateDomain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    IsOpen (pairNormalizedCoordinateDomain cov A j i) := by
  exact (isOpen_pairRawCoordinateDomain cov A j i).preimage
    (contDiff_denormalizedTensorHeatCoordinate cov A j).continuous

theorem pairNormalizedCoordinateCore_subset_domain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    pairNormalizedCoordinateCore cov A j i ⊆
      pairNormalizedCoordinateDomain cov A j i := by
  rintro y ⟨x, hx, rfl⟩
  have hxjPatch := A.cover.pieces_subset_domain j hx.1
  have hxiPatch := (A.bufferedCutoff cov i).support_subset hx.2
  have hxjFrame := A.patch_subset_trivialization (j : M) hxjPatch
  have hxiFrame := A.patch_subset_trivialization (i : M) hxiPatch
  have hrj : A.radius (j : M) ≠ 0 := ne_of_gt (A.radius_pos (j : M))
  have hraw : denormalizedTensorHeatCoordinate cov A j
      (normalizedTensorHeatCoordinate (I := I)
        (j : M) (A.radius (j : M)) x) =
      (extChartAt I (j : M)) x := by
    unfold denormalizedTensorHeatCoordinate normalizedTensorHeatCoordinate
    rw [smul_smul, mul_inv_cancel₀ hrj, one_smul, add_sub_cancel]
  rw [pairNormalizedCoordinateDomain, Set.mem_preimage, hraw]
  refine ⟨(extChartAt I (j : M)).map_source hxjPatch.1, ?_⟩
  change (extChartAt I (j : M)).symm
      ((extChartAt I (j : M)) x) ∈
    ((extChartAt I (i : M)).source ∩
      ((trivializationAt E TM (i : M)).baseSet ∩
        (trivializationAt E TM (j : M)).baseSet))
  rw [(extChartAt I (j : M)).left_inv hxjPatch.1]
  exact ⟨hxiPatch.1, ⟨hxiFrame, hxjFrame⟩⟩

theorem isCompact_pairNormalizedCoordinateCore
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    IsCompact (pairNormalizedCoordinateCore cov A j i) := by
  let K : Set M := (A.cover.pieces j : Set M) ∩
    tsupport (A.bufferedCutoff cov i).cutoff
  have hK : IsCompact K := (A.cover.pieces j).isCompact.inter_right
    (A.bufferedCutoff cov i).compactSupport.isClosed
  have hchart : ContinuousOn (extChartAt I (j : M)) K :=
    (continuousOn_extChartAt (I := I) (j : M)).mono (fun x hx =>
      (A.cover.pieces_subset_domain j hx.1).1)
  have hnorm : ContinuousOn
      (normalizedTensorHeatCoordinate (I := I)
        (j : M) (A.radius (j : M))) K := by
    exact (hchart.sub continuousOn_const).const_smul
      (A.radius (j : M))⁻¹
  exact hK.image_of_continuousOn hnorm

/-- The normalized spatial chart transition is `C¹` throughout its
pairwise geometric domain. -/
theorem contDiffOn_normalizedSpatialTransition
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    ContDiffOn ℝ 1 (normalizedSpatialTransition cov A j i)
      (pairNormalizedCoordinateDomain cov A j i) := by
  let U := pairNormalizedCoordinateDomain cov A j i
  let V := pairRawCoordinateDomain cov A j i
  have hVU : MapsTo (denormalizedTensorHeatCoordinate cov A j) U V := by
    intro y hy
    exact hy
  have hVsource : V ⊆
      ((extChartAt I (j : M)).symm ≫ extChartAt I (i : M)).source := by
    intro z hz
    change z ∈ (extChartAt I (j : M)).target ∩
      (extChartAt I (j : M)).symm ⁻¹' (extChartAt I (i : M)).source
    refine ⟨hz.1, ?_⟩
    exact hz.2.1
  have hchange : ContDiffOn ℝ 1
      (extChartAt I (i : M) ∘ (extChartAt I (j : M)).symm) V :=
    (contDiffOn_ext_coord_change (I := I) (n := 1)
      (i : M) (j : M)).mono hVsource
  have hcomp : ContDiffOn ℝ 1
      ((extChartAt I (i : M) ∘ (extChartAt I (j : M)).symm) ∘
        denormalizedTensorHeatCoordinate cov A j) U :=
    hchange.comp
      ((contDiff_denormalizedTensorHeatCoordinate cov A j).of_le
        (by norm_num)).contDiffOn hVU
  exact ((hcomp.sub contDiffOn_const).const_smul
    (A.radius (i : M))⁻¹).congr (fun _ _ => rfl)

/-- Linear synthesis of pair-indexed tensor coordinates into the model
bilinear form used by the induced tensor-bundle trivialization. -/
def tensorPairCoordinateSynthesisL
    (b : Module.Basis (Fin d) ℝ E) : W₂ →L[ℝ] Bil₂ :=
  (matrixBilinearSynthesis b).comp
    (tensorCoordinateReconstructionEquiv d).toContinuousLinearMap

/-- Linear readout of a model bilinear form in the pair-index convention
used by the parabolic forcing spaces. -/
def tensorPairCoordinateReadoutL
    (b : Module.Basis (Fin d) ℝ E) : Bil₂ →L[ℝ] W₂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h ij => h (b ij.2) (b ij.1)
      map_add' := by
        intro h k
        funext ij
        rfl
      map_smul' := by
        intro c h
        funext ij
        rfl }

@[simp] theorem tensorPairCoordinateSynthesisL_apply_basis
    (b : Module.Basis (Fin d) ℝ E) (q : W₂) (p k : Fin d) :
    tensorPairCoordinateSynthesisL b q (b p) (b k) = q (k, p) := by
  simp [tensorPairCoordinateSynthesisL,
    matrixBilinearSynthesis_apply, matrixBilinearCLM_apply_basis]

@[simp] theorem tensorPairCoordinateReadoutL_apply
    (b : Module.Basis (Fin d) ℝ E) (h : Bil₂) (ij : Fin d × Fin d) :
    tensorPairCoordinateReadoutL b h ij = h (b ij.2) (b ij.1) := rfl

/-- Explicit evaluation formula for the induced covariant-two-tensor
trivialization. -/
theorem localTwoTensorTrivialization_apply_apply_of_mem
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet)
    (h : T₂ x) (v w : E) :
    ((localTwoTensorTrivialization (I := I) e)
        (TotalSpace.mk' _ x h)).2 v w =
      h (e.symm x v) (e.symm x w) := by
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  have hx₁ : x ∈ (localCovectorTrivialization (I := I) e).baseSet :=
    ⟨hx, hx₀⟩
  rw [localTwoTensorTrivialization,
    Bundle.Trivialization.continuousLinearMap_apply]
  change
    ((localCovectorTrivialization (I := I) e).continuousLinearMapAt ℝ x
      (h (e.symmL ℝ x v))) w = _
  rw [Bundle.Trivialization.continuousLinearMapAt_apply]
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hx₁]
  simp [localCovectorTrivialization, localRealLineTrivialization,
    Bundle.Trivialization.continuousLinearMap_apply, hx]

/-- Change the pair-indexed components of a covariant two-tensor from atlas
member `i`'s preferred frame to atlas member `j`'s preferred frame. -/
def tensorPairFrameChangeL
    (b : Module.Basis (Fin d) ℝ E) (i j : M) (x : M) : W₂ →L[ℝ] W₂ :=
  tensorPairCoordinateReadoutL b |>.comp
    (((localTwoTensorTrivialization (I := I)
        (trivializationAt E TM i)).coordChangeL ℝ
      (localTwoTensorTrivialization (I := I)
        (trivializationAt E TM j)) x : Bil₂ →L[ℝ] Bil₂).comp
      (tensorPairCoordinateSynthesisL b))

/-- Fixed continuous-linear pre/postcomposition turning an induced
bilinear-model frame change into the pair-indexed frame change. -/
def tensorPairFrameConjugationL
    (b : Module.Basis (Fin d) ℝ E) :
    (Bil₂ →L[ℝ] Bil₂) →L[ℝ] (W₂ →L[ℝ] W₂) :=
  (ContinuousLinearMap.compL ℝ W₂ Bil₂ W₂
      (tensorPairCoordinateReadoutL b)).comp
    ((ContinuousLinearMap.compL ℝ W₂ Bil₂ Bil₂).flip
      (tensorPairCoordinateSynthesisL b))

@[simp] theorem tensorPairFrameConjugationL_apply
    (b : Module.Basis (Fin d) ℝ E) (L : Bil₂ →L[ℝ] Bil₂) :
    tensorPairFrameConjugationL b L =
      (tensorPairCoordinateReadoutL b).comp
        (L.comp (tensorPairCoordinateSynthesisL b)) := rfl

/-- The pairwise frame change pulled back to normalized coordinates of the
target atlas member. -/
def normalizedTensorPairFrameChange
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (y : E) : W₂ →L[ℝ] W₂ :=
  tensorPairFrameChangeL (I := I) b (i : M) (j : M)
    ((extChartAt I (j : M)).symm
      (denormalizedTensorHeatCoordinate cov A j y))

theorem localTwoTensorTrivialization_mem_baseSet_of_mem
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) :
    x ∈ (localTwoTensorTrivialization (I := I) e).baseSet := by
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  exact ⟨hx, ⟨hx, hx₀⟩⟩

/-- The normalized frame-change field is `C¹` on the geometric pair
domain. -/
theorem contDiffOn_normalizedTensorPairFrameChange
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    ContDiffOn ℝ 1 (normalizedTensorPairFrameChange cov A j i)
      (pairNormalizedCoordinateDomain cov A j i) := by
  let U := pairNormalizedCoordinateDomain cov A j i
  let V := pairRawCoordinateDomain cov A j i
  let ei := localTwoTensorTrivialization (I := I)
    (trivializationAt E TM (i : M))
  let ej := localTwoTensorTrivialization (I := I)
    (trivializationAt E TM (j : M))
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I 1
      (extChartAt I (j : M)).symm V :=
    (contMDiffOn_extChartAt_symm (I := I) (n := 1) (j : M)).mono
      (fun _ hz => hz.1)
  have hmaps : MapsTo (extChartAt I (j : M)).symm V
      (ei.baseSet ∩ ej.baseSet) := by
    intro z hz
    exact ⟨
      localTwoTensorTrivialization_mem_baseSet_of_mem
        (I := I) (trivializationAt E TM (i : M)) hz.2.2.1,
      localTwoTensorTrivialization_mem_baseSet_of_mem
        (I := I) (trivializationAt E TM (j : M)) hz.2.2.2⟩
  have hchgM : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, Bil₂ →L[ℝ] Bil₂) 1
      (fun z => (ei.coordChangeL ℝ ej
        ((extChartAt I (j : M)).symm z) : Bil₂ →L[ℝ] Bil₂)) V :=
    (contMDiffOn_coordChangeL ei ej).comp hsymm hmaps
  have hchg : ContDiffOn ℝ 1
      (fun z => (ei.coordChangeL ℝ ej
        ((extChartAt I (j : M)).symm z) : Bil₂ →L[ℝ] Bil₂)) V :=
    contMDiffOn_iff_contDiffOn.mp hchgM
  have hVU : MapsTo (denormalizedTensorHeatCoordinate cov A j) U V := by
    intro y hy
    exact hy
  have hpull : ContDiffOn ℝ 1
      (fun y => (ei.coordChangeL ℝ ej
        ((extChartAt I (j : M)).symm
          (denormalizedTensorHeatCoordinate cov A j y)) :
            Bil₂ →L[ℝ] Bil₂)) U :=
    hchg.comp
      ((contDiff_denormalizedTensorHeatCoordinate cov A j).of_le
        (by norm_num)).contDiffOn hVU
  have hout := (tensorPairFrameConjugationL b).contDiff.comp_contDiffOn hpull
  exact hout.congr (fun _ _ => rfl)

/-- On the compact overlap, the normalized frame field is the actual
source-to-target tensor coordinate change at the manifold point. -/
theorem normalizedTensorPairFrameChange_at_normalizedCoordinate
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) {x : M}
    (hxj : x ∈ actualLocalTensorHeatPatch (I := I)
      (j : M) (A.radius (j : M))) :
    normalizedTensorPairFrameChange cov A j i
        (normalizedTensorHeatCoordinate (I := I)
          (j : M) (A.radius (j : M)) x) =
      tensorPairFrameChangeL (I := I) b (i : M) (j : M) x := by
  have hrj : A.radius (j : M) ≠ 0 := ne_of_gt (A.radius_pos (j : M))
  have hraw : denormalizedTensorHeatCoordinate cov A j
      (normalizedTensorHeatCoordinate (I := I)
        (j : M) (A.radius (j : M)) x) =
      (extChartAt I (j : M)) x := by
    unfold denormalizedTensorHeatCoordinate normalizedTensorHeatCoordinate
    rw [smul_smul, mul_inv_cancel₀ hrj, one_smul, add_sub_cancel]
  unfold normalizedTensorPairFrameChange
  rw [hraw, (extChartAt I (j : M)).left_inv hxj.1]

/-- Simultaneous bounded Lipschitz extensions of the spatial and frame
changes for one ordered pair of atlas members. -/
structure PairTransitionExtensions
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) where
  spatial : CompactCoefficientExtension E E
    (normalizedSpatialTransition cov A j i)
    (pairNormalizedCoordinateCore cov A j i)
    (pairNormalizedCoordinateDomain cov A j i)
  frame : CompactCoefficientExtension E (W₂ →L[ℝ] W₂)
    (normalizedTensorPairFrameChange cov A j i)
    (pairNormalizedCoordinateCore cov A j i)
    (pairNormalizedCoordinateDomain cov A j i)

theorem nonempty_pairTransitionExtensions
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    Nonempty (PairTransitionExtensions cov A j i) := by
  have hK := isCompact_pairNormalizedCoordinateCore cov A j i
  have hU := isOpen_pairNormalizedCoordinateDomain cov A j i
  have hKU := pairNormalizedCoordinateCore_subset_domain cov A j i
  obtain ⟨S⟩ := exists_compactCoefficientExtension_of_contDiffOn
    hK hU hKU (contDiffOn_normalizedSpatialTransition cov A j i)
  obtain ⟨F⟩ := exists_compactCoefficientExtension_of_contDiffOn
    hK hU hKU (contDiffOn_normalizedTensorPairFrameChange cov A j i)
  exact ⟨⟨S, F⟩⟩

/-- Canonical chosen pairwise extensions. -/
def pairTransitionExtensions
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : PairTransitionExtensions cov A j i :=
  Classical.choice (nonempty_pairTransitionExtensions cov A j i)

/-- Globally bounded Lipschitz spatial transition in normalized target
coordinates. -/
def extendedNormalizedSpatialTransition
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : E → E :=
  (pairTransitionExtensions cov A j i).spatial.extension

/-- Globally bounded Lipschitz pair-indexed tensor frame change. -/
def extendedNormalizedTensorPairFrameChange
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : E → (W₂ →L[ℝ] W₂) :=
  (pairTransitionExtensions cov A j i).frame.extension

theorem extendedNormalizedSpatialTransition_eq_on_buffered_overlap
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M))
    (hxiBuffer : x ∈ tsupport (A.bufferedCutoff cov i).cutoff) :
    extendedNormalizedSpatialTransition cov A j i
        (normalizedTensorHeatCoordinate (I := I)
          (j : M) (A.radius (j : M)) x) =
      normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x := by
  let y := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  have hy : y ∈ pairNormalizedCoordinateCore cov A j i :=
    ⟨x, ⟨hxj, hxiBuffer⟩, rfl⟩
  have heq := (pairTransitionExtensions cov A j i).spatial
    |>.eventuallyEq_original.self_of_nhdsSet y hy
  rw [show extendedNormalizedSpatialTransition cov A j i y =
      normalizedSpatialTransition cov A j i y by exact heq]
  exact normalizedSpatialTransition_normalizedTensorHeatCoordinate
    cov A j i (A.cover.pieces_subset_domain j hxj)

theorem extendedNormalizedSpatialTransition_eq_on_overlap
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M))
    (hxi : x ∈ (A.cover.pieces i : Set M)) :
    extendedNormalizedSpatialTransition cov A j i
        (normalizedTensorHeatCoordinate (I := I)
          (j : M) (A.radius (j : M)) x) =
      normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x :=
  extendedNormalizedSpatialTransition_eq_on_buffered_overlap cov A j i hxj
    (A.piece_subset_bufferedCutoff_tsupport cov i hxi)

theorem extendedNormalizedTensorPairFrameChange_eq_on_buffered_overlap
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M))
    (hxiBuffer : x ∈ tsupport (A.bufferedCutoff cov i).cutoff) :
    extendedNormalizedTensorPairFrameChange cov A j i
        (normalizedTensorHeatCoordinate (I := I)
          (j : M) (A.radius (j : M)) x) =
      tensorPairFrameChangeL (I := I) b (i : M) (j : M) x := by
  let y := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  have hy : y ∈ pairNormalizedCoordinateCore cov A j i :=
    ⟨x, ⟨hxj, hxiBuffer⟩, rfl⟩
  have heq := (pairTransitionExtensions cov A j i).frame
    |>.eventuallyEq_original.self_of_nhdsSet y hy
  rw [show extendedNormalizedTensorPairFrameChange cov A j i y =
      normalizedTensorPairFrameChange cov A j i y by exact heq]
  exact normalizedTensorPairFrameChange_at_normalizedCoordinate
    cov A j i (A.cover.pieces_subset_domain j hxj)

theorem extendedNormalizedTensorPairFrameChange_eq_on_overlap
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M))
    (hxi : x ∈ (A.cover.pieces i : Set M)) :
    extendedNormalizedTensorPairFrameChange cov A j i
        (normalizedTensorHeatCoordinate (I := I)
          (j : M) (A.radius (j : M)) x) =
      tensorPairFrameChangeL (I := I) b (i : M) (j : M) x :=
  extendedNormalizedTensorPairFrameChange_eq_on_buffered_overlap cov A j i hxj
    (A.piece_subset_bufferedCutoff_tsupport cov i hxi)

/-! ## A supported source mask for pairwise transport -/

/-- The source member's buffered cutoff, written in the target member's raw
preferred chart. -/
def pairBufferedCutoffChartFunction
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : E → ℝ :=
  writtenInExtChartAt I 𝓘(ℝ) (j : M)
    (A.bufferedCutoff cov i).cutoff

theorem contDiffOn_pairBufferedCutoffChartFunction
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    ContDiffOn ℝ 1 (pairBufferedCutoffChartFunction cov A j i)
      (cutoffCommutatorCoordinateDomain cov A j) := by
  apply contDiffOn_writtenInExtChartAt_of_contMDiffOn
    (I := I) (p := (j : M))
    ((A.bufferedCutoff cov i).contMDiff_three.of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contMDiffOn
  · exact Set.inter_subset_left
  · intro z hz
    exact Set.mem_univ _

/-- A globally bounded Lipschitz extension of the pairwise source mask in
raw target-chart coordinates. -/
def pairBufferedCutoffExtension
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : CompactCoefficientExtension E ℝ
      (pairBufferedCutoffChartFunction cov A j i)
      (cutoffCommutatorCoordinateCore cov A j)
      (cutoffCommutatorCoordinateDomain cov A j) :=
  Classical.choice (exists_compactCoefficientExtension_of_contDiffOn
    (isCompact_cutoffCommutatorCoordinateCore cov A j)
    (isOpen_cutoffCommutatorCoordinateDomain cov A j)
    (cutoffCommutatorCoordinateCore_subset_domain cov A j)
    (contDiffOn_pairBufferedCutoffChartFunction cov A j i))

/-- The time-independent normalized target-cylinder mask used to suppress
pair transport away from the source buffered support. -/
def normalizedPairBufferedCutoffField
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    ParabolicC0AlphaSpace E ℝ α
      (parabolicFiniteCylinder E t₀ T) :=
  let F := pairBufferedCutoffExtension cov A j i
  ParabolicC0AlphaSpace.localizedRescale
    (show 0 ≤ (1 : ℝ) by norm_num) (le_refl 0)
    F.bound_nonneg F.lipschitzBound_nonneg A.alpha_pos A.alpha_lt_one.le
    (fun _ : E => (1 : ℝ)) F.extension
    ((extChartAt I (j : M)) (j : M)) (A.radius (j : M))
    (parabolicFiniteCylinder E t₀ T)
    (fun _ => by simp) (fun _ _ => by simp)
    F.norm_le F.norm_sub_le

@[simp] theorem toFun_normalizedPairBufferedCutoffField
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (z : ℝ × E) :
    ParabolicC0AlphaSpace.toFun
        (normalizedPairBufferedCutoffField cov A j i) z =
      (pairBufferedCutoffExtension cov A j i).extension
        (denormalizedTensorHeatCoordinate cov A j z.2) := by
  simp [normalizedPairBufferedCutoffField, localizedRescale,
    denormalizedTensorHeatCoordinate]

/-- On the target partition piece, the normalized source mask is exactly
the genuine buffered cutoff evaluated at the manifold point. -/
theorem normalizedPairBufferedCutoffField_at_normalizedCoordinate
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (s : ℝ) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M)) :
    ParabolicC0AlphaSpace.toFun
        (normalizedPairBufferedCutoffField cov A j i)
        (s, normalizedTensorHeatCoordinate (I := I)
          (j : M) (A.radius (j : M)) x) =
      (A.bufferedCutoff cov i).cutoff x := by
  have hrj : A.radius (j : M) ≠ 0 := ne_of_gt (A.radius_pos (j : M))
  have hraw : denormalizedTensorHeatCoordinate cov A j
      (normalizedTensorHeatCoordinate (I := I)
        (j : M) (A.radius (j : M)) x) =
      (extChartAt I (j : M)) x := by
    unfold denormalizedTensorHeatCoordinate normalizedTensorHeatCoordinate
    rw [smul_smul, mul_inv_cancel₀ hrj, one_smul, add_sub_cancel]
  rw [toFun_normalizedPairBufferedCutoffField, hraw]
  have hzCore : (extChartAt I (j : M)) x ∈
      cutoffCommutatorCoordinateCore cov A j :=
    ⟨x, A.piece_subset_bufferedCutoff_tsupport cov j hxj, rfl⟩
  rw [(pairBufferedCutoffExtension cov A j i).eventuallyEq_original
    |>.self_of_nhdsSet _ hzCore]
  simp only [pairBufferedCutoffChartFunction, writtenInExtChartAt,
    extChartAt_model_space_eq_id, Function.comp_def, PartialEquiv.refl_coe]
  simp only [id_eq]
  rw [(extChartAt I (j : M)).left_inv
    (A.cover.pieces_subset_domain j hxj).1]

/-- Positive ratio between target and source chart radii. -/
def pairRadiusRatio
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : ℝ :=
  A.radius (j : M) / A.radius (i : M)

theorem pairRadiusRatio_pos
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : 0 < pairRadiusRatio cov A j i :=
  div_pos (A.radius_pos (j : M)) (A.radius_pos (i : M))

/-- Time-coordinate transition corresponding to the same physical time in
the normalized target and source cylinders. -/
def normalizedPairTimeTransition
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (s : ℝ) : ℝ :=
  t₀ + pairRadiusRatio cov A j i ^ 2 * (s - t₀)

theorem normalizedPairTimeTransition_normalizedTime
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (t : ℝ) :
    normalizedPairTimeTransition cov A j i
        (FiniteClassicalTensorHeatField.normalizedTime
          t₀ (A.radius (j : M)) t) =
      FiniteClassicalTensorHeatField.normalizedTime
        t₀ (A.radius (i : M)) t := by
  have hrj : A.radius (j : M) ≠ 0 := ne_of_gt (A.radius_pos (j : M))
  have hri : A.radius (i : M) ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  unfold normalizedPairTimeTransition pairRadiusRatio
    FiniteClassicalTensorHeatField.normalizedTime
  field_simp
  ring

/-- Global space-time transition used to pull a source-chart residual into
the normalized target cylinder. -/
def extendedPairSpacetimeTransition
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : ℝ × E → ℝ × E := fun z =>
  (normalizedPairTimeTransition cov A j i z.1,
    extendedNormalizedSpatialTransition cov A j i z.2)

/-- A nonnegative global parabolic Lipschitz constant for the extended
pairwise space-time transition. -/
def pairSpacetimeLipschitzBound
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : ℝ :=
  max (pairRadiusRatio cov A j i)
    (pairTransitionExtensions cov A j i).spatial.lipschitzBound

theorem pairSpacetimeLipschitzBound_nonneg
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    0 ≤ pairSpacetimeLipschitzBound cov A j i :=
  le_trans (pairRadiusRatio_pos cov A j i).le (le_max_left _ _)

theorem parabolicDistance_extendedPairSpacetimeTransition_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (p q : ℝ × E) :
    parabolicDistance
        (extendedPairSpacetimeTransition cov A j i p)
        (extendedPairSpacetimeTransition cov A j i q) ≤
      pairSpacetimeLipschitzBound cov A j i *
        parabolicDistance p q := by
  let a := pairRadiusRatio cov A j i
  let L := (pairTransitionExtensions cov A j i).spatial.lipschitzBound
  have ha0 : 0 ≤ a := (pairRadiusRatio_pos cov A j i).le
  have hL0 : 0 ≤ L :=
    (pairTransitionExtensions cov A j i).spatial.lipschitzBound_nonneg
  have htime :
      Real.sqrt
          |normalizedPairTimeTransition cov A j i p.1 -
            normalizedPairTimeTransition cov A j i q.1| =
        a * Real.sqrt |p.1 - q.1| := by
    unfold normalizedPairTimeTransition
    change Real.sqrt |t₀ + a ^ 2 * (p.1 - t₀) -
        (t₀ + a ^ 2 * (q.1 - t₀))| = _
    rw [show t₀ + a ^ 2 * (p.1 - t₀) -
        (t₀ + a ^ 2 * (q.1 - t₀)) =
        a ^ 2 * (p.1 - q.1) by ring]
    rw [abs_mul, abs_of_nonneg (sq_nonneg a),
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
      abs_of_nonneg ha0]
  unfold extendedPairSpacetimeTransition parabolicDistance
  rw [htime]
  apply max_le
  · calc
      a * Real.sqrt |p.1 - q.1| ≤
          max a L * Real.sqrt |p.1 - q.1| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ max a L * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _)
          (le_trans ha0 (le_max_left _ _))
  · calc
      dist (extendedNormalizedSpatialTransition cov A j i p.2)
          (extendedNormalizedSpatialTransition cov A j i q.2) =
          ‖extendedNormalizedSpatialTransition cov A j i p.2 -
            extendedNormalizedSpatialTransition cov A j i q.2‖ :=
        dist_eq_norm _ _
      _ ≤ L * dist p.2 q.2 :=
        (pairTransitionExtensions cov A j i).spatial.norm_sub_le _ _
      _ ≤ max a L * dist p.2 q.2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
      _ ≤ max a L * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _)
          (le_trans hL0 (le_max_right _ _))

/-- Time-independent target-cylinder coefficient field supplied by the
extended tensor-frame change. -/
def normalizedPairFrameCoefficientField
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    ParabolicC0AlphaSpace E (W₂ →L[ℝ] W₂) α
      (parabolicFiniteCylinder E t₀ T) :=
  let F := (pairTransitionExtensions cov A j i).frame
  ParabolicC0AlphaSpace.ofSpatialBoundedLipschitz
    F.bound_nonneg F.lipschitzBound_nonneg A.alpha_pos A.alpha_lt_one.le
    F.extension (parabolicFiniteCylinder E t₀ T)
    (fun x _ => F.norm_le x)
    (fun x _ y _ => F.norm_sub_le x y)

@[simp] theorem toFun_normalizedPairFrameCoefficientField
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (z : ℝ × E) :
    ParabolicC0AlphaSpace.toFun
        (normalizedPairFrameCoefficientField cov A j i) z =
      extendedNormalizedTensorPairFrameChange cov A j i z.2 := rfl

/-- Pull the `i`-th normalized cutoff residual through the global pairwise
space-time transition into the `j`-th normalized cylinder. -/
def pairResidualPullbackL
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
    (j i : A.cover.Index) :
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  (ParabolicC0AlphaBanach.precompL
    (X := E) (Y := E) (E := W₂) (α := α)
    (s := (Set.univ : Set (ℝ × E)))
    (t := parabolicFiniteCylinder E t₀ T)
    A.alpha_pos.le (pairSpacetimeLipschitzBound_nonneg cov A j i)
    (Set.mapsTo_univ _ _)
    (fun p _ q _ =>
      parabolicDistance_extendedPairSpacetimeTransition_le cov A j i p q)).comp
    ((ParabolicC0AlphaBanach.finiteSourceExtensionL
      (X := E) (E := W₂) A.time_lt A.alpha_pos).comp
      (normalizedCutoffCommutatorLocalResidualL cov A i))

/-- Transport the `i`-th cutoff residual into target chart `j`, change its
tensor frame, and multiply by `r_j²`, the factor inverted by physical source
reconstruction. -/
def pairResidualTransportL
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
    (j i : A.cover.Index) :
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  A.radius (j : M) ^ 2 •
    ((ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation W₂ W₂)
      (normalizedPairFrameCoefficientField cov A j i)).comp
        (pairResidualPullbackL cov A j i))

/-- Evaluation formula for pairwise residual transport. -/
theorem eval_pairResidualTransportL
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
    (j i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (hsource : extendedPairSpacetimeTransition cov A j i z ∈
      parabolicFiniteCylinder E t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (pairResidualTransportL cov A j i q) =
      A.radius (j : M) ^ 2 •
        extendedNormalizedTensorPairFrameChange cov A j i z.2
          (ParabolicC0AlphaBanach.evalCLM
            (extendedPairSpacetimeTransition cov A j i z) hsource
            (normalizedCutoffCommutatorLocalResidualL cov A i q)) := by
  rw [pairResidualTransportL]
  rw [ContinuousLinearMap.smul_apply, map_smul]
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    toFun_normalizedPairFrameCoefficientField, operatorEvaluation_apply]
  rw [pairResidualPullbackL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [ParabolicC0AlphaBanach.evalCLM_precompL_apply]
  rw [ParabolicC0AlphaBanach.finiteSourceExtensionL_apply]
  rw [ParabolicC0AlphaBanach.eval_finiteSourceExtension_of_mem
    A.time_lt A.alpha_pos _ _ hsource]

/-- Pairwise residual transport multiplied by the source member's buffered
cutoff.  The larger exactness cores above ensure that this mask introduces no
spurious residual outside the source partition piece. -/
def supportedPairResidualTransportL
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
    (j i : A.cover.Index) :
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  (ParabolicC0AlphaBanach.mulCoeffL
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (normalizedPairBufferedCutoffField cov A j i)).comp
      (pairResidualTransportL cov A j i)

theorem eval_supportedPairResidualTransportL
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
    (j i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (supportedPairResidualTransportL cov A j i q) =
      ParabolicC0AlphaSpace.toFun
          (normalizedPairBufferedCutoffField cov A j i) z •
        ParabolicC0AlphaBanach.evalCLM z hz
          (pairResidualTransportL cov A j i q) := by
  rw [supportedPairResidualTransportL, ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply]
  rfl

/-- The frame-change operator reads exactly the same intrinsic tensor in the
target preferred frame. -/
theorem tensorPairFrameChangeL_apply_eq
    (b : Module.Basis (Fin d) ℝ E) (i j : M) {x : M}
    (hxi : x ∈ (trivializationAt E TM i).baseSet)
    (hxj : x ∈ (trivializationAt E TM j).baseSet)
    (q : W₂) (p k : Fin d) :
    tensorPairFrameChangeL (I := I) b i j x q (k, p) =
      (localTwoTensorTrivialization (I := I)
          (trivializationAt E TM i)).symm x
          (tensorPairCoordinateSynthesisL b q)
        ((trivializationAt E TM j).localFrame b p x)
        ((trivializationAt E TM j).localFrame b k x) := by
  let ei := localTwoTensorTrivialization (I := I)
    (trivializationAt E TM i)
  let ej := localTwoTensorTrivialization (I := I)
    (trivializationAt E TM j)
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  have hxi₂ : x ∈ ei.baseSet := by
    exact ⟨hxi, ⟨hxi, hx₀⟩⟩
  have hxj₂ : x ∈ ej.baseSet := by
    exact ⟨hxj, ⟨hxj, hx₀⟩⟩
  have hover : x ∈ ei.baseSet ∩ ej.baseSet := ⟨hxi₂, hxj₂⟩
  change
    (ei.coordChangeL ℝ ej x (tensorPairCoordinateSynthesisL b q))
        (b p) (b k) = _
  rw [ei.coordChangeL_apply (R := ℝ) ej hover]
  have hframe (a : Fin d) :
      (trivializationAt E TM j).localFrame b a x =
        (trivializationAt E TM j).symm x (b a) := by
    rw [Bundle.Trivialization.localFrame]
    rw [dif_pos hxj]
    rfl
  rw [hframe p, hframe k]
  simpa [ei, ej] using
    localTwoTensorTrivialization_apply_apply_of_mem
      (I := I) (trivializationAt E TM j) hxj
      (ei.symm x (tensorPairCoordinateSynthesisL b q)) (b p) (b k)

/-- Changing pair coordinates from a preferred tensor frame to itself is
the identity. -/
theorem tensorPairFrameChangeL_self_apply
    (b : Module.Basis (Fin d) ℝ E) (i : M) {x : M}
    (hxi : x ∈ (trivializationAt E TM i).baseSet)
    (q : W₂) :
    tensorPairFrameChangeL (I := I) b i i x q = q := by
  let ei := localTwoTensorTrivialization (I := I)
    (trivializationAt E TM i)
  have hxi₂ : x ∈ ei.baseSet :=
    localTwoTensorTrivialization_mem_baseSet_of_mem
      (I := I) (trivializationAt E TM i) hxi
  have hchg : (ei.coordChangeL ℝ ei x : Bil₂ →L[ℝ] Bil₂)
      (tensorPairCoordinateSynthesisL b q) =
        tensorPairCoordinateSynthesisL b q := by
    calc
      (ei.coordChangeL ℝ ei x : Bil₂ →L[ℝ] Bil₂)
          (tensorPairCoordinateSynthesisL b q) =
          (ei ⟨x, ei.symm x (tensorPairCoordinateSynthesisL b q)⟩).2 :=
        ei.coordChangeL_apply (R := ℝ) ei ⟨hxi₂, hxi₂⟩ _
      _ = tensorPairCoordinateSynthesisL b q := congrArg Prod.snd
        (ei.apply_mk_symm hxi₂ (tensorPairCoordinateSynthesisL b q))
  ext out
  rcases out with ⟨k, p⟩
  change tensorPairCoordinateReadoutL b
      ((ei.coordChangeL ℝ ei x : Bil₂ →L[ℝ] Bil₂)
        (tensorPairCoordinateSynthesisL b q)) (k, p) = q (k, p)
  rw [hchg]
  exact tensorPairCoordinateSynthesisL_apply_basis b q p k

/-- Pair-indexed components of an intrinsic covariant two-tensor in one
preferred atlas frame. -/
def intrinsicTensorPairCoordinates
    (b : Module.Basis (Fin d) ℝ E) (j : M) (x : M)
    (h : T₂ x) : W₂ := fun out =>
  h ((trivializationAt E TM j).localFrame b out.2 x)
    ((trivializationAt E TM j).localFrame b out.1 x)

/-- Exact coordinate transport: if `q` are the source-frame components of
an intrinsic tensor, the pair frame change returns its target-frame
components. -/
theorem tensorPairFrameChangeL_eq_intrinsicTensorPairCoordinates
    (b : Module.Basis (Fin d) ℝ E) (i j : M) {x : M}
    (hxi : x ∈ (trivializationAt E TM i).baseSet)
    (hxj : x ∈ (trivializationAt E TM j).baseSet)
    (h : T₂ x) (q : W₂)
    (hq : ∀ p k, q (k, p) =
      h ((trivializationAt E TM i).localFrame b p x)
        ((trivializationAt E TM i).localFrame b k x)) :
    tensorPairFrameChangeL (I := I) b i j x q =
      intrinsicTensorPairCoordinates (I := I) b j x h := by
  let hs : T₂ x :=
    (localTwoTensorTrivialization (I := I)
      (trivializationAt E TM i)).symm x
        (tensorPairCoordinateSynthesisL b q)
  have hself := tensorPairFrameChangeL_apply_eq
    (I := I) b i i hxi hxi q
  have hhs : hs = h := by
    apply continuousBilinearMap_ext_localFrame
      (I := I) (trivializationAt E TM i) b hxi
    intro p k
    calc
      hs ((trivializationAt E TM i).localFrame b p x)
          ((trivializationAt E TM i).localFrame b k x) =
          tensorPairFrameChangeL (I := I) b i i x q (k, p) :=
        (hself p k).symm
      _ = q (k, p) := by rw [tensorPairFrameChangeL_self_apply b i hxi q]
      _ = h ((trivializationAt E TM i).localFrame b p x)
          ((trivializationAt E TM i).localFrame b k x) := hq p k
  ext out
  rcases out with ⟨k, p⟩
  rw [tensorPairFrameChangeL_apply_eq b i j hxi hxj q p k]
  exact congrArg
    (fun H : T₂ x => H
      ((trivializationAt E TM j).localFrame b p x)
      ((trivializationAt E TM j).localFrame b k x)) hhs

/-- Every chart-normalized time associated to the common physical interval
lies in the original finite normalized cylinder. -/
theorem normalizedTime_mem_Ioc_of_mem_commonInterval [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) {t : ℝ}
    (ht : t ∈ Ioo t₀ A.commonTerminalTime) :
    FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (i : M)) t ∈ Ioc t₀ T := by
  apply FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc
    (ne_of_gt (A.radius_pos (i : M)))
  exact ⟨ht.1, ht.2.le.trans (A.commonTerminalTime_le cov i)⟩

/-- At a genuine pairwise overlap and a common physical time, pairwise
transport evaluates to `r_j²` times the target-frame coordinates of the
actual intrinsic cutoff commutator. -/
theorem eval_pairResidualTransportL_at_physical_overlap [Nonempty M]
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
    (j i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    {t : ℝ} (ht : t ∈ Ioo t₀ A.commonTerminalTime) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M))
    (hxi : x ∈ (A.cover.pieces i : Set M)) :
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    ParabolicC0AlphaBanach.evalCLM (sj, yj)
        (by simpa using A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht)
        (pairResidualTransportL cov A j i q) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (connectionLaplacianCutoffCommutator cov (A.cover.partition i)
            (A.bufferedLocalSolutionSlice cov i q
              (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t)) x) := by
  dsimp only
  let sj := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (j : M)) t
  let si := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (i : M)) t
  let yj := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  let yi := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  have hsj : sj ∈ Ioc t₀ T :=
    A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
  have hsi : si ∈ Ioc t₀ T :=
    A.normalizedTime_mem_Ioc_of_mem_commonInterval cov i ht
  have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ T := by
    simpa [sj, yj] using hsj
  have hspace : extendedNormalizedSpatialTransition cov A j i yj = yi := by
    exact extendedNormalizedSpatialTransition_eq_on_overlap cov A j i hxj hxi
  have htime : normalizedPairTimeTransition cov A j i sj = si := by
    exact normalizedPairTimeTransition_normalizedTime cov A j i t
  have htransition : extendedPairSpacetimeTransition cov A j i (sj, yj) =
      (si, yi) := by
    simp [extendedPairSpacetimeTransition, htime, hspace]
  have hsource : extendedPairSpacetimeTransition cov A j i (sj, yj) ∈
      parabolicFiniteCylinder E t₀ T := by
    rw [htransition]
    simpa [si, yi] using hsi
  rw [eval_pairResidualTransportL cov A j i q (sj, yj) hzj hsource]
  rw [extendedNormalizedTensorPairFrameChange_eq_on_overlap cov A j i hxj hxi]
  apply congrArg (fun v : W₂ => A.radius (j : M) ^ 2 • v)
  let Hx : T₂ x := connectionLaplacianCutoffCommutator cov
    (A.cover.partition i) (A.bufferedLocalSolutionSlice cov i q si) x
  apply tensorPairFrameChangeL_eq_intrinsicTensorPairCoordinates
    (I := I) b (i : M) (j : M)
    (A.patch_subset_trivialization (i : M)
      (A.cover.pieces_subset_domain i hxi))
    (A.patch_subset_trivialization (j : M)
      (A.cover.pieces_subset_domain j hxj)) Hx
  intro p k
  have heval := A.eval_normalizedCutoffCommutatorLocalResidualL
    cov i q si hsi hxi p k
  simpa [htransition, si, yi, Hx] using heval

/-- The supported pair operator represents the `i`-th intrinsic commutator
in target chart `j` at every point of the target partition piece.  On the
overlap the buffer is one; off the source partition piece the intrinsic
commutator and the supported coordinate residual both vanish. -/
theorem eval_supportedPairResidualTransportL_at_physical_point [Nonempty M]
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
    (j i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    {t : ℝ} (ht : t ∈ Ioo t₀ A.commonTerminalTime) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M)) :
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    ParabolicC0AlphaBanach.evalCLM (sj, yj)
        (by simpa using A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht)
        (supportedPairResidualTransportL cov A j i q) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (connectionLaplacianCutoffCommutator cov (A.cover.partition i)
            (A.bufferedLocalSolutionSlice cov i q
              (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t)) x) := by
  dsimp only
  let sj := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (j : M)) t
  let si := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (i : M)) t
  let yj := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  let yi := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  have hsj : sj ∈ Ioc t₀ T :=
    A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
  have hsi : si ∈ Ioc t₀ T :=
    A.normalizedTime_mem_Ioc_of_mem_commonInterval cov i ht
  have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ T := by
    simpa [sj, yj] using hsj
  rw [eval_supportedPairResidualTransportL cov A j i q (sj, yj) hzj]
  rw [normalizedPairBufferedCutoffField_at_normalizedCoordinate
    cov A j i sj hxj]
  by_cases hxi : x ∈ (A.cover.pieces i : Set M)
  · rw [A.bufferedCutoff_eq_one_of_mem_piece cov i hxi, one_smul]
    exact eval_pairResidualTransportL_at_physical_overlap
      cov A j i q ht hxj hxi
  · have hcomm : connectionLaplacianCutoffCommutator cov
        (A.cover.partition i) (A.bufferedLocalSolutionSlice cov i q si) x = 0 :=
      connectionLaplacianCutoffCommutator_eq_zero_of_notMem_tsupport
        (I := I) cov b
        ((A.cover.partition i).contMDiff.of_le
          (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
        (A.contMDiff_bufferedLocalSolutionSlice cov i q hsi) hxi
    rw [show FiniteClassicalTensorHeatField.normalizedTime
        t₀ (A.radius (i : M)) t = si by rfl, hcomm]
    have hrhs : intrinsicTensorPairCoordinates (I := I) b (j : M) x
        (0 : T₂ x) = 0 := by
      rfl
    rw [hrhs, smul_zero]
    by_cases hcut : (A.bufferedCutoff cov i).cutoff x = 0
    · rw [hcut, zero_smul]
    · have hxBuffer : x ∈ tsupport (A.bufferedCutoff cov i).cutoff := by
        apply subset_closure
        exact hcut
      have hspace : extendedNormalizedSpatialTransition cov A j i yj = yi :=
        extendedNormalizedSpatialTransition_eq_on_buffered_overlap
          cov A j i hxj hxBuffer
      have htime : normalizedPairTimeTransition cov A j i sj = si :=
        normalizedPairTimeTransition_normalizedTime cov A j i t
      have htransition : extendedPairSpacetimeTransition cov A j i (sj, yj) =
          (si, yi) := by
        simp [extendedPairSpacetimeTransition, htime, hspace]
      have hsource : extendedPairSpacetimeTransition cov A j i (sj, yj) ∈
          parabolicFiniteCylinder E t₀ T := by
        rw [htransition]
        simpa [si, yi] using hsi
      rw [eval_pairResidualTransportL cov A j i q (sj, yj) hzj hsource]
      have hres0 := A.eval_normalizedCutoffCommutatorLocalResidualL_eq_zero
        cov i q si hsi hxBuffer hxi
      have hres : ParabolicC0AlphaBanach.evalCLM
          (extendedPairSpacetimeTransition cov A j i (sj, yj)) hsource
          (normalizedCutoffCommutatorLocalResidualL cov A i q) = 0 := by
        simpa only [htransition, si, yi] using hres0
      rw [hres]
      simp

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
