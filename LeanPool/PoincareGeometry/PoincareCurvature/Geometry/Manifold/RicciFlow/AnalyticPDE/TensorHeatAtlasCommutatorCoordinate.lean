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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasCutoff
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCutoffCommutator
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.CompactCoefficientExtension
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LocalizedCoefficientScaling

/-!
# Atlas coordinate coefficients for the tensor-heat cutoff commutator

For each member of the finite tensor-heat atlas, this file constructs the
actual first- and zeroth-order coefficient fields of the partition cutoff
commutator.  It proves that they are `C¹` on the full chart/frame overlap and
then extends them to globally bounded Lipschitz fields without changing them
near the compact partition piece.
-/

@[expose] public section

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
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "DW₂" => (E →L[ℝ] W₂)
local notation "D2W₂" => (E →L[ℝ] E →L[ℝ] W₂)
local notation "P₂" => (D2W₂ →L[ℝ] W₂)
local notation "B₂" => (DW₂ →L[ℝ] W₂)
local notation "C₂" => (W₂ →L[ℝ] W₂)

@[reducible] local instance atlasCommutatorScalarFirstNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCommutatorScalarFirstNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCommutatorScalarSecondNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCommutatorScalarSecondNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCommutatorScalarThirdNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance atlasCommutatorScalarThirdNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance atlasCommutatorThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance atlasCommutatorThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance atlasCommutatorThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasCommutatorThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasCommutatorThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
@[reducible] local instance atlasCommutatorFirstNormedAddCommGroup :
    NormedAddCommGroup DW₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCommutatorFirstNormedSpace :
    NormedSpace ℝ DW₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCommutatorSecondNormedAddCommGroup :
    NormedAddCommGroup D2W₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCommutatorSecondNormedSpace :
    NormedSpace ℝ D2W₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCommutatorPrincipalNormedAddCommGroup :
    NormedAddCommGroup P₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCommutatorPrincipalNormedSpace :
    NormedSpace ℝ P₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCommutatorFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup B₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCommutatorFirstCoeffNormedSpace :
    NormedSpace ℝ B₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCommutatorZeroCoeffNormedAddCommGroup :
    NormedAddCommGroup C₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCommutatorZeroCoeffNormedSpace :
    NormedSpace ℝ C₂ := ContinuousLinearMap.toNormedSpace

/-- The open model-space region where both the preferred chart and the
preferred tangent frame for atlas member `i` are valid. -/
def cutoffCommutatorCoordinateDomain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : Set E :=
  (extChartAt I (i : M)).target ∩
    (extChartAt I (i : M)).symm ⁻¹'
      (trivializationAt E TM (i : M)).baseSet

/-- The compact image of the buffered support surrounding one partition
piece.  Extending the commutator coefficients on this larger core is what
allows pairwise chart transport to be cut off without losing exactness. -/
def cutoffCommutatorCoordinateCore
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : Set E :=
  extChartAt I (i : M) ''
    tsupport (A.bufferedCutoff cov i).cutoff

/-- The `i`-th partition function transported to its preferred chart. -/
def cutoffCommutatorChartFunction
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : E → ℝ :=
  writtenInExtChartAt I 𝓘(ℝ) (i : M) (A.cover.partition i)

/-- First chart derivative of the partition function. -/
def cutoffCommutatorChartGradient
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : E → E →L[ℝ] ℝ := fun z =>
  fderivWithin ℝ (cutoffCommutatorChartFunction cov A i) (Set.range I) z

/-- Second chart derivative of the partition function. -/
def cutoffCommutatorChartHessian
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : E → E →L[ℝ] E →L[ℝ] ℝ := fun z =>
  fderivWithin ℝ (cutoffCommutatorChartGradient cov A i) (Set.range I) z

/-- Actual first-order coefficient of the `i`-th cutoff commutator in the
preferred tensor frame. -/
def cutoffCommutatorFirstCoefficient
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : E → B₂ := fun z =>
  secondOrderCutoffFirstCoefficient
    (localTensorHeatPrincipalCoefficient (I := I) (i : M)
      (trivializationAt E TM (i : M)) b z)
    (cutoffCommutatorChartGradient cov A i z)

/-- Actual zeroth-order coefficient of the `i`-th cutoff commutator in the
preferred tensor frame. -/
def cutoffCommutatorZeroCoefficient
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : E → C₂ := fun z =>
  secondOrderCutoffZeroCoefficient
    (localTensorHeatPrincipalCoefficient (I := I) (i : M)
      (trivializationAt E TM (i : M)) b z)
    (localTensorHeatFirstCoefficient (I := I) cov (i : M)
      (trivializationAt E TM (i : M)) b z)
    (cutoffCommutatorChartGradient cov A i z)
    (cutoffCommutatorChartHessian cov A i z)

theorem isOpen_cutoffCommutatorCoordinateDomain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) :
    IsOpen (cutoffCommutatorCoordinateDomain cov A i) :=
  (continuousOn_extChartAt_symm (I := I) (i : M)).isOpen_inter_preimage
    (isOpen_extChartAt_target (i : M))
    (trivializationAt E TM (i : M)).open_baseSet

theorem cutoffCommutatorCoordinateDomain_subset_range
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) :
    cutoffCommutatorCoordinateDomain cov A i ⊆ Set.range I :=
  Set.Subset.trans Set.inter_subset_left
    (extChartAt_target_subset_range (i : M))

/-- The compact partition core lies in the full chart/frame domain. -/
theorem cutoffCommutatorCoordinateCore_subset_domain
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) :
    cutoffCommutatorCoordinateCore cov A i ⊆
      cutoffCommutatorCoordinateDomain cov A i := by
  rintro z ⟨x, hx, rfl⟩
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) :=
    (A.bufferedCutoff cov i).support_subset hx
  constructor
  · exact (extChartAt I (i : M)).map_source hxPatch.1
  · change (extChartAt I (i : M)).symm
      ((extChartAt I (i : M)) x) ∈
        (trivializationAt E TM (i : M)).baseSet
    rw [(extChartAt I (i : M)).left_inv hxPatch.1]
    exact A.patch_subset_trivialization (i : M) hxPatch

theorem isCompact_cutoffCommutatorCoordinateCore
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) :
    IsCompact (cutoffCommutatorCoordinateCore cov A i) := by
  exact (A.bufferedCutoff cov i).compactSupport.image_of_continuousOn
    ((continuousOn_extChartAt (I := I) (i : M)).mono
      (fun x hx => ((A.bufferedCutoff cov i).support_subset hx).1))

/-- Away from the topological support of the partition function, both raw
coordinate coefficients of its cutoff commutator vanish. -/
theorem cutoffCommutatorCoefficients_eq_zero_of_not_mem_piece
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) {x : M}
    (hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)))
    (hx : x ∉ (A.cover.pieces i : Set M)) :
    cutoffCommutatorFirstCoefficient cov A i
          ((extChartAt I (i : M)) x) = 0 ∧
      cutoffCommutatorZeroCoefficient cov A i
          ((extChartAt I (i : M)) x) = 0 := by
  let z := (extChartAt I (i : M)) x
  let χ := cutoffCommutatorChartFunction cov A i
  have hsymm : Tendsto (extChartAt I (i : M)).symm
      (nhds z) (nhds x) := by
    have h := continuousAt_extChartAt_symm' hxPatch.1
    change Tendsto (extChartAt I (i : M)).symm
      (nhds ((extChartAt I (i : M)) x))
      (nhds ((extChartAt I (i : M)).symm
        ((extChartAt I (i : M)) x))) at h
    rw [(extChartAt I (i : M)).left_inv hxPatch.1] at h
    exact h
  have hg0 : (A.cover.partition i : M → ℝ) =ᶠ[nhds x] 0 := by
    exact notMem_tsupport_iff_eventuallyEq.mp hx
  have hpull :
      (fun w => (A.cover.partition i)
        ((extChartAt I (i : M)).symm w)) =ᶠ[nhds z] 0 := by
    exact hsymm.eventually hg0
  have hχ0 : χ =ᶠ[nhds z] 0 := by
    simpa [χ, cutoffCommutatorChartFunction, writtenInExtChartAt,
      extChartAt_model_space_eq_id, Function.comp_def, PartialEquiv.refl_coe,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      OpenPartialHomeomorph.coe_toPartialEquiv] using hpull
  have hzTarget : z ∈ (extChartAt I (i : M)).target :=
    (extChartAt I (i : M)).map_source hxPatch.1
  have hrange : Set.range I ∈ nhds z :=
    mem_of_superset
      ((isOpen_extChartAt_target (i : M)).mem_nhds hzTarget)
      (extChartAt_target_subset_range (i : M))
  have hdχ : cutoffCommutatorChartGradient cov A i z = 0 := by
    unfold cutoffCommutatorChartGradient
    rw [show cutoffCommutatorChartFunction cov A i = χ by rfl]
    rw [fderivWithin_of_mem_nhds hrange]
    rw [hχ0.fderiv_eq]
    simp
  have hdχev : cutoffCommutatorChartGradient cov A i =ᶠ[nhds z] 0 := by
    have htarget : (extChartAt I (i : M)).target ∈ nhds z :=
      (isOpen_extChartAt_target (i : M)).mem_nhds hzTarget
    have hdf := hχ0.fderiv (𝕜 := ℝ)
    filter_upwards [htarget, hdf] with w hw hfw
    unfold cutoffCommutatorChartGradient
    rw [fderivWithin_of_mem_nhds
      (mem_of_superset
        ((isOpen_extChartAt_target (i : M)).mem_nhds hw)
        (extChartAt_target_subset_range (i : M)))]
    rw [show fderiv ℝ (cutoffCommutatorChartFunction cov A i) w = 0 by
      simpa [χ] using hfw]
    rfl
  have hddχ : cutoffCommutatorChartHessian cov A i z = 0 := by
    unfold cutoffCommutatorChartHessian
    rw [fderivWithin_of_mem_nhds hrange]
    rw [hdχev.fderiv_eq]
    simp
  constructor
  · change secondOrderCutoffFirstCoefficient
      (localTensorHeatPrincipalCoefficient (I := I) (i : M)
        (trivializationAt E TM (i : M)) b z)
      (cutoffCommutatorChartGradient cov A i z) = 0
    rw [hdχ]
    ext Du out
    simp [secondOrderCutoffFirstCoefficient, cutoffGradientCrossL]
  · change secondOrderCutoffZeroCoefficient
      (localTensorHeatPrincipalCoefficient (I := I) (i : M)
        (trivializationAt E TM (i : M)) b z)
      (localTensorHeatFirstCoefficient (I := I) cov (i : M)
        (trivializationAt E TM (i : M)) b z)
      (cutoffCommutatorChartGradient cov A i z)
      (cutoffCommutatorChartHessian cov A i z) = 0
    rw [hdχ, hddχ]
    ext u out
    simp [secondOrderCutoffZeroCoefficient, cutoffHessianValueL,
      cutoffGradientValueL]

/-- Both genuine cutoff-commutator coefficient fields are `C¹` on the
preferred coordinate domain. -/
theorem contDiffOn_cutoffCommutatorCoefficients
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
    (i : A.cover.Index) :
    ContDiffOn ℝ 1 (cutoffCommutatorFirstCoefficient cov A i)
        (cutoffCommutatorCoordinateDomain cov A i) ∧
      ContDiffOn ℝ 1 (cutoffCommutatorZeroCoefficient cov A i)
        (cutoffCommutatorCoordinateDomain cov A i) := by
  let U := cutoffCommutatorCoordinateDomain cov A i
  have hU : IsOpen U := isOpen_cutoffCommutatorCoordinateDomain cov A i
  have hUr : U ⊆ Set.range I :=
    cutoffCommutatorCoordinateDomain_subset_range cov A i
  have hχ : ContDiffOn ℝ 3 (cutoffCommutatorChartFunction cov A i) U := by
    apply CovariantDerivative.contDiffOn_writtenInExtChartAt_of_contMDiffOn
      (I := I) (p := (i : M))
      ((A.cover.partition i).contMDiff.of_le
        (show (3 : WithTop ℕ∞) ≤ ∞ by decide)).contMDiffOn
    · exact Set.inter_subset_left
    · intro z hz
      exact Set.mem_univ _
  have hdχ : ContDiffOn ℝ 2 (cutoffCommutatorChartGradient cov A i) U := by
    exact CovariantDerivative.contDiffOn_fderivWithin_range_succ
      (I := I) hU hUr hχ
  have hddχ : ContDiffOn ℝ 1 (cutoffCommutatorChartHessian cov A i) U := by
    exact CovariantDerivative.contDiffOn_fderivWithin_range_succ
      (I := I) hU hUr hdχ
  obtain ⟨hP, hB, _hC⟩ :=
    contDiffOn_actualTensorHeatCoefficients
      (I := I) cov (i : M) (trivializationAt E TM (i : M)) b
  constructor
  · exact contDiffOn_secondOrderCutoffFirstCoefficient hP
      (hdχ.of_le (by norm_num))
  · exact contDiffOn_secondOrderCutoffZeroCoefficient hP hB
      (hdχ.of_le (by norm_num)) hddχ

/-- Chosen globally bounded Lipschitz extensions of the two genuine
commutator coefficients, fixed simultaneously for one atlas member. -/
structure CutoffCommutatorCoefficientExtensions
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) where
  first : CompactCoefficientExtension E B₂
    (cutoffCommutatorFirstCoefficient cov A i)
    (cutoffCommutatorCoordinateCore cov A i)
    (cutoffCommutatorCoordinateDomain cov A i)
  zero : CompactCoefficientExtension E C₂
    (cutoffCommutatorZeroCoefficient cov A i)
    (cutoffCommutatorCoordinateCore cov A i)
    (cutoffCommutatorCoordinateDomain cov A i)

/-- Every atlas member has simultaneous global bounded Lipschitz extensions
of its actual cutoff-commutator coefficients. -/
theorem nonempty_cutoffCommutatorCoefficientExtensions
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
    (i : A.cover.Index) :
    Nonempty (CutoffCommutatorCoefficientExtensions cov A i) := by
  have hK := isCompact_cutoffCommutatorCoordinateCore cov A i
  have hU := isOpen_cutoffCommutatorCoordinateDomain cov A i
  have hKU := cutoffCommutatorCoordinateCore_subset_domain cov A i
  obtain ⟨hfirst, hzero⟩ := contDiffOn_cutoffCommutatorCoefficients cov A i
  obtain ⟨G⟩ := exists_compactCoefficientExtension_of_contDiffOn
    hK hU hKU hfirst
  obtain ⟨D⟩ := exists_compactCoefficientExtension_of_contDiffOn
    hK hU hKU hzero
  exact ⟨⟨G, D⟩⟩

/-- Canonical choice of the extended commutator coefficients. -/
def cutoffCommutatorCoefficientExtensions
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
    (i : A.cover.Index) : CutoffCommutatorCoefficientExtensions cov A i :=
  Classical.choice (nonempty_cutoffCommutatorCoefficientExtensions cov A i)

/-- Globally defined first-order coefficient selected by the compact
extension construction. -/
def extendedCutoffCommutatorFirstCoefficient
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
    (i : A.cover.Index) : E → B₂ :=
  (cutoffCommutatorCoefficientExtensions cov A i).first.extension

/-- Globally defined zeroth-order coefficient selected by the compact
extension construction. -/
def extendedCutoffCommutatorZeroCoefficient
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
    (i : A.cover.Index) : E → C₂ :=
  (cutoffCommutatorCoefficientExtensions cov A i).zero.extension

/-- The first-order commutator coefficient in normalized coordinates.  Its
inverse-radius factor converts the normalized solution gradient to the raw
preferred-chart gradient. -/
def normalizedCutoffCommutatorFirstCoefficient
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
    (i : A.cover.Index) (y : E) : B₂ :=
  (A.radius (i : M))⁻¹ •
    extendedCutoffCommutatorFirstCoefficient cov A i
      ((extChartAt I (i : M)) (i : M) + A.radius (i : M) • y)

/-- The zeroth-order commutator coefficient in normalized coordinates. -/
def normalizedCutoffCommutatorZeroCoefficient
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
    (i : A.cover.Index) (y : E) : C₂ :=
  extendedCutoffCommutatorZeroCoefficient cov A i
    ((extChartAt I (i : M)) (i : M) + A.radius (i : M) • y)

/-- The normalized first-order coefficient as a finite-cylinder parabolic
Hölder field. -/
def normalizedCutoffCommutatorFirstField
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
    (i : A.cover.Index) :
    FiniteFirstCoefficientSpace (X := E) (W := W₂)
      (t₀ := t₀) (T := T) (α := α) :=
  let G := (cutoffCommutatorCoefficientExtensions cov A i).first
  ParabolicC0AlphaSpace.localizedRescale
    (abs_nonneg (A.radius (i : M))⁻¹) (le_refl 0)
    G.bound_nonneg G.lipschitzBound_nonneg A.alpha_pos A.alpha_lt_one.le
    (fun _ : E => (A.radius (i : M))⁻¹) G.extension
    ((extChartAt I (i : M)) (i : M)) (A.radius (i : M))
    (parabolicFiniteCylinder E t₀ T)
    (fun _ => le_rfl) (fun _ _ => by simp)
    G.norm_le G.norm_sub_le

/-- The normalized zeroth-order coefficient as a finite-cylinder parabolic
Hölder field. -/
def normalizedCutoffCommutatorZeroField
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
    (i : A.cover.Index) :
    FiniteZeroCoefficientSpace (X := E) (W := W₂)
      (t₀ := t₀) (T := T) (α := α) :=
  let D := (cutoffCommutatorCoefficientExtensions cov A i).zero
  ParabolicC0AlphaSpace.localizedRescale
    (show 0 ≤ (1 : ℝ) by norm_num) (le_refl 0)
    D.bound_nonneg D.lipschitzBound_nonneg A.alpha_pos A.alpha_lt_one.le
    (fun _ : E => (1 : ℝ)) D.extension
    ((extChartAt I (i : M)) (i : M)) (A.radius (i : M))
    (parabolicFiniteCylinder E t₀ T)
    (fun _ => by simp) (fun _ _ => by simp)
    D.norm_le D.norm_sub_le

@[simp] theorem toFun_normalizedCutoffCommutatorFirstField
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
    (i : A.cover.Index) (z : ℝ × E) :
    ParabolicC0AlphaSpace.toFun
        (normalizedCutoffCommutatorFirstField cov A i) z =
      normalizedCutoffCommutatorFirstCoefficient cov A i z.2 := by
  simp [normalizedCutoffCommutatorFirstField,
    normalizedCutoffCommutatorFirstCoefficient,
    extendedCutoffCommutatorFirstCoefficient, localizedRescale]

@[simp] theorem toFun_normalizedCutoffCommutatorZeroField
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
    (i : A.cover.Index) (z : ℝ × E) :
    ParabolicC0AlphaSpace.toFun
        (normalizedCutoffCommutatorZeroField cov A i) z =
      normalizedCutoffCommutatorZeroCoefficient cov A i z.2 := by
  simp [normalizedCutoffCommutatorZeroField,
    normalizedCutoffCommutatorZeroCoefficient,
    extendedCutoffCommutatorZeroCoefficient, localizedRescale]

/-- On the compact partition core, the chosen extensions realize the
coordinate coefficients of the genuine intrinsic cutoff commutator. -/
theorem connectionLaplacianCutoffCommutator_apply_eq_extendedCoefficients
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
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    connectionLaplacianCutoffCommutator cov (A.cover.partition i)
        (A.bufferedLocalSolutionSlice cov i q s) x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      (extendedCutoffCommutatorFirstCoefficient cov A i
          ((extChartAt I (i : M)) x)
          (finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
            (FiniteParabolicC2AlphaBanach.spaceDeriv
              (A.localInverse (i : M) q)
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x))) +
        extendedCutoffCommutatorZeroCoefficient cov A i
          ((extChartAt I (i : M)) x)
          (FiniteParabolicC2AlphaBanach.value
            (A.localInverse (i : M) q)
            (s, normalizedTensorHeatCoordinate (I := I)
              (i : M) (A.radius (i : M)) x))) (k, p) := by
  let z : E := (extChartAt I (i : M)) x
  let h := A.bufferedLocalSolutionSlice cov i q s
  let u := FiniteParabolicC2AlphaBanach.value
    (A.localInverse (i : M) q)
    (s, normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x)
  let Du := finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
    (FiniteParabolicC2AlphaBanach.spaceDeriv
      (A.localInverse (i : M) q)
      (s, normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x))
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) := A.cover.pieces_subset_domain i hx
  have hcoord :=
    connectionLaplacianCutoffCommutator_apply_eq_secondOrderCutoff
      (I := I) cov (i : M) (trivializationAt E TM (i : M)) b
      ((A.cover.partition i).contMDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
      (A.contMDiff_bufferedLocalSolutionSlice cov i q hs)
      (A.patch_subset_trivialization (i : M) hxPatch) hxPatch.1 p k
  have hDu := (A.localTensorCoordinateDerivatives_buffered
    cov i q s hs hx).1
  have hu : localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b h z = u := by
    have hev := A.localTensorCoordinates_buffered_eventuallyEq_normalized
      cov i q s hs hx
    have hv := hev.self_of_nhds
    simpa [h, z, u, normalizedTensorHeatCoordinate] using hv
  have hzCore : z ∈ cutoffCommutatorCoordinateCore cov A i :=
    ⟨x, A.piece_subset_bufferedCutoff_tsupport cov i hx, rfl⟩
  have hG := (cutoffCommutatorCoefficientExtensions cov A i).first
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  have hD := (cutoffCommutatorCoefficientExtensions cov A i).zero
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  rw [hcoord]
  change
    (cutoffCommutatorFirstCoefficient cov A i z
          (localTensorCoordinateDerivative (I := I) (i : M)
            (trivializationAt E TM (i : M)) b h z) +
      cutoffCommutatorZeroCoefficient cov A i z
          (localTensorCoordinates (I := I) (i : M)
            (trivializationAt E TM (i : M)) b h z)) (k, p) = _
  rw [hDu, hu]
  change (cutoffCommutatorFirstCoefficient cov A i z Du +
      cutoffCommutatorZeroCoefficient cov A i z u) (k, p) = _
  rw [← hG, ← hD]
  rfl

/-- The genuine cutoff commutator, expressed as a bounded lower-order
operator on the normalized local solution produced by atlas member `i`. -/
def normalizedCutoffCommutatorLocalResidualL
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
    (i : A.cover.Index) :
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  (FiniteParabolicC2AlphaBanach.lowerOrderL
    (normalizedCutoffCommutatorFirstField cov A i)
    (normalizedCutoffCommutatorZeroField cov A i)).comp
      (A.localInverse (i : M))

/-- Pointwise identification of the normalized bounded lower-order operator
with the actual intrinsic cutoff commutator on the compact partition piece. -/
theorem eval_normalizedCutoffCommutatorLocalResidualL
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
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs)
        (normalizedCutoffCommutatorLocalResidualL cov A i q) (k, p) =
      connectionLaplacianCutoffCommutator cov (A.cover.partition i)
        (A.bufferedLocalSolutionSlice cov i q s) x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) := by
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  have hz : (s, ξ) ∈ parabolicFiniteCylinder E t₀ T := by
    simpa [ξ] using hs
  have hraw : (extChartAt I (i : M)) (i : M) +
      A.radius (i : M) • ξ = (extChartAt I (i : M)) x := by
    dsimp [ξ, normalizedTensorHeatCoordinate]
    rw [smul_smul,
      mul_inv_cancel₀ (ne_of_gt (A.radius_pos (i : M))),
      one_smul, add_sub_cancel]
  have hgeom :=
    connectionLaplacianCutoffCommutator_apply_eq_extendedCoefficients
      cov A i q s hs hx p k
  rw [show normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x = ξ by rfl] at hgeom
  rw [hgeom]
  rw [normalizedCutoffCommutatorLocalResidualL,
    ContinuousLinearMap.comp_apply,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL]
  simp only [toFun_normalizedCutoffCommutatorFirstField,
    toFun_normalizedCutoffCommutatorZeroField]
  change
    (normalizedCutoffCommutatorFirstCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.spaceDeriv
            (A.localInverse (i : M) q) (s, ξ)) +
      normalizedCutoffCommutatorZeroCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.value
            (A.localInverse (i : M) q) (s, ξ))) (k, p) = _
  rw [normalizedCutoffCommutatorFirstCoefficient,
    normalizedCutoffCommutatorZeroCoefficient, hraw]
  have hscale : finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
      (FiniteParabolicC2AlphaBanach.spaceDeriv
        (A.localInverse (i : M) q) (s, ξ)) =
      (A.radius (i : M))⁻¹ •
        FiniteParabolicC2AlphaBanach.spaceDeriv
          (A.localInverse (i : M) q) (s, ξ) := by
    ext v out
    simp [finiteAffineFirstDerivativeL_apply]
  rw [hscale, map_smul]
  rfl

/-- On the buffered support but outside the partition piece, the normalized
local commutator residual is exactly zero. -/
theorem eval_normalizedCutoffCommutatorLocalResidualL_eq_zero
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
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hxBuffer : x ∈ tsupport (A.bufferedCutoff cov i).cutoff)
    (hx : x ∉ (A.cover.pieces i : Set M)) :
    ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs)
        (normalizedCutoffCommutatorLocalResidualL cov A i q) = 0 := by
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  let z : E := (extChartAt I (i : M)) x
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) :=
    (A.bufferedCutoff cov i).support_subset hxBuffer
  have hraw : (extChartAt I (i : M)) (i : M) +
      A.radius (i : M) • ξ = z := by
    dsimp [ξ, z, normalizedTensorHeatCoordinate]
    rw [smul_smul,
      mul_inv_cancel₀ (ne_of_gt (A.radius_pos (i : M))),
      one_smul, add_sub_cancel]
  have hzCore : z ∈ cutoffCommutatorCoordinateCore cov A i :=
    ⟨x, hxBuffer, rfl⟩
  have hG := (cutoffCommutatorCoefficientExtensions cov A i).first
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  have hD := (cutoffCommutatorCoefficientExtensions cov A i).zero
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  have hzero := cutoffCommutatorCoefficients_eq_zero_of_not_mem_piece
    cov A i hxPatch hx
  rw [normalizedCutoffCommutatorLocalResidualL,
    ContinuousLinearMap.comp_apply,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL]
  simp only [toFun_normalizedCutoffCommutatorFirstField,
    toFun_normalizedCutoffCommutatorZeroField]
  change
    normalizedCutoffCommutatorFirstCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.spaceDeriv
            (A.localInverse (i : M) q) (s, ξ)) +
      normalizedCutoffCommutatorZeroCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.value
            (A.localInverse (i : M) q) (s, ξ)) = 0
  rw [normalizedCutoffCommutatorFirstCoefficient,
    normalizedCutoffCommutatorZeroCoefficient, hraw]
  change
    ((A.radius (i : M))⁻¹ •
        (cutoffCommutatorCoefficientExtensions cov A i).first.extension z)
          (FiniteParabolicC2AlphaBanach.spaceDeriv
            (A.localInverse (i : M) q) (s, ξ)) +
      (cutoffCommutatorCoefficientExtensions cov A i).zero.extension z
          (FiniteParabolicC2AlphaBanach.value
            (A.localInverse (i : M) q) (s, ξ)) = 0
  rw [hG, hD, hzero.1, hzero.2]
  simp

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
