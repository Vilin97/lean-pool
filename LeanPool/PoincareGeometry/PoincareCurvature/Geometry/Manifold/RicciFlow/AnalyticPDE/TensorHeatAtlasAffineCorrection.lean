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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasInitial
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasShortContraction

/-! # Arbitrary-trace correction for the tensor-heat atlas -/

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

@[reducible] local instance affineFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup DW₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance affineFirstDerivativeNormedSpace :
    NormedSpace ℝ DW₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance affineSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup D2W₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance affineSecondDerivativeNormedSpace :
    NormedSpace ℝ D2W₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance affineScalarThirdNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance affineScalarThirdNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance affineThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance affineThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance affineThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance affineThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance affineThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- An arbitrary normalized higher coefficient field, extended to a global
tensor slice by the buffered cutoff. -/
def bufferedLocalHigherSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) : ∀ x : M, T₂ x :=
  cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM (i : M)) b
    (A.bufferedCutoff cov i).cutoff
    (normalizedTensorHeatCoefficientSlice (I := I)
      (i : M) (A.radius (i : M)) (normalizedHigherSolution u) s)

/-- Positive-time buffered slices of an arbitrary higher atlas member are
globally twice continuously differentiable. -/
theorem contMDiff_bufferedLocalHigherSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    {s : ℝ} (hs : s ∈ Ioc t₀ T) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (bufferedLocalHigherSlice cov A i u s x)) := by
  apply contMDiff_cutoffLocalTensorOfMatrix_of_coefficients_of_isOpen
    (I := I) (i : M) (trivializationAt E TM (i : M)) b
    (A.bufferedCutoff cov i).cutoff
    (normalizedTensorHeatCoefficientSlice (I := I)
      (i : M) (A.radius (i : M)) (normalizedHigherSolution u) s)
    (isOpen_actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)))
    (A.patch_subset_trivialization (i : M))
  · exact (A.bufferedCutoff cov i).contMDiff_three.of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  · exact (A.bufferedCutoff cov i).support_subset
  · exact contMDiffOn_normalizedTensorHeatCoefficientSlice
      (I := I) (i : M) (A.radius (i : M))
      (normalizedHigherSolution u) A.alpha_pos hs

/-- Reading an uncut arbitrary higher reconstruction in its preferred frame
recovers the original pair-indexed coefficient value. -/
theorem localTensorCoordinates_normalizedHigher_reconstruction
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M))) :
    localTensorCoordinates (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (localTensorOfMatrix (I := I) (trivializationAt E TM (i : M)) b
          (normalizedTensorHeatCoefficientSlice (I := I)
            (i : M) (A.radius (i : M)) (normalizedHigherSolution u) s))
        ((extChartAt I (i : M)) x) =
      FiniteParabolicC2AlphaBanach.value u
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x) := by
  funext out
  rcases out with ⟨a, c⟩
  have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
    A.patch_subset_trivialization (i : M) hx
  have hz : (s, normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x) ∈
      parabolicFiniteCylinder E t₀ T := by simpa using hs
  simp [localTensorCoordinates, localTwoTensorComponentInChart,
    writtenInExtChartAt]
  simp_all only [mfld_simps, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  rw [localTwoTensorComponent_apply_of_mem
    (I := I) (trivializationAt E TM (i : M)) b _ hxFrame]
  rw [localTensorOfMatrix_localFrame
    (I := I) (trivializationAt E TM (i : M)) b _ hxFrame]
  unfold normalizedTensorHeatCoefficientSlice normalizedHigherSolution
  rw [FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ _ hz]
  rfl

/-- Near a partition piece, the buffered arbitrary higher field has the
same preferred-chart coefficients as its normalized Banach element. -/
theorem localTensorCoordinates_bufferedHigher_eventuallyEq_normalized
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) :
    localTensorCoordinates (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (bufferedLocalHigherSlice cov A i u s) =ᶠ[nhds
          ((extChartAt I (i : M)) x)]
      (fun z => FiniteParabolicC2AlphaBanach.value u
        (s, (A.radius (i : M))⁻¹ •
          (z - (extChartAt I (i : M)) (i : M)))) := by
  have hxPatch := A.cover.pieces_subset_domain i hx
  have hzTarget : (extChartAt I (i : M)) x ∈
      (extChartAt I (i : M)).target :=
    (extChartAt I (i : M)).map_source hxPatch.1
  have hsymm : Tendsto (extChartAt I (i : M)).symm
      (nhds ((extChartAt I (i : M)) x)) (nhds x) := by
    have h := continuousAt_extChartAt_symm' hxPatch.1
    change Tendsto (extChartAt I (i : M)).symm
      (nhds ((extChartAt I (i : M)) x))
      (nhds ((extChartAt I (i : M)).symm
        ((extChartAt I (i : M)) x))) at h
    rwa [(extChartAt I (i : M)).left_inv hxPatch.1] at h
  have hχx : ∀ᶠ y in nhds x, (A.bufferedCutoff cov i).cutoff y = 1 :=
    (A.bufferedCutoff cov i).one_nhds.filter_mono (nhds_le_nhdsSet hx)
  have hχz : ∀ᶠ z in nhds ((extChartAt I (i : M)) x),
      (A.bufferedCutoff cov i).cutoff
        ((extChartAt I (i : M)).symm z) = 1 := hsymm.eventually hχx
  have hpatchz : ∀ᶠ z in nhds ((extChartAt I (i : M)) x),
      (extChartAt I (i : M)).symm z ∈
        actualLocalTensorHeatPatch (I := I)
          (i : M) (A.radius (i : M)) :=
    hsymm.eventually
      ((isOpen_actualLocalTensorHeatPatch (I := I)
        (i : M) (A.radius (i : M))).mem_nhds hxPatch)
  have htarget : ∀ᶠ z in nhds ((extChartAt I (i : M)) x),
      z ∈ (extChartAt I (i : M)).target :=
    (isOpen_extChartAt_target (I := I) (i : M)).mem_nhds hzTarget
  filter_upwards [hχz, hpatchz, htarget] with z hχ hzPatch hzTarget'
  have hbase := localTensorCoordinates_normalizedHigher_reconstruction
    cov A i u s hs hzPatch
  have hleft : (extChartAt I (i : M))
      ((extChartAt I (i : M)).symm z) = z :=
    (extChartAt I (i : M)).right_inv hzTarget'
  change localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b
      (bufferedLocalHigherSlice cov A i u s) z = _
  rw [hleft] at hbase
  have hbase' : localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b
      (localTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M)) (normalizedHigherSolution u) s)) z =
      FiniteParabolicC2AlphaBanach.value u
        (s, (A.radius (i : M))⁻¹ •
          (z - (extChartAt I (i : M)) (i : M))) := by
    have hnorm : normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M))
        ((extChartAt I (i : M)).symm z) =
        (A.radius (i : M))⁻¹ •
          (z - (extChartAt I (i : M)) (i : M)) := by
      unfold normalizedTensorHeatCoordinate
      rw [hleft]
    rwa [hnorm] at hbase
  rw [← hbase']
  have hfield : bufferedLocalHigherSlice cov A i u s
      ((extChartAt I (i : M)).symm z) =
      localTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M)) (normalizedHigherSolution u) s)
        ((extChartAt I (i : M)).symm z) := by
    unfold bufferedLocalHigherSlice cutoffLocalTensorOfMatrix
    rw [hχ, one_smul]
  funext out
  simp [localTensorCoordinates, localTwoTensorComponentInChart,
    writtenInExtChartAt]
  simp_all only [mfld_simps, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  unfold localTwoTensorComponent
  rw [hfield]

/-- The first and second preferred-chart derivatives of an arbitrary
buffered higher member carry the expected inverse-radius factors. -/
theorem localTensorCoordinateDerivatives_bufferedHigher
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) :
    localTensorCoordinateDerivative (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (bufferedLocalHigherSlice cov A i u s)
        ((extChartAt I (i : M)) x) =
      finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
        (FiniteParabolicC2AlphaBanach.spaceDeriv u
          (s, normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) x)) ∧
    localTensorCoordinateSecondDerivative (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (bufferedLocalHigherSlice cov A i u s)
        ((extChartAt I (i : M)) x) =
      finiteAffineSecondDerivativeL (A.radius (i : M))⁻¹
        (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u
          (s, normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) x)) := by
  let z₀ : E := (extChartAt I (i : M)) x
  let c : E := (extChartAt I (i : M)) (i : M)
  let r : ℝ := A.radius (i : M)
  let F : E → W₂ := localTensorCoordinates (I := I) (i : M)
    (trivializationAt E TM (i : M)) b
    (bufferedLocalHigherSlice cov A i u s)
  let G : E → W₂ := fun z =>
    FiniteParabolicC2AlphaBanach.value u (s, r⁻¹ • (z - c))
  let L : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  let K := (ContinuousLinearMap.compL ℝ E E W₂).flip L
  have hxPatch := A.cover.pieces_subset_domain i hx
  have hzTarget : z₀ ∈ (extChartAt I (i : M)).target :=
    (extChartAt I (i : M)).map_source hxPatch.1
  have hzRange : Set.range I ∈ nhds z₀ :=
    mem_of_superset
      ((isOpen_extChartAt_target (I := I) (i : M)).mem_nhds hzTarget)
      (extChartAt_target_subset_range (I := I) (i : M))
  have hFG : F =ᶠ[nhds z₀] G := by
    simpa [F, G, z₀, c, r] using
      localTensorCoordinates_bufferedHigher_eventuallyEq_normalized
        cov A i u s hs hx
  have hG (z : E) : HasFDerivAt G
      ((FiniteParabolicC2AlphaBanach.spaceDeriv u
        (s, r⁻¹ • (z - c))).comp L) z := by
    simpa only [G, L] using
      FiniteParabolicC2AlphaBanach.hasFDerivAt_spatialInvAffineValue
        u hs c r z
  have hJ (z : E) : HasFDerivAt
      (fun y : E => K (FiniteParabolicC2AlphaBanach.spaceDeriv u
        (s, r⁻¹ • (y - c))))
      (K.comp ((FiniteParabolicC2AlphaBanach.spaceSecondDeriv u
        (s, r⁻¹ • (z - c))).comp L)) z := by
    simpa only [K, L] using
      FiniteParabolicC2AlphaBanach.hasFDerivAt_spatialInvAffineSpaceDeriv
        u hs c r z
  have hfirstFG : fderivWithin ℝ F (Set.range I) z₀ =
      fderivWithin ℝ G (Set.range I) z₀ :=
    hFG.fderivWithin_eq_of_nhds
  have hfirstG : fderivWithin ℝ G (Set.range I) z₀ =
      (FiniteParabolicC2AlphaBanach.spaceDeriv u
        (s, r⁻¹ • (z₀ - c))).comp L := by
    rw [fderivWithin_of_mem_nhds hzRange, (hG z₀).fderiv]
  have hfirst : fderivWithin ℝ F (Set.range I) z₀ =
      (FiniteParabolicC2AlphaBanach.spaceDeriv u
        (s, r⁻¹ • (z₀ - c))).comp L := hfirstFG.trans hfirstG
  have hDFG : fderivWithin ℝ F (Set.range I) =ᶠ[
      nhdsWithin z₀ (Set.range I)]
      fderivWithin ℝ G (Set.range I) :=
    (hFG.filter_mono nhdsWithin_le_nhds).fderivWithin
  have hsecondFG : fderivWithin ℝ
      (fderivWithin ℝ F (Set.range I)) (Set.range I) z₀ =
      fderivWithin ℝ
        (fderivWithin ℝ G (Set.range I)) (Set.range I) z₀ :=
    hDFG.fderivWithin_eq hfirstFG
  have htarget : ∀ᶠ z in nhds z₀,
      z ∈ (extChartAt I (i : M)).target :=
    (isOpen_extChartAt_target (I := I) (i : M)).mem_nhds hzTarget
  have hDG : fderivWithin ℝ G (Set.range I) =ᶠ[nhds z₀]
      (fun z => K (FiniteParabolicC2AlphaBanach.spaceDeriv u
        (s, r⁻¹ • (z - c)))) := by
    filter_upwards [htarget] with z hz
    have hrange : Set.range I ∈ nhds z :=
      mem_of_superset
        ((isOpen_extChartAt_target (I := I) (i : M)).mem_nhds hz)
        (extChartAt_target_subset_range (I := I) (i : M))
    rw [fderivWithin_of_mem_nhds hrange, (hG z).fderiv]
    rfl
  have hsecondG : fderivWithin ℝ
      (fderivWithin ℝ G (Set.range I)) (Set.range I) z₀ =
      K.comp ((FiniteParabolicC2AlphaBanach.spaceSecondDeriv u
        (s, r⁻¹ • (z₀ - c))).comp L) := by
    rw [hDG.fderivWithin_eq_of_nhds]
    rw [fderivWithin_of_mem_nhds hzRange, (hJ z₀).fderiv]
  constructor
  · change fderivWithin ℝ F (Set.range I) z₀ = _
    rw [hfirst]
    ext v out
    simp [L, z₀, c, r, normalizedTensorHeatCoordinate,
      finiteAffineFirstDerivativeL_apply]
  · change fderivWithin ℝ (fderivWithin ℝ F (Set.range I))
      (Set.range I) z₀ = _
    rw [hsecondFG.trans hsecondG]
    ext v w out
    simp [K, L, z₀, c, r, normalizedTensorHeatCoordinate,
      finiteAffineSecondDerivativeL_apply, pow_two, smul_smul]

/-- The intrinsic Laplacian of a buffered arbitrary higher member is the
normalized coordinate second-order operator after multiplication by `r²`. -/
theorem radius_sq_mul_connectionLaplacian_bufferedHigher_apply
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    A.radius (i : M) ^ 2 *
        connectionLaplacian cov (bufferedLocalHigherSlice cov A i u s) x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) =
      (localTensorHeatPrincipalCoefficient (I := I) (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) x)
            (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x)) +
        A.radius (i : M) •
          localTensorHeatFirstCoefficient (I := I) cov (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) x)
            (FiniteParabolicC2AlphaBanach.spaceDeriv u
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x)) +
        A.radius (i : M) ^ 2 •
          localTensorHeatZeroCoefficient (I := I) cov (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) x)
            (FiniteParabolicC2AlphaBanach.value u
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x))) (k, p) := by
  let h := bufferedLocalHigherSlice cov A i u s
  let z : E := (extChartAt I (i : M)) x
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  let U := FiniteParabolicC2AlphaBanach.value u (s, ξ)
  let D₁ := FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ)
  let D₂ := FiniteParabolicC2AlphaBanach.spaceSecondDeriv u (s, ξ)
  have hxPatch := A.cover.pieces_subset_domain i hx
  have hbridge :=
    connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_contMDiff_two
      (I := I) cov (i : M) (trivializationAt E TM (i : M)) b
      (contMDiff_bufferedLocalHigherSlice cov A i u hs)
      (A.patch_subset_trivialization (i : M) hxPatch) hxPatch.1 p k
  have hderiv := localTensorCoordinateDerivatives_bufferedHigher
    cov A i u s hs hx
  have hvalue : localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b h z = U := by
    have hv := (localTensorCoordinates_bufferedHigher_eventuallyEq_normalized
      cov A i u s hs hx).self_of_nhds
    simpa [h, z, ξ, U, normalizedTensorHeatCoordinate] using hv
  have hD₁scale : finiteAffineFirstDerivativeL
      (A.radius (i : M))⁻¹ D₁ = (A.radius (i : M))⁻¹ • D₁ := by
    ext v out
    simp [finiteAffineFirstDerivativeL_apply]
  have hD₂scale : finiteAffineSecondDerivativeL
      (A.radius (i : M))⁻¹ D₂ =
        (A.radius (i : M))⁻¹ ^ 2 • D₂ := by
    ext v w out
    simp [finiteAffineSecondDerivativeL_apply]
  change A.radius (i : M) ^ 2 *
      connectionLaplacian cov h x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) = _
  rw [hbridge, hderiv.1, hderiv.2, hvalue]
  change A.radius (i : M) ^ 2 *
      (localTensorHeatPrincipalCoefficient (I := I) (i : M)
          (trivializationAt E TM (i : M)) b z
          (finiteAffineSecondDerivativeL (A.radius (i : M))⁻¹ D₂) +
        localTensorHeatFirstCoefficient (I := I) cov (i : M)
          (trivializationAt E TM (i : M)) b z
          (finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹ D₁) +
        localTensorHeatZeroCoefficient (I := I) cov (i : M)
          (trivializationAt E TM (i : M)) b z U) (k, p) = _
  rw [hD₁scale, hD₂scale]
  have hr : A.radius (i : M) ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  let P : W₂ := localTensorHeatPrincipalCoefficient (I := I) (i : M)
    (trivializationAt E TM (i : M)) b z D₂
  let F : W₂ := localTensorHeatFirstCoefficient (I := I) cov (i : M)
    (trivializationAt E TM (i : M)) b z D₁
  let Z : W₂ := localTensorHeatZeroCoefficient (I := I) cov (i : M)
    (trivializationAt E TM (i : M)) b z U
  have hscale :
      A.radius (i : M) ^ 2 •
          ((A.radius (i : M))⁻¹ ^ 2 • P +
            (A.radius (i : M))⁻¹ • F + Z) =
        P + A.radius (i : M) • F + A.radius (i : M) ^ 2 • Z := by
    ext kp
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp [hr]
  simpa only [map_smul, P, F, Z, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using
    congrArg (fun v : W₂ => v (k, p)) hscale

/-- The normalized reconstructed time derivative of an arbitrary higher
member is its stored parabolic time derivative. -/
theorem normalizedTensorHeatTimeDerivative_bufferedHigher_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    normalizedTensorHeatTimeDerivative (I := I) (i : M)
        (A.radius (i : M)) b (A.bufferedCutoff cov i).cutoff
        (normalizedHigherSolution u) s x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      FiniteParabolicC2AlphaBanach.timeDeriv u
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x) (k, p) := by
  have hxPatch := A.cover.pieces_subset_domain i hx
  have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
    A.patch_subset_trivialization (i : M) hxPatch
  have hz : (s, normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x) ∈
      parabolicFiniteCylinder E t₀ T := by simpa using hs
  rw [normalizedTensorHeatTimeDerivative,
    cutoffLocalTensorOfMatrix_localFrame
      (I := I) (trivializationAt E TM (i : M)) b _ _ hxFrame]
  rw [A.bufferedCutoff_eq_one_of_mem_piece cov i hx, one_mul]
  unfold normalizedHigherSolution
  simp only [FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL _ _ _ hz]
  rfl

/-- The partition-cutoff reconstruction of an arbitrary higher member equals
the partition function times its buffered reconstruction. -/
theorem cutoffLocalHigherSummand_eq_partition_smul_buffered
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) (s : ℝ) :
    cutoffLocalTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b (A.cover.partition i)
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M)) (normalizedHigherSolution u) s) =
      (fun x => A.cover.partition i x •
        bufferedLocalHigherSlice cov A i u s x) := by
  funext x
  by_cases hψ : A.cover.partition i x = 0
  · simp only [cutoffLocalTensorOfMatrix]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [_root_.smul_apply, smul_eq_mul]
    simp [hψ]
  · have hxPiece : x ∈ (A.cover.pieces i : Set M) :=
      subset_closure (by simpa [Function.mem_support] using hψ)
    have hχ := A.bufferedCutoff_eq_one_of_mem_piece cov i hxPiece
    simp [cutoffLocalTensorOfMatrix, bufferedLocalHigherSlice, hχ]

/-- Leibniz decomposition of the partitioned arbitrary higher summand. -/
theorem connectionLaplacian_cutoffLocalHigherSummand_eq_buffered_add_commutator
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    {s : ℝ} (hs : s ∈ Ioc t₀ T) (x : M) :
    connectionLaplacian cov
        (cutoffLocalTensorOfMatrix (I := I)
          (trivializationAt E TM (i : M)) b (A.cover.partition i)
          (normalizedTensorHeatCoefficientSlice (I := I)
            (i : M) (A.radius (i : M)) (normalizedHigherSolution u) s)) x =
      A.cover.partition i x •
          connectionLaplacian cov (bufferedLocalHigherSlice cov A i u s) x +
        connectionLaplacianCutoffCommutator cov (A.cover.partition i)
          (bufferedLocalHigherSlice cov A i u s) x := by
  rw [cutoffLocalHigherSummand_eq_partition_smul_buffered cov A i u s]
  exact connectionLaplacian_smul_function_of_contMDiff_two cov
    ((A.cover.partition i).contMDiff.of_le
      (by decide : (2 : WithTop ℕ∞) ≤ ∞))
    (contMDiff_bufferedLocalHigherSlice cov A i u hs) x

/-- Every arbitrary higher member satisfies, tautologically, the coordinate
equation whose right-hand side is its Cauchy image.  On the unit ball those
stored coefficients are the actual connection-Laplacian coefficients. -/
theorem normalizedHigherEquation_on_unitBall
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (hzBall : z.2 ∈ Metric.closedBall (0 : E) 1) :
    FiniteParabolicC2AlphaBanach.timeDeriv u z -
        (localTensorHeatPrincipalCoefficient (I := I) (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) (i : M) +
              A.radius (i : M) • z.2)
            (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u z) +
          A.radius (i : M) •
            localTensorHeatFirstCoefficient (I := I) cov (i : M)
              (trivializationAt E TM (i : M)) b
              ((extChartAt I (i : M)) (i : M) +
                A.radius (i : M) • z.2)
              (FiniteParabolicC2AlphaBanach.spaceDeriv u z) +
          A.radius (i : M) ^ 2 •
            localTensorHeatZeroCoefficient (I := I) cov (i : M)
              (trivializationAt E TM (i : M)) b
              ((extChartAt I (i : M)) (i : M) +
                A.radius (i : M) • z.2)
              (FiniteParabolicC2AlphaBanach.value u z)) =
      ParabolicC0AlphaBanach.evalCLM z hz
        (localCoordinateCauchyL cov A i u) := by
  obtain ⟨_hzDomain, hA, hB, hC⟩ := A.fields_agree (i : M) z hzBall
  rw [localCoordinateCauchyL,
    FiniteParabolicC2AlphaBanach.evalCLM_coordinateCauchyL]
  rw [hA, hB, hC]
  simp only [smul_apply]

/-- The normalized residual of a partitioned arbitrary higher atlas member is
its partitioned coordinate Cauchy image minus the exact cutoff commutator. -/
theorem normalized_cutoffLocalHigherSummand_residual_apply
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) (x : M) (p k : Fin d) :
    let e := trivializationAt E TM (i : M)
    let U := normalizedHigherSolution u
    let cutoffField := cutoffLocalTensorOfMatrix (I := I) e b
      (A.cover.partition i)
      (normalizedTensorHeatCoefficientSlice (I := I)
        (i : M) (A.radius (i : M)) U s)
    (normalizedTensorHeatTimeDerivative (I := I) (i : M)
          (A.radius (i : M)) b (A.cover.partition i) U s x -
        A.radius (i : M) ^ 2 • connectionLaplacian cov cutoffField x)
        (e.localFrame b p x) (e.localFrame b k x) =
      A.cover.partition i x *
          ParabolicC0AlphaBanach.representative
            (localCoordinateCauchyL cov A i u)
            (s, normalizedTensorHeatCoordinate (I := I)
              (i : M) (A.radius (i : M)) x) (k, p) -
        A.radius (i : M) ^ 2 *
          connectionLaplacianCutoffCommutator cov
            (A.cover.partition i) (bufferedLocalHigherSlice cov A i u s) x
            (e.localFrame b p x) (e.localFrame b k x) := by
  dsimp only
  have hlap := connectionLaplacian_cutoffLocalHigherSummand_eq_buffered_add_commutator
    cov A i u hs x
  rw [hlap]
  simp only [sub_apply, smul_apply, smul_eq_mul, add_apply]
  by_cases hψ : A.cover.partition i x = 0
  · simp [normalizedTensorHeatTimeDerivative,
      cutoffLocalTensorOfMatrix, hψ]
  · have hxPiece : x ∈ (A.cover.pieces i : Set M) :=
      subset_closure (by simpa [Function.mem_support] using hψ)
    have hxPatch := A.cover.pieces_subset_domain i hxPiece
    have hξ : normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x ∈
        Metric.closedBall (0 : E) 1 :=
      inv_smul_sub_mem_closedBall_one_of_mem_ball
        (A.radius_pos (i : M)) hxPatch.2
    have hz : (s, normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x) ∈
        parabolicFiniteCylinder E t₀ T := by simpa using hs
    have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
      A.patch_subset_trivialization (i : M) hxPatch
    have htime :
        normalizedTensorHeatTimeDerivative (I := I) (i : M)
            (A.radius (i : M)) b (A.cover.partition i)
            (normalizedHigherSolution u) s x
            ((trivializationAt E TM (i : M)).localFrame b p x)
            ((trivializationAt E TM (i : M)).localFrame b k x) =
          A.cover.partition i x *
            FiniteParabolicC2AlphaBanach.timeDeriv u
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x) (k, p) := by
      rw [normalizedTensorHeatTimeDerivative,
        cutoffLocalTensorOfMatrix_localFrame
          (I := I) (trivializationAt E TM (i : M)) b _ _ hxFrame]
      unfold normalizedHigherSolution
      simp only [FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL _ _ _ hz]
      rfl
    have hlap' := radius_sq_mul_connectionLaplacian_bufferedHigher_apply
      cov A i u s hs hxPiece p k
    have heq := normalizedHigherEquation_on_unitBall cov A i u
      (s, normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x) hz hξ
    have hphysical : (extChartAt I (i : M)) (i : M) +
        A.radius (i : M) • normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x = (extChartAt I (i : M)) x := by
      unfold normalizedTensorHeatCoordinate
      rw [smul_smul,
        mul_inv_cancel₀ (ne_of_gt (A.radius_pos (i : M))),
        one_smul, add_sub_cancel]
    rw [hphysical] at heq
    have hcomponent := congrArg (fun v : W₂ => v (k, p)) heq
    simp only [Pi.sub_apply] at hcomponent
    have heq' :
        FiniteParabolicC2AlphaBanach.timeDeriv u
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x) (k, p) -
            A.radius (i : M) ^ 2 *
              connectionLaplacian cov
                (bufferedLocalHigherSlice cov A i u s) x
                ((trivializationAt E TM (i : M)).localFrame b p x)
                ((trivializationAt E TM (i : M)).localFrame b k x) =
          ParabolicC0AlphaBanach.representative
            (localCoordinateCauchyL cov A i u)
            (s, normalizedTensorHeatCoordinate (I := I)
              (i : M) (A.radius (i : M)) x) (k, p) := by
      rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
        (localCoordinateCauchyL cov A i u) _ hz]
      rw [hlap']
      exact hcomponent
    rw [htime]
    linear_combination (A.cover.partition i x) * heq'

/-- The actual physical tensor-heat residual of one arbitrary higher atlas
summand is its rescaled coordinate Cauchy image minus its cutoff commutator. -/
theorem localFieldOfHigher_tensorHeatOperator_apply
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
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) (p k : Fin d) :
    (localFieldOfHigher cov A i u).tensorHeatOperator cov t ht x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      (A.radius (i : M))⁻¹ ^ 2 * A.cover.partition i x *
          ParabolicC0AlphaBanach.representative
            (localCoordinateCauchyL cov A i u)
            (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t,
              normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x) (k, p) -
        connectionLaplacianCutoffCommutator cov
            (A.cover.partition i)
            (bufferedLocalHigherSlice cov A i u
              (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t)) x
            ((trivializationAt E TM (i : M)).localFrame b p x)
            ((trivializationAt E TM (i : M)).localFrame b k x) := by
  let r : ℝ := A.radius (i : M)
  let s : ℝ := FiniteClassicalTensorHeatField.normalizedTime t₀ r t
  have hr : r ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  have htPhysical : t ∈ Ioc t₀
      (FiniteClassicalTensorHeatField.physicalTerminalTime t₀ T r) :=
    ⟨ht.1, ht.2.le.trans (A.commonTerminalTime_le cov i)⟩
  have hs : s ∈ Ioc t₀ T :=
    FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc hr htPhysical
  have hnormalized := normalized_cutoffLocalHigherSummand_residual_apply
    cov A i u s hs x p k
  dsimp only at hnormalized
  simp only [sub_apply, smul_apply, smul_eq_mul] at hnormalized
  change r⁻¹ ^ 2 *
        normalizedTensorHeatTimeDerivative (I := I) (i : M) r b
          (A.cover.partition i) (normalizedHigherSolution u) s x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) -
      connectionLaplacian cov
          (cutoffLocalTensorOfMatrix (I := I)
            (trivializationAt E TM (i : M)) b (A.cover.partition i)
            (normalizedTensorHeatCoefficientSlice (I := I)
              (i : M) r (normalizedHigherSolution u) s)) x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) = _
  calc
    _ = r⁻¹ ^ 2 *
        (normalizedTensorHeatTimeDerivative (I := I) (i : M) r b
            (A.cover.partition i) (normalizedHigherSolution u) s x
            ((trivializationAt E TM (i : M)).localFrame b p x)
            ((trivializationAt E TM (i : M)).localFrame b k x) -
          r ^ 2 *
            connectionLaplacian cov
              (cutoffLocalTensorOfMatrix (I := I)
                (trivializationAt E TM (i : M)) b (A.cover.partition i)
                (normalizedTensorHeatCoefficientSlice (I := I)
                  (i : M) r (normalizedHigherSolution u) s)) x
              ((trivializationAt E TM (i : M)).localFrame b p x)
              ((trivializationAt E TM (i : M)).localFrame b k x)) := by
          field_simp [hr]
    _ = r⁻¹ ^ 2 *
        (A.cover.partition i x *
            ParabolicC0AlphaBanach.representative
              (localCoordinateCauchyL cov A i u)
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) r x) (k, p) -
          r ^ 2 *
            connectionLaplacianCutoffCommutator cov
              (A.cover.partition i) (bufferedLocalHigherSlice cov A i u s) x
              ((trivializationAt E TM (i : M)).localFrame b p x)
              ((trivializationAt E TM (i : M)).localFrame b k x)) := by
          dsimp only [r]
          rw [hnormalized]
    _ = _ := by
      dsimp only [r, s]
      field_simp [ne_of_gt (A.radius_pos (i : M))]

/-- Intrinsic residual identity for one arbitrary higher atlas summand. -/
theorem localFieldOfHigher_tensorHeatOperator_eq_source_sub_commutator
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
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    (localFieldOfHigher cov A i u).tensorHeatOperator cov t ht x =
      A.physicalLocalSourceSlice cov i (localCoordinateCauchyL cov A i u) t x -
        connectionLaplacianCutoffCommutator cov (A.cover.partition i)
          (bufferedLocalHigherSlice cov A i u
            (FiniteClassicalTensorHeatField.normalizedTime
              t₀ (A.radius (i : M)) t)) x := by
  let r : ℝ := A.radius (i : M)
  let s : ℝ := FiniteClassicalTensorHeatField.normalizedTime t₀ r t
  have hr : r ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  have hs : s ∈ Ioc t₀ T :=
    FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc hr
      ⟨ht.1, ht.2.le.trans (A.commonTerminalTime_le cov i)⟩
  by_cases hpsi : A.cover.partition i x = 0
  · have hlap :=
      connectionLaplacian_cutoffLocalHigherSummand_eq_buffered_add_commutator
        cov A i u hs x
    change r⁻¹ ^ 2 •
          normalizedTensorHeatTimeDerivative (I := I) (i : M) r b
            (A.cover.partition i) (normalizedHigherSolution u) s x -
        connectionLaplacian cov
          (cutoffLocalTensorOfMatrix (I := I)
            (trivializationAt E TM (i : M)) b (A.cover.partition i)
            (normalizedTensorHeatCoefficientSlice (I := I)
              (i : M) r (normalizedHigherSolution u) s)) x =
      A.physicalLocalSourceSlice cov i
          (localCoordinateCauchyL cov A i u) t x -
        connectionLaplacianCutoffCommutator cov
          (A.cover.partition i) (bufferedLocalHigherSlice cov A i u s) x
    dsimp only [r, s] at hlap ⊢
    rw [hlap]
    simp [physicalLocalSourceSlice, normalizedTensorHeatTimeDerivative,
      cutoffLocalTensorOfMatrix, hpsi]
    ext v w
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
      zero_mul, mul_zero, zero_sub, zero_add]
  · have hxPiece : x ∈ (A.cover.pieces i : Set M) :=
      subset_closure (by simpa [Function.mem_support] using hpsi)
    have hxPatch := A.cover.pieces_subset_domain i hxPiece
    have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
      A.patch_subset_trivialization (i : M) hxPatch
    apply continuousBilinearMap_ext_localFrame
      (I := I) (trivializationAt E TM (i : M)) b hxFrame
    intro p k
    simp only [sub_apply]
    rw [localFieldOfHigher_tensorHeatOperator_apply
      cov A i u t ht x p k]
    rw [A.physicalLocalSourceSlice_localFrame cov i
      (localCoordinateCauchyL cov A i u) t hxFrame p k]
    ring

/-- The intrinsic cutoff commutator of an arbitrary higher atlas member is
the canonical extended first-plus-zero order coefficient expression. -/
theorem connectionLaplacianCutoffCommutator_higher_apply_eq_extendedCoefficients
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    connectionLaplacianCutoffCommutator cov (A.cover.partition i)
        (bufferedLocalHigherSlice cov A i u s) x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      (extendedCutoffCommutatorFirstCoefficient cov A i
          ((extChartAt I (i : M)) x)
          (finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
            (FiniteParabolicC2AlphaBanach.spaceDeriv u
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x))) +
        extendedCutoffCommutatorZeroCoefficient cov A i
          ((extChartAt I (i : M)) x)
          (FiniteParabolicC2AlphaBanach.value u
            (s, normalizedTensorHeatCoordinate (I := I)
              (i : M) (A.radius (i : M)) x))) (k, p) := by
  let z : E := (extChartAt I (i : M)) x
  let h := bufferedLocalHigherSlice cov A i u s
  let U := FiniteParabolicC2AlphaBanach.value u
    (s, normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x)
  let Du := finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
    (FiniteParabolicC2AlphaBanach.spaceDeriv u
      (s, normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x))
  have hxPatch := A.cover.pieces_subset_domain i hx
  have hcoord :=
    connectionLaplacianCutoffCommutator_apply_eq_secondOrderCutoff
      (I := I) cov (i : M) (trivializationAt E TM (i : M)) b
      ((A.cover.partition i).contMDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
      (contMDiff_bufferedLocalHigherSlice cov A i u hs)
      (A.patch_subset_trivialization (i : M) hxPatch) hxPatch.1 p k
  have hDu := (localTensorCoordinateDerivatives_bufferedHigher
    cov A i u s hs hx).1
  have hu : localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b h z = U := by
    have hev := localTensorCoordinates_bufferedHigher_eventuallyEq_normalized
      cov A i u s hs hx
    have hv := hev.self_of_nhds
    simpa [h, z, U, normalizedTensorHeatCoordinate] using hv
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
      cutoffCommutatorZeroCoefficient cov A i z U) (k, p) = _
  rw [← hG, ← hD]
  rfl

/-- The bounded normalized commutator operator acting directly on an
arbitrary higher coefficient field. -/
def higherCutoffCommutatorResidualL
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
    FiniteParabolicC2AlphaBanach E W₂ t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  FiniteParabolicC2AlphaBanach.lowerOrderL
    (normalizedCutoffCommutatorFirstField cov A i)
    (normalizedCutoffCommutatorZeroField cov A i)

/-- On a partition piece the higher residual is exactly the intrinsic
cutoff commutator. -/
theorem eval_higherCutoffCommutatorResidualL
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs)
        (higherCutoffCommutatorResidualL cov A i u) (k, p) =
      connectionLaplacianCutoffCommutator cov (A.cover.partition i)
        (bufferedLocalHigherSlice cov A i u s) x
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
    connectionLaplacianCutoffCommutator_higher_apply_eq_extendedCoefficients
      cov A i u s hs hx p k
  rw [show normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x = ξ by rfl] at hgeom
  rw [hgeom]
  rw [higherCutoffCommutatorResidualL,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL]
  simp only [toFun_normalizedCutoffCommutatorFirstField,
    toFun_normalizedCutoffCommutatorZeroField]
  change
    (normalizedCutoffCommutatorFirstCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ)) +
      normalizedCutoffCommutatorZeroCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.value u (s, ξ))) (k, p) = _
  rw [normalizedCutoffCommutatorFirstCoefficient,
    normalizedCutoffCommutatorZeroCoefficient, hraw]
  have hscale : finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
      (FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ)) =
      (A.radius (i : M))⁻¹ •
        FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ) := by
    ext v out
    simp [finiteAffineFirstDerivativeL_apply]
  rw [hscale, map_smul]
  rfl

/-- On the buffered support outside the partition piece, the arbitrary
higher residual vanishes exactly. -/
theorem eval_higherCutoffCommutatorResidualL_eq_zero
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hxBuffer : x ∈ tsupport (A.bufferedCutoff cov i).cutoff)
    (hx : x ∉ (A.cover.pieces i : Set M)) :
    ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs)
        (higherCutoffCommutatorResidualL cov A i u) = 0 := by
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
  rw [higherCutoffCommutatorResidualL,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL]
  simp only [toFun_normalizedCutoffCommutatorFirstField,
    toFun_normalizedCutoffCommutatorZeroField]
  change
    normalizedCutoffCommutatorFirstCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ)) +
      normalizedCutoffCommutatorZeroCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.value u (s, ξ)) = 0
  rw [normalizedCutoffCommutatorFirstCoefficient,
    normalizedCutoffCommutatorZeroCoefficient, hraw]
  change
    ((A.radius (i : M))⁻¹ •
        (cutoffCommutatorCoefficientExtensions cov A i).first.extension z)
          (FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ)) +
      (cutoffCommutatorCoefficientExtensions cov A i).zero.extension z
          (FiniteParabolicC2AlphaBanach.value u (s, ξ)) = 0
  rw [hG, hD, hzero.1, hzero.2]
  simp

/-- Pull the commutator residual of an arbitrary higher coefficient through
the global pairwise spacetime transition. -/
def higherPairResidualPullbackL
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
    FiniteParabolicC2AlphaBanach E W₂ t₀ T α →L[ℝ]
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
      (higherCutoffCommutatorResidualL cov A i))

/-- Transport an arbitrary higher coefficient's `i`-th residual into target
chart `j`, change tensor frames, and insert the physical `r_j²` scale. -/
def higherPairResidualTransportL
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
    FiniteParabolicC2AlphaBanach E W₂ t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  A.radius (j : M) ^ 2 •
    ((ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation W₂ W₂)
      (normalizedPairFrameCoefficientField cov A j i)).comp
        (higherPairResidualPullbackL cov A j i))

theorem eval_higherPairResidualTransportL
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (hsource : extendedPairSpacetimeTransition cov A j i z ∈
      parabolicFiniteCylinder E t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (higherPairResidualTransportL cov A j i u) =
      A.radius (j : M) ^ 2 •
        extendedNormalizedTensorPairFrameChange cov A j i z.2
          (ParabolicC0AlphaBanach.evalCLM
            (extendedPairSpacetimeTransition cov A j i z) hsource
            (higherCutoffCommutatorResidualL cov A i u)) := by
  rw [higherPairResidualTransportL]
  rw [smul_apply, map_smul]
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    toFun_normalizedPairFrameCoefficientField, operatorEvaluation_apply]
  rw [higherPairResidualPullbackL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [ParabolicC0AlphaBanach.evalCLM_precompL_apply]
  rw [ParabolicC0AlphaBanach.finiteSourceExtensionL_apply]
  rw [ParabolicC0AlphaBanach.eval_finiteSourceExtension_of_mem
    A.time_lt A.alpha_pos _ _ hsource]

/-- Mask the transported residual by the source member's buffered cutoff. -/
def higherSupportedPairResidualTransportL
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
    FiniteParabolicC2AlphaBanach E W₂ t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  (ParabolicC0AlphaBanach.mulCoeffL
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (normalizedPairBufferedCutoffField cov A j i)).comp
      (higherPairResidualTransportL cov A j i)

theorem eval_higherSupportedPairResidualTransportL
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (higherSupportedPairResidualTransportL cov A j i u) =
      ParabolicC0AlphaSpace.toFun
          (normalizedPairBufferedCutoffField cov A j i) z •
        ParabolicC0AlphaBanach.evalCLM z hz
          (higherPairResidualTransportL cov A j i u) := by
  rw [higherSupportedPairResidualTransportL,
    ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply]
  rfl

/-- On a genuine chart overlap, higher residual transport is exactly the
intrinsic cutoff commutator in the target frame. -/
theorem eval_higherPairResidualTransportL_at_physical_overlap [Nonempty M]
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    {t : ℝ} (ht : t ∈ Ioo t₀ A.commonTerminalTime) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M))
    (hxi : x ∈ (A.cover.pieces i : Set M)) :
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    ParabolicC0AlphaBanach.evalCLM (sj, yj)
        (by simpa using A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht)
        (higherPairResidualTransportL cov A j i u) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (connectionLaplacianCutoffCommutator cov (A.cover.partition i)
            (bufferedLocalHigherSlice cov A i u
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
  have hspace : extendedNormalizedSpatialTransition cov A j i yj = yi :=
    extendedNormalizedSpatialTransition_eq_on_overlap cov A j i hxj hxi
  have htime : normalizedPairTimeTransition cov A j i sj = si :=
    normalizedPairTimeTransition_normalizedTime cov A j i t
  have htransition : extendedPairSpacetimeTransition cov A j i (sj, yj) =
      (si, yi) := by
    simp [extendedPairSpacetimeTransition, htime, hspace]
  have hsource : extendedPairSpacetimeTransition cov A j i (sj, yj) ∈
      parabolicFiniteCylinder E t₀ T := by
    rw [htransition]
    simpa [si, yi] using hsi
  rw [eval_higherPairResidualTransportL cov A j i u
    (sj, yj) hzj hsource]
  rw [extendedNormalizedTensorPairFrameChange_eq_on_overlap cov A j i hxj hxi]
  apply congrArg (fun v : W₂ => A.radius (j : M) ^ 2 • v)
  let Hx : T₂ x := connectionLaplacianCutoffCommutator cov
    (A.cover.partition i) (bufferedLocalHigherSlice cov A i u si) x
  apply tensorPairFrameChangeL_eq_intrinsicTensorPairCoordinates
    (I := I) b (i : M) (j : M)
    (A.patch_subset_trivialization (i : M)
      (A.cover.pieces_subset_domain i hxi))
    (A.patch_subset_trivialization (j : M)
      (A.cover.pieces_subset_domain j hxj)) Hx
  intro p k
  have heval := eval_higherCutoffCommutatorResidualL
    cov A i u si hsi hxi p k
  simpa [htransition, si, yi, Hx] using heval

/-- The supported higher pair operator represents the source chart's
intrinsic commutator at every point of the target partition piece. -/
theorem eval_higherSupportedPairResidualTransportL_at_physical_point
    [Nonempty M]
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
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    {t : ℝ} (ht : t ∈ Ioo t₀ A.commonTerminalTime) {x : M}
    (hxj : x ∈ (A.cover.pieces j : Set M)) :
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    ParabolicC0AlphaBanach.evalCLM (sj, yj)
        (by simpa using A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht)
        (higherSupportedPairResidualTransportL cov A j i u) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (connectionLaplacianCutoffCommutator cov (A.cover.partition i)
            (bufferedLocalHigherSlice cov A i u
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
  rw [eval_higherSupportedPairResidualTransportL cov A j i u
    (sj, yj) hzj]
  rw [normalizedPairBufferedCutoffField_at_normalizedCoordinate
    cov A j i sj hxj]
  by_cases hxi : x ∈ (A.cover.pieces i : Set M)
  · rw [A.bufferedCutoff_eq_one_of_mem_piece cov i hxi, one_smul]
    exact eval_higherPairResidualTransportL_at_physical_overlap
      cov A j i u ht hxj hxi
  · have hcomm : connectionLaplacianCutoffCommutator cov
        (A.cover.partition i) (bufferedLocalHigherSlice cov A i u si) x = 0 :=
      connectionLaplacianCutoffCommutator_eq_zero_of_notMem_tsupport
        (I := I) cov b
        ((A.cover.partition i).contMDiff.of_le
          (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
        (contMDiff_bufferedLocalHigherSlice cov A i u hsi) hxi
    rw [show FiniteClassicalTensorHeatField.normalizedTime
        t₀ (A.radius (i : M)) t = si by rfl, hcomm]
    have hrhs : intrinsicTensorPairCoordinates (I := I) b (j : M) x
        (0 : T₂ x) = 0 := by rfl
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
      rw [eval_higherPairResidualTransportL cov A j i u
        (sj, yj) hzj hsource]
      have hres0 := eval_higherCutoffCommutatorResidualL_eq_zero
        cov A i u si hsi hxBuffer hxi
      have hres : ParabolicC0AlphaBanach.evalCLM
          (extendedPairSpacetimeTransition cov A j i (sj, yj)) hsource
          (higherCutoffCommutatorResidualL cov A i u) = 0 := by
        simpa only [htransition, si, yi] using hres0
      rw [hres]
      simp

/-- The intrinsic commutator sum of an arbitrary higher atlas family. -/
def higherAtlasCommutatorSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (t : ℝ) (x : M) : T₂ x :=
  ∑ i : A.cover.Index,
    connectionLaplacianCutoffCommutator cov (A.cover.partition i)
      (bufferedLocalHigherSlice cov A i (u i)
        (FiniteClassicalTensorHeatField.normalizedTime
          t₀ (A.radius (i : M)) t)) x

/-- Assemble every transported arbitrary-higher commutator into one source
family. -/
def higherAtlasCommutatorLiftL
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
    HigherCoefficientSpace cov A →L[ℝ] SourceSpace cov A :=
  ContinuousLinearMap.pi fun j =>
    ∑ i : A.cover.Index,
      (higherSupportedPairResidualTransportL cov A j i).comp
        (ContinuousLinearMap.proj i)

@[simp] theorem higherAtlasCommutatorLiftL_apply
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
    (u : HigherCoefficientSpace cov A) (j : A.cover.Index) :
    higherAtlasCommutatorLiftL cov A u j =
      ∑ i : A.cover.Index,
        higherSupportedPairResidualTransportL cov A j i (u i) := by
  simp [higherAtlasCommutatorLiftL, ContinuousLinearMap.comp_apply]

/-- The physical source reconstructed from the higher lift is its exact
intrinsic commutator sum. -/
theorem physicalAtlasSourceSlice_higherAtlasCommutatorLiftL [Nonempty M]
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
    (u : HigherCoefficientSpace cov A) {t : ℝ}
    (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    A.physicalAtlasSourceSlice cov (higherAtlasCommutatorLiftL cov A u) t x =
      higherAtlasCommutatorSlice cov A u t x := by
  unfold physicalAtlasSourceSlice
  have hlocal (j : A.cover.Index) :
      A.physicalLocalSourceSlice cov j
          (higherAtlasCommutatorLiftL cov A u j) t x =
        A.cover.partition j x • higherAtlasCommutatorSlice cov A u t x := by
    by_cases hψ : A.cover.partition j x = 0
    · simp only [physicalLocalSourceSlice, cutoffLocalTensorOfMatrix, hψ]
      ext v w
      simp
    · have hxj : x ∈ (A.cover.pieces j : Set M) :=
        subset_closure hψ
      have hxPatch := A.cover.pieces_subset_domain j hxj
      have hxFrame : x ∈ (trivializationAt E TM (j : M)).baseSet :=
        A.patch_subset_trivialization (j : M) hxPatch
      apply continuousBilinearMap_ext_localFrame
        (I := I) (trivializationAt E TM (j : M)) b hxFrame
      intro p k
      rw [A.physicalLocalSourceSlice_localFrame cov j
        (higherAtlasCommutatorLiftL cov A u j) t hxFrame p k]
      simp only [smul_apply, smul_eq_mul]
      let sj := FiniteClassicalTensorHeatField.normalizedTime
        t₀ (A.radius (j : M)) t
      let yj := normalizedTensorHeatCoordinate (I := I)
        (j : M) (A.radius (j : M)) x
      have hsj : sj ∈ Ioc t₀ T :=
        A.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
      have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ T := by
        simpa [sj, yj] using hsj
      have heval : ParabolicC0AlphaBanach.evalCLM (sj, yj) hzj
          (higherAtlasCommutatorLiftL cov A u j) =
          A.radius (j : M) ^ 2 •
            intrinsicTensorPairCoordinates (I := I) b (j : M) x
              (higherAtlasCommutatorSlice cov A u t x) := by
        calc
          ParabolicC0AlphaBanach.evalCLM (sj, yj) hzj
              (higherAtlasCommutatorLiftL cov A u j) =
              ∑ i : A.cover.Index,
                ParabolicC0AlphaBanach.evalCLM (sj, yj) hzj
                  (higherSupportedPairResidualTransportL cov A j i (u i)) := by
            rw [higherAtlasCommutatorLiftL_apply, map_sum]
          _ = ∑ i : A.cover.Index, A.radius (j : M) ^ 2 •
                intrinsicTensorPairCoordinates (I := I) b (j : M) x
                  (connectionLaplacianCutoffCommutator cov
                    (A.cover.partition i)
                    (bufferedLocalHigherSlice cov A i (u i)
                      (FiniteClassicalTensorHeatField.normalizedTime
                        t₀ (A.radius (i : M)) t)) x) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact eval_higherSupportedPairResidualTransportL_at_physical_point
              cov A j i (u i) ht hxj
          _ = A.radius (j : M) ^ 2 •
                intrinsicTensorPairCoordinates (I := I) b (j : M) x
                  (higherAtlasCommutatorSlice cov A u t x) := by
            rw [← Finset.smul_sum]
            congr 1
            unfold higherAtlasCommutatorSlice intrinsicTensorPairCoordinates
            ext out
            simp
      have heval' := congrFun heval (k, p)
      have hrep : ParabolicC0AlphaBanach.representative
            (higherAtlasCommutatorLiftL cov A u j) (sj, yj) (k, p) =
          A.radius (j : M) ^ 2 *
            higherAtlasCommutatorSlice cov A u t x
              ((trivializationAt E TM (j : M)).localFrame b p x)
              ((trivializationAt E TM (j : M)).localFrame b k x) := by
        rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
          (higherAtlasCommutatorLiftL cov A u j) (sj, yj) hzj]
        simpa [intrinsicTensorPairCoordinates, smul_eq_mul] using heval'
      change A.cover.partition j x *
          ((A.radius (j : M))⁻¹ ^ 2 *
            ParabolicC0AlphaBanach.representative
              (higherAtlasCommutatorLiftL cov A u j) (sj, yj) (k, p)) = _
      rw [hrep]
      field_simp [ne_of_gt (A.radius_pos (j : M))]
  simp_rw [hlocal]
  rw [← Finset.sum_smul]
  have hpartition : ∑ j : A.cover.Index, A.cover.partition j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      A.cover.partition.sum_eq_one (Set.mem_univ x)
  rw [hpartition, one_smul]

/-- Global residual identity for an arbitrary higher atlas reconstruction. -/
theorem atlasFieldOfHigher_tensorHeatOperator_eq_source_sub_commutator
    [Nonempty M]
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
    (u : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x =
      A.physicalAtlasSourceSlice cov
          (localCoordinateCauchyFamilyL cov A u) t x -
        higherAtlasCommutatorSlice cov A u t x := by
  unfold atlasFieldOfHigher physicalAtlasSourceSlice
    higherAtlasCommutatorSlice
  rw [FiniteClassicalTensorHeatField.tensorHeatOperator_finsetSum]
  calc
    _ = ∑ i : A.cover.Index,
          (A.physicalLocalSourceSlice cov i
              (localCoordinateCauchyL cov A i (u i)) t x -
            connectionLaplacianCutoffCommutator cov
              (A.cover.partition i)
              (bufferedLocalHigherSlice cov A i (u i)
                (FiniteClassicalTensorHeatField.normalizedTime
                  t₀ (A.radius (i : M)) t)) x) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact localFieldOfHigher_tensorHeatOperator_eq_source_sub_commutator
          cov A i (u i) t ht x
    _ = _ := by
      simp only [localCoordinateCauchyFamilyL_apply]
      simpa only using
        (Finset.sum_sub_distrib
          (s := Finset.univ)
          (fun i : A.cover.Index =>
            A.physicalLocalSourceSlice cov i
              (localCoordinateCauchyL cov A i (u i)) t x)
          (fun i : A.cover.Index =>
            connectionLaplacianCutoffCommutator cov
              (A.cover.partition i)
              (bufferedLocalHigherSlice cov A i (u i)
                (FiniteClassicalTensorHeatField.normalizedTime
                  t₀ (A.radius (i : M)) t)) x))

/-- For a family produced by the local inverses, the higher-family
commutator is definitionally the original parametrix commutator. -/
theorem higherAtlasCommutatorSlice_localSolutionFamilyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) (t : ℝ) (x : M) :
    higherAtlasCommutatorSlice cov A
        (localSolutionFamilyL cov A q) t x =
      A.atlasCommutatorSlice cov q t x := by
  rfl

/-- The zero-trace normalized forcing used for arbitrary initial data. -/
def affineCorrectedSource
    (cov : CovariantDerivative I E TM)
    [Nonempty M]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    SourceSpace cov A :=
  CommutatorLift.correctedSource cov K
    (f - localCoordinateCauchyFamilyL cov A h +
      higherAtlasCommutatorLiftL cov A h)

/-- The coordinate source assigned to the affine local Cauchy family. -/
def affineCorrectedCoordinateSource
    (cov : CovariantDerivative I E TM)
    [Nonempty M]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    SourceSpace cov A :=
  localCoordinateCauchyFamilyL cov A h + affineCorrectedSource cov K h f

/-- The finite-atlas classical solution with arbitrary prescribed atlas
initial trace and arbitrary atlas forcing. -/
def affineCorrectedField
    (cov : CovariantDerivative I E TM)
    [Nonempty M]
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
    (K : CommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ A.commonTerminalTime :=
  atlasFieldOfHigher cov A
    (affineLocalSolutionFamily cov A h
      (affineCorrectedCoordinateSource cov K h f))

/-- The affine corrected field has exactly the prescribed geometric initial
tensor reconstructed from the higher family. -/
theorem hasInitialTrace_affineCorrectedField
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
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (K : CommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (affineCorrectedField cov A K h f) (atlasInitialTrace cov A h) := by
  exact A.hasInitialTrace_affineAtlasField cov h
    (affineCorrectedCoordinateSource cov K h f)

/-- The corrected zero-trace source satisfies the exact affine defect
equation in the atlas source space. -/
theorem affineCorrectedSource_sub_commutator
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    affineCorrectedSource cov K h f -
        K.toContinuousLinearMap (affineCorrectedSource cov K h f) =
      f - localCoordinateCauchyFamilyL cov A h +
        higherAtlasCommutatorLiftL cov A h := by
  exact CommutatorLift.correctedSource_sub_commutator cov K _

/-- The affine corrected field solves the genuine intrinsic tensor heat
equation with the prescribed reconstructed forcing. -/
theorem affineCorrectedField_tensorHeatOperator
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
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (K : CommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    (affineCorrectedField cov A K h f).tensorHeatOperator cov t ht x =
      A.physicalAtlasSourceSlice cov f t x := by
  let g : SourceSpace cov A := affineCorrectedSource cov K h f
  let C : HigherCoefficientSpace cov A →L[ℝ] SourceSpace cov A :=
    localCoordinateCauchyFamilyL cov A
  let Hlift : HigherCoefficientSpace cov A →L[ℝ] SourceSpace cov A :=
    higherAtlasCommutatorLiftL cov A
  let u : HigherCoefficientSpace cov A :=
    affineLocalSolutionFamily cov A h
      (affineCorrectedCoordinateSource cov K h f)
  have hu : u = h + localSolutionFamilyL cov A g := by
    change h + localSolutionFamilyL cov A
        ((C h + g) - C h) = h + localSolutionFamilyL cov A g
    congr 1
    congr 1
    abel
  have hC : C u = C h + g := by
    simpa [C, u, affineCorrectedCoordinateSource, g] using
      A.localCoordinateCauchyFamilyL_affineLocalSolutionFamily cov h
        (affineCorrectedCoordinateSource cov K h f)
  have hg : g - K.toContinuousLinearMap g =
      f - C h + Hlift h := by
    simpa [g, C, Hlift] using
      affineCorrectedSource_sub_commutator cov K h f
  have hsource : C h + g =
      f + Hlift h + K.toContinuousLinearMap g := by
    calc
      C h + g =
          C h + ((g - K.toContinuousLinearMap g) +
            K.toContinuousLinearMap g) := by abel
      _ = C h + ((f - C h + Hlift h) +
            K.toContinuousLinearMap g) := by rw [hg]
      _ = f + Hlift h + K.toContinuousLinearMap g := by abel
  have hH :
      higherAtlasCommutatorSlice cov A u t x =
        A.physicalAtlasSourceSlice cov (Hlift h) t x +
          A.physicalAtlasSourceSlice cov
            (K.toContinuousLinearMap g) t x := by
    calc
      higherAtlasCommutatorSlice cov A u t x =
          A.physicalAtlasSourceSlice cov (Hlift u) t x := by
        exact (physicalAtlasSourceSlice_higherAtlasCommutatorLiftL
          cov A u ht x).symm
      _ = A.physicalAtlasSourceSlice cov
          (Hlift h + Hlift (localSolutionFamilyL cov A g)) t x := by
        rw [hu, map_add]
      _ = A.physicalAtlasSourceSlice cov (Hlift h) t x +
          A.physicalAtlasSourceSlice cov
            (Hlift (localSolutionFamilyL cov A g)) t x := by
        rw [A.physicalAtlasSourceSlice_add cov]
      _ = higherAtlasCommutatorSlice cov A h t x +
          higherAtlasCommutatorSlice cov A
            (localSolutionFamilyL cov A g) t x := by
        rw [physicalAtlasSourceSlice_higherAtlasCommutatorLiftL
          cov A h ht x,
          physicalAtlasSourceSlice_higherAtlasCommutatorLiftL
            cov A (localSolutionFamilyL cov A g) ht x]
      _ = A.physicalAtlasSourceSlice cov (Hlift h) t x +
          A.physicalAtlasSourceSlice cov
            (K.toContinuousLinearMap g) t x := by
        rw [higherAtlasCommutatorSlice_localSolutionFamilyL cov A g t x]
        rw [← physicalAtlasSourceSlice_higherAtlasCommutatorLiftL
          cov A h ht x, ← K.realizes g t ht x]
  have hsourcePhysical := congrArg
    (fun q : SourceSpace cov A => A.physicalAtlasSourceSlice cov q t x)
    hsource
  rw [A.physicalAtlasSourceSlice_add cov,
    A.physicalAtlasSourceSlice_add cov] at hsourcePhysical
  rw [A.physicalAtlasSourceSlice_add cov] at hsourcePhysical
  change (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x =
    A.physicalAtlasSourceSlice cov f t x
  rw [atlasFieldOfHigher_tensorHeatOperator_eq_source_sub_commutator
    cov A u t ht x, hC, A.physicalAtlasSourceSlice_add cov, hH]
  rw [hsourcePhysical]
  abel

/-- Global finite-atlas Schauder estimate for the arbitrary-trace corrected
solution family. -/
theorem norm_affineCorrectedSolutionFamily_le
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    ‖affineLocalSolutionFamily cov A h
        (affineCorrectedCoordinateSource cov K h f)‖ ≤
      ‖h‖ + ‖localSolutionFamilyL cov A‖ *
        (1 - ‖K.toContinuousLinearMap‖)⁻¹ *
          ‖f - localCoordinateCauchyFamilyL cov A h +
            higherAtlasCommutatorLiftL cov A h‖ := by
  let g : SourceSpace cov A := affineCorrectedSource cov K h f
  have hbase := norm_affineLocalSolutionFamily_le cov A h
    (affineCorrectedCoordinateSource cov K h f)
  have hdiff :
      affineCorrectedCoordinateSource cov K h f -
          localCoordinateCauchyFamilyL cov A h = g := by
    unfold affineCorrectedCoordinateSource
    abel
  rw [hdiff] at hbase
  have hg : ‖g‖ ≤ (1 - ‖K.toContinuousLinearMap‖)⁻¹ *
      ‖f - localCoordinateCauchyFamilyL cov A h +
        higherAtlasCommutatorLiftL cov A h‖ := by
    simpa [g, affineCorrectedSource] using
      (CommutatorLift.norm_correctedSource_apply_le cov K
        (f - localCoordinateCauchyFamilyL cov A h +
          higherAtlasCommutatorLiftL cov A h))
  calc
    ‖affineLocalSolutionFamily cov A h
        (affineCorrectedCoordinateSource cov K h f)‖ ≤
        ‖h‖ + ‖localSolutionFamilyL cov A‖ * ‖g‖ := hbase
    _ ≤ ‖h‖ + ‖localSolutionFamilyL cov A‖ *
        ((1 - ‖K.toContinuousLinearMap‖)⁻¹ *
          ‖f - localCoordinateCauchyFamilyL cov A h +
            higherAtlasCommutatorLiftL cov A h‖) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left
          hg
          (norm_nonneg (localSolutionFamilyL cov A))) _
    _ = _ := by ring

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
