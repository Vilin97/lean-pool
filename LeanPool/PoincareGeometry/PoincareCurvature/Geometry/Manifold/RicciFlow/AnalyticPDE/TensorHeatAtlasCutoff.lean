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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteAtlasEquation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteParabolicScaling
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLeibniz

/-!
# Buffered cutoffs for the finite tensor-heat atlas

Each member of the subordinate partition has compact topological support
strictly inside its radius-adapted chart patch.  This file chooses a second
smooth cutoff which is identically one on a neighborhood of that compact
piece and remains supported in the patch.  Multiplying the uncut local
solution by the buffered cutoff gives a globally `C²` tensor field without
changing the actual partition-of-unity summand.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative
open PoincareCurvature.Bundle.Trivialization

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
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance atlasCutoffFirstNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCutoffFirstNormedSpace :
    NormedSpace ℝ (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCutoffSecondNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasCutoffSecondNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasCutoffThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance atlasCutoffThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance atlasCutoffThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance atlasCutoffThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance atlasCutoffThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasCutoffThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasCutoffThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- A smooth buffer which is one near one compact partition piece and whose
support stays inside the corresponding tensor-heat chart patch. -/
structure BufferedCutoff
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) where
  cutoff : M → ℝ
  contMDiff_three : ContMDiff I 𝓘(ℝ) 3 cutoff
  compactSupport : HasCompactSupport cutoff
  support_subset : tsupport cutoff ⊆
    actualLocalTensorHeatPatch (I := I) (i : M) (A.radius (i : M))
  one_nhds : ∀ᶠ x in nhdsSet (A.cover.pieces i : Set M), cutoff x = 1

/-- Every atlas piece admits a buffered cutoff. -/
theorem nonempty_bufferedCutoff
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : Nonempty (BufferedCutoff cov A i) := by
  let K : Set M := (A.cover.pieces i : Set M)
  let U : Set M := actualLocalTensorHeatPatch (I := I)
    (i : M) (A.radius (i : M))
  have hK : IsCompact K := (A.cover.pieces i).isCompact
  have hU : IsOpen U := isOpen_actualLocalTensorHeatPatch
    (I := I) (i : M) (A.radius (i : M))
  have hKU : K ⊆ U := A.cover.pieces_subset_domain i
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hfOne, hfZero, _hfIcc⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior I hK.isClosed hKL
      (n := (3 : ℕ∞))
  have hsupp : Function.support (f : M → ℝ) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hfZero x hxL)
  have hcompact : HasCompactSupport (f : M → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact hLc hsupp
  have htsupp : tsupport (f : M → ℝ) ⊆ U := by
    calc
      tsupport (f : M → ℝ) = closure (Function.support (f : M → ℝ)) := rfl
      _ ⊆ closure L := closure_mono hsupp
      _ = L := hLc.isClosed.closure_eq
      _ ⊆ U := hLU
  exact ⟨⟨(f : M → ℝ), f.contMDiff, hcompact, htsupp, hfOne⟩⟩

/-- A fixed buffered cutoff for each selected atlas piece. -/
def bufferedCutoff
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : BufferedCutoff cov A i :=
  Classical.choice (nonempty_bufferedCutoff cov A i)

theorem bufferedCutoff_eq_one_of_mem_piece
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) {x : M} (hx : x ∈ (A.cover.pieces i : Set M)) :
    (A.bufferedCutoff cov i).cutoff x = 1 :=
  (A.bufferedCutoff cov i).one_nhds.self_of_nhdsSet x hx

/-- Every partition piece lies in the topological support of its buffered
cutoff. -/
theorem piece_subset_bufferedCutoff_tsupport
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) :
    (A.cover.pieces i : Set M) ⊆
      tsupport (A.bufferedCutoff cov i).cutoff := by
  intro x hx
  apply subset_closure
  rw [Function.mem_support]
  rw [A.bufferedCutoff_eq_one_of_mem_piece cov i hx]
  norm_num

/-- The normalized local solution, extended to a globally `C²` tensor by
the buffered cutoff. -/
def bufferedLocalSolutionSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) : ∀ x : M, T₂ x :=
  cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM (i : M)) b
    (A.bufferedCutoff cov i).cutoff
    (normalizedTensorHeatCoefficientSlice (I := I)
      (i : M) (A.radius (i : M))
      (A.normalizedLocalSolution cov i q) s)

/-- Every positive-time buffered slice is globally `C²`. -/
theorem contMDiff_bufferedLocalSolutionSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    {s : ℝ} (hs : s ∈ Ioc t₀ T) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (A.bufferedLocalSolutionSlice cov i q s x)) := by
  apply contMDiff_cutoffLocalTensorOfMatrix_of_coefficients_of_isOpen
    (I := I) (i : M) (trivializationAt E TM (i : M)) b
    (A.bufferedCutoff cov i).cutoff
    (normalizedTensorHeatCoefficientSlice (I := I)
      (i : M) (A.radius (i : M))
      (A.normalizedLocalSolution cov i q) s)
    (isOpen_actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)))
    (A.patch_subset_trivialization (i : M))
  · exact (A.bufferedCutoff cov i).contMDiff_three.of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  · exact (A.bufferedCutoff cov i).support_subset
  · exact contMDiffOn_normalizedTensorHeatCoefficientSlice
      (I := I) (i : M) (A.radius (i : M))
          (A.normalizedLocalSolution cov i q) A.alpha_pos hs

/-- In fixed chart coordinates, the buffered solution agrees on a whole
neighborhood of each compact partition piece with the radius-normalized
coordinate solution.  This neighborhood statement, rather than merely a
pointwise value identity, is what preserves both spatial derivatives. -/
theorem localTensorCoordinates_buffered_eventuallyEq_normalized
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) :
    localTensorCoordinates (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (A.bufferedLocalSolutionSlice cov i q s) =ᶠ[nhds
          ((extChartAt I (i : M)) x)]
      (fun z => FiniteParabolicC2AlphaBanach.value
        (A.localInverse (i : M) q)
        (s, (A.radius (i : M))⁻¹ •
          (z - (extChartAt I (i : M)) (i : M)))) := by
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) := A.cover.pieces_subset_domain i hx
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
    rw [(extChartAt I (i : M)).left_inv hxPatch.1] at h
    exact h
  have hχx : ∀ᶠ y in nhds x, (A.bufferedCutoff cov i).cutoff y = 1 :=
    (A.bufferedCutoff cov i).one_nhds.filter_mono
      (nhds_le_nhdsSet hx)
  have hχz : ∀ᶠ z in nhds ((extChartAt I (i : M)) x),
      (A.bufferedCutoff cov i).cutoff
        ((extChartAt I (i : M)).symm z) = 1 :=
    hsymm.eventually hχx
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
  have hbase := A.localTensorCoordinates_normalized_reconstruction
    cov i q s hs hzPatch
  have hleft : (extChartAt I (i : M))
      ((extChartAt I (i : M)).symm z) = z :=
    (extChartAt I (i : M)).right_inv hzTarget'
  change localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b
      (A.bufferedLocalSolutionSlice cov i q s) z = _
  rw [hleft] at hbase
  have hbase' : localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b
      (localTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M))
          (A.normalizedLocalSolution cov i q) s)) z =
      FiniteParabolicC2AlphaBanach.value
        (A.localInverse (i : M) q)
        (s, (A.radius (i : M))⁻¹ •
          (z - (extChartAt I (i : M)) (i : M))) := by
    have hnorm : normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M))
        ((extChartAt I (i : M)).symm z) =
        (A.radius (i : M))⁻¹ •
          (z - (extChartAt I (i : M)) (i : M)) := by
      unfold normalizedTensorHeatCoordinate
      rw [hleft]
    rw [hnorm] at hbase
    exact hbase
  rw [← hbase']
  have hfield : A.bufferedLocalSolutionSlice cov i q s
      ((extChartAt I (i : M)).symm z) =
      localTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M))
          (A.normalizedLocalSolution cov i q) s)
        ((extChartAt I (i : M)).symm z) := by
    unfold bufferedLocalSolutionSlice cutoffLocalTensorOfMatrix
    rw [hχ, one_smul]
  funext out
  simp [localTensorCoordinates, localTwoTensorComponentInChart,
    writtenInExtChartAt]
  simp_all only [mfld_simps, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  unfold localTwoTensorComponent
  rw [hfield]

/-- The first and second fixed-chart derivatives of the buffered local
solution carry exactly one and two inverse-radius factors.  The conclusion
uses the stored derivative witnesses of the finite-cylinder Banach element,
so this is also the calculus bridge from the analytic jet to the intrinsic
coordinate operator. -/
theorem localTensorCoordinateDerivatives_buffered
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) :
    localTensorCoordinateDerivative (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (A.bufferedLocalSolutionSlice cov i q s)
        ((extChartAt I (i : M)) x) =
      finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
        (FiniteParabolicC2AlphaBanach.spaceDeriv
          (A.localInverse (i : M) q)
          (s, normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) x)) ∧
    localTensorCoordinateSecondDerivative (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (A.bufferedLocalSolutionSlice cov i q s)
        ((extChartAt I (i : M)) x) =
      finiteAffineSecondDerivativeL (A.radius (i : M))⁻¹
        (FiniteParabolicC2AlphaBanach.spaceSecondDeriv
          (A.localInverse (i : M) q)
          (s, normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) x)) := by
  let z₀ : E := (extChartAt I (i : M)) x
  let c : E := (extChartAt I (i : M)) (i : M)
  let r : ℝ := A.radius (i : M)
  let u := A.localInverse (i : M) q
  let F : E → W₂ := localTensorCoordinates (I := I) (i : M)
    (trivializationAt E TM (i : M)) b
    (A.bufferedLocalSolutionSlice cov i q s)
  let G : E → W₂ := fun z =>
    FiniteParabolicC2AlphaBanach.value u (s, r⁻¹ • (z - c))
  let L : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  let K := (ContinuousLinearMap.compL ℝ E E W₂).flip L
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) := A.cover.pieces_subset_domain i hx
  have hzTarget : z₀ ∈ (extChartAt I (i : M)).target := by
    exact (extChartAt I (i : M)).map_source hxPatch.1
  have hzRange : Set.range I ∈ nhds z₀ :=
    mem_of_superset
      ((isOpen_extChartAt_target (I := I) (i : M)).mem_nhds hzTarget)
      (extChartAt_target_subset_range (I := I) (i : M))
  have hFG : F =ᶠ[nhds z₀] G := by
    simpa [F, G, z₀, c, r, u] using
      A.localTensorCoordinates_buffered_eventuallyEq_normalized
        cov i q s hs hx
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
    simp [L, z₀, c, r, u, normalizedTensorHeatCoordinate,
      finiteAffineFirstDerivativeL_apply]
  · change fderivWithin ℝ (fderivWithin ℝ F (Set.range I))
      (Set.range I) z₀ = _
    rw [hsecondFG.trans hsecondG]
    ext v w out
    simp [K, L, z₀, c, r, u, normalizedTensorHeatCoordinate,
      finiteAffineSecondDerivativeL_apply, pow_two, smul_smul]

/-- After multiplying by `r²`, the intrinsic connection Laplacian of the
buffered solution is exactly the normalized coordinate spatial operator. -/
theorem radius_sq_mul_connectionLaplacian_buffered_apply
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
    A.radius (i : M) ^ 2 *
        connectionLaplacian cov
          (A.bufferedLocalSolutionSlice cov i q s) x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) =
      (localTensorHeatPrincipalCoefficient (I := I) (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) x)
            (FiniteParabolicC2AlphaBanach.spaceSecondDeriv
              (A.localInverse (i : M) q)
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x)) +
        A.radius (i : M) •
          localTensorHeatFirstCoefficient (I := I) cov (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) x)
            (FiniteParabolicC2AlphaBanach.spaceDeriv
              (A.localInverse (i : M) q)
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x)) +
        A.radius (i : M) ^ 2 •
          localTensorHeatZeroCoefficient (I := I) cov (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) x)
            (FiniteParabolicC2AlphaBanach.value
              (A.localInverse (i : M) q)
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x))) (k, p) := by
  let h := A.bufferedLocalSolutionSlice cov i q s
  let z : E := (extChartAt I (i : M)) x
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  let U := FiniteParabolicC2AlphaBanach.value
    (A.localInverse (i : M) q) (s, ξ)
  let D₁ := FiniteParabolicC2AlphaBanach.spaceDeriv
    (A.localInverse (i : M) q) (s, ξ)
  let D₂ := FiniteParabolicC2AlphaBanach.spaceSecondDeriv
    (A.localInverse (i : M) q) (s, ξ)
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) := A.cover.pieces_subset_domain i hx
  have hh := A.contMDiff_bufferedLocalSolutionSlice cov i q hs
  have hbridge :=
    connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_contMDiff_two
      (I := I) cov (i : M) (trivializationAt E TM (i : M)) b hh
        (A.patch_subset_trivialization (i : M) hxPatch) hxPatch.1 p k
  have hderiv := A.localTensorCoordinateDerivatives_buffered
    cov i q s hs hx
  have hvalue : localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b h z = U := by
    have hev := A.localTensorCoordinates_buffered_eventuallyEq_normalized
      cov i q s hs hx
    have hv := hev.self_of_nhds
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

/-- The reconstructed normalized time derivative of the buffered solution
recovers the pair-indexed time derivative stored by the local inverse. -/
theorem normalizedTensorHeatTimeDerivative_buffered_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    normalizedTensorHeatTimeDerivative (I := I) (i : M)
        (A.radius (i : M)) b (A.bufferedCutoff cov i).cutoff
        (A.normalizedLocalSolution cov i q) s x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      FiniteParabolicC2AlphaBanach.timeDeriv
        (A.localInverse (i : M) q)
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x) (k, p) := by
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) := A.cover.pieces_subset_domain i hx
  have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
    A.patch_subset_trivialization (i : M) hxPatch
  have hz : (s, normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x) ∈
      parabolicFiniteCylinder E t₀ T := by
    simpa using hs
  rw [normalizedTensorHeatTimeDerivative,
    cutoffLocalTensorOfMatrix_localFrame
      (I := I) (trivializationAt E TM (i : M)) b _ _ hxFrame]
  rw [A.bufferedCutoff_eq_one_of_mem_piece cov i hx, one_mul]
  unfold normalizedLocalSolution
  simp only [FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL _ _ _ hz]
  rfl

/-- On every partition piece, the buffered local solution satisfies the
genuine normalized tensor heat equation.  The spatial term is the actual
connection Laplacian and the right-hand side is the selected coordinate
source, with no differential identity hidden in a hypothesis. -/
theorem normalized_buffered_tensorHeatEquation_apply
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
    (normalizedTensorHeatTimeDerivative (I := I) (i : M)
          (A.radius (i : M)) b (A.bufferedCutoff cov i).cutoff
          (A.normalizedLocalSolution cov i q) s x -
        A.radius (i : M) ^ 2 •
          connectionLaplacian cov
            (A.bufferedLocalSolutionSlice cov i q s) x)
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs) q (k, p) := by
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) := A.cover.pieces_subset_domain i hx
  have hξ : ξ ∈ Metric.closedBall (0 : E) 1 := by
    exact inv_smul_sub_mem_closedBall_one_of_mem_ball
      (A.radius_pos (i : M)) hxPatch.2
  have hz : (s, ξ) ∈ parabolicFiniteCylinder E t₀ T := by
    simpa [ξ] using hs
  have hcoord := A.normalizedLocalEquation_on_unitBall cov i q (s, ξ) hz hξ
  have hphysical : (extChartAt I (i : M)) (i : M) +
      A.radius (i : M) • ξ = (extChartAt I (i : M)) x := by
    dsimp [ξ, normalizedTensorHeatCoordinate]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (A.radius_pos (i : M))),
      one_smul, add_sub_cancel]
  rw [hphysical] at hcoord
  have htime := A.normalizedTensorHeatTimeDerivative_buffered_apply
    cov i q s hs hx p k
  have hlap := A.radius_sq_mul_connectionLaplacian_buffered_apply
    cov i q s hs hx p k
  have hcomponent := congrArg (fun v : W₂ => v (k, p)) hcoord
  change
    normalizedTensorHeatTimeDerivative (I := I) (i : M)
        (A.radius (i : M)) b (A.bufferedCutoff cov i).cutoff
        (A.normalizedLocalSolution cov i q) s x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) -
      A.radius (i : M) ^ 2 *
        connectionLaplacian cov
          (A.bufferedLocalSolutionSlice cov i q s) x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) = _
  rw [htime, hlap]
  simpa only [Pi.sub_apply, ξ] using hcomponent

/-- The original partition-cutoff summand is exactly the partition function
times its globally regular buffered local solution. -/
theorem cutoffLocalSummand_eq_partition_smul_buffered
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) :
    cutoffLocalTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b (A.cover.partition i)
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M))
          (A.normalizedLocalSolution cov i q) s) =
      (fun x => A.cover.partition i x •
        A.bufferedLocalSolutionSlice cov i q s x) := by
  funext x
  by_cases hψ : A.cover.partition i x = 0
  · simp only [cutoffLocalTensorOfMatrix]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [_root_.smul_apply, smul_eq_mul]
    simp [hψ]
  · have hxSupport : x ∈ Function.support (A.cover.partition i) := by
      simpa [Function.mem_support] using hψ
    have hxPiece : x ∈ (A.cover.pieces i : Set M) :=
      subset_closure hxSupport
    have hχ := A.bufferedCutoff_eq_one_of_mem_piece cov i hxPiece
    simp [cutoffLocalTensorOfMatrix, bufferedLocalSolutionSlice, hχ]

/-- The connection Laplacian of an actual partition-cutoff atlas summand is
the partition function times the Laplacian of its buffered uncut solution,
plus the genuine lower-order cutoff commutator.  All differentiability
premises are derived from the finite-cylinder solution and the two smooth
cutoffs. -/
theorem connectionLaplacian_cutoffLocalSummand_eq_buffered_add_commutator
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    {s : ℝ} (hs : s ∈ Ioc t₀ T) (x : M) :
    connectionLaplacian cov
        (cutoffLocalTensorOfMatrix (I := I)
          (trivializationAt E TM (i : M)) b (A.cover.partition i)
          (normalizedTensorHeatCoefficientSlice (I := I)
            (i : M) (A.radius (i : M))
            (A.normalizedLocalSolution cov i q) s)) x =
      A.cover.partition i x •
          connectionLaplacian cov
            (A.bufferedLocalSolutionSlice cov i q s) x +
        connectionLaplacianCutoffCommutator cov (A.cover.partition i)
          (A.bufferedLocalSolutionSlice cov i q s) x := by
  rw [A.cutoffLocalSummand_eq_partition_smul_buffered cov i q s]
  exact connectionLaplacian_smul_function_of_contMDiff_two cov
    ((A.cover.partition i).contMDiff.of_le
      (by decide : (2 : WithTop ℕ∞) ≤ ∞))
    (A.contMDiff_bufferedLocalSolutionSlice cov i q hs) x

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
