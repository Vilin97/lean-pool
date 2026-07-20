/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.SupportedH1
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure.Finiteness
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannianVolume
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.H1
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.Localization
import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul
import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.ExtendByZeroRangeEquiv

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Transport`

Change-of-measure and `extendByZero` transport lemmas used in the Riemannian Rellich–Kondrachov
compactness proof.

## Main definitions

- `l2EquivVolumeOnRhoSupportImage` / `l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage`: `L²`-level
  equivalences between the chart pushforward measure of the Riemannian volume and Lebesgue `volume`,
  localized to the fixed compact support `FiniteChartData.rhoSupportImage`.
- `rhoSupportImage_measurable`: measurability of the fixed support set.
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped BigOperators ENNReal MeasureTheory Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [I.Boundaryless]
  [T3Space M]
  [T2Space M] [CompactSpace M]

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMSobolevRellichKondrachovRiemannian :
    MeasurableSpace M := borel M
local instance instBorelSpaceMSobolevRellichKondrachovRiemannian : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceESobolevRellichKondrachovRiemannian :
    MeasurableSpace E := borel E
local instance instBorelSpaceESobolevRellichKondrachovRiemannian :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceESobolevRellichKondrachovRiemannian :
    OpensMeasurableSpace E := by
  infer_instance

-- On compact manifolds, the Riemannian volume measure is finite.
local instance instIsFiniteMeasureriemannianVolumeMeasure :
    IsFiniteMeasure
        (Riemannian.riemannianVolumeMeasure (I := I) (M := M)) :=
  Riemannian.riemannianVolumeMeasure_isFiniteMeasure (I := I) (M := M)

namespace RiemannianFiniteChartData

variable (dR : RiemannianFiniteChartData (H := H) (M := M) I)

/-!
## Support control

We will use a fixed compact set in the chart model space containing the supports of all localized
functions. In the Riemannian-specialized finite chart data, this set sits inside the chart ball.
-/

omit
  [FiniteDimensional ℝ E]
  [IsManifold I (1 : WithTop ℕ∞) M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [I.Boundaryless]
  [T3Space M]
  [T2Space M]
  [CompactSpace M] in
lemma rhoSupportImage_subset_chartBall (i : dR.d.ι) :
    FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i ⊆ chartBall dR i := by
  classical
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hxBall :
      x ∈
        (extChartAt I (dR.d.center i)) ⁻¹'
            Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i)) (dR.r i) ∩
          (extChartAt I (dR.d.center i)).source :=
    dR.subordinate_ball i hx
  refine ⟨?_, ?_⟩
  · exact hxBall.1
  · exact (extChartAt I (dR.d.center i)).map_source hxBall.2

/-!
## Measure comparison on the fixed compact support

Downstream `L²` change-of-measure equivalences require *finite* domination constants. The Riemannian
chart-measure comparison lemmas provide explicit constants on the chart ball; the support-control
lemma above lets us restrict those inequalities to the compact support set
`FiniteChartData.rhoSupportImage`.
-/

private lemma restrict_le_of_subset {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {s t : Set α} {c : ℝ≥0∞} (ht : MeasurableSet t) (hts : t ⊆ s)
    (h : μ.restrict s ≤ c • ν.restrict s) :
    μ.restrict t ≤ c • ν.restrict t := by
  have h' := Measure.restrict_mono_measure (μ := μ.restrict s) (ν := c • ν.restrict s) h t
  -- Rewrite both sides using `restrict_restrict` and simplify the intersections using `t ⊆ s`.
  simpa [Measure.restrict_restrict ht, Measure.restrict_smul, inter_eq_left.mpr hts] using h'

variable {I}

omit [FiniteDimensional ℝ E]
  [IsManifold I (1 : WithTop ℕ∞) M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [I.Boundaryless]
  [T3Space M]
  [T2Space M] in
lemma rhoSupportImage_measurable (i : dR.d.ι) :
    MeasurableSet (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i) := by
  have hK : IsCompact (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i) :=
    FiniteChartData.isCompact_rhoSupportImage (d := dR.d) (I := I) i
  exact hK.measurableSet

/-!
### `L²` support for the chartwise `H¹` projection

For each chart `i`, the scalar `L²` component of the manifold `H¹` element is (a.e.) supported in
`rhoSupportImage i`. We record this as membership in the range of `extendByZeroₗᵢ` from the
restricted measure.
-/

/-!
### Chart coordinate lands in Euclidean `H¹`

The manifold `H¹` is built from the Euclidean graph construction chartwise, hence each chart
coordinate of a manifold `H¹` element belongs to the corresponding Euclidean `H¹` space.
-/

omit [T2Space M] in
private lemma h1ToChart_mem_euclidean_h1 (i : dR.d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I)
            (μ :=
              RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                (M := M)))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    (FiniteChartData.h1ToChart (d := dR.d) (I := I) (μ := μM) i x) ∈
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
        (μ := μchart) (E := E) : Set _) := by
  classical
  intro μM μchart
  let A : Set (FiniteChartData.h1Target (d := dR.d) (I := I) μM) :=
    (LinearMap.range (FiniteChartData.h1Graph (d := dR.d) (I := I) (μ := μM)) : Set _)
  have hx_closure : (x.1 : FiniteChartData.h1Target (d := dR.d) (I := I) μM) ∈ closure A := by
    simp only [FiniteChartData.h1, A]
    exact x.2
  -- Project to the `i`-th chart coordinate in the ambient product.
  let proj :
      (FiniteChartData.h1Target (d := dR.d) (I := I) μM) →L[ℝ]
        (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i) :=
    ContinuousLinearMap.proj (R := ℝ) i
  have hproj_mem : proj x.1 ∈ closure (Set.image proj A) :=
    mem_closure_image (f := proj) (s := A) (x := x.1)
      (proj.continuous.continuousAt) hx_closure
  have hImage :
      Set.image proj A ⊆
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
          (μ := μchart) (E := E) : Set _) := by
    intro y hy
    rcases hy with ⟨z, hzA, rfl⟩
    rcases hzA with ⟨f, rfl⟩
    -- `proj (h1Graph f)` is `h1GraphChart i f`, and this lies in the Euclidean graph range.
    have :
        FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f ∈
          LinearMap.range
            (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
              (μ := μchart) (E := E)) := by
      simpa [μchart] using
        (FiniteChartData.h1GraphChart_mem_range_euclidean_graph (d := dR.d) (I := I) (μ := μM) i f)
    -- Conclude membership in the Euclidean `H¹` closure.
    exact (Submodule.le_topologicalClosure _ ) this
  have hClosed :
      IsClosed
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E) :
          Set (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i)) := by
    simpa [FiniteChartData.h1TargetE, μchart] using
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isClosed_h1
        (μ := μchart) (E := E))
  have hx_closure_h1 :
      proj x.1 ∈
        closure
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E) :
            Set (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i)) :=
    (closure_mono hImage) hproj_mem
  have :
      proj x.1 ∈
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E) :
          Set (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i)) := by
    simpa [hClosed.closure_eq] using hx_closure_h1
  -- Rewrite the projection as `h1ToChart`.
  have hxi : proj x.1 = FiniteChartData.h1ToChart (d := dR.d) (I := I) (μ := μM) i x := rfl
  rw [hxi] at this
  exact this

/-!
### Codomain restriction: chart coordinate as a Euclidean `H¹` element

We package `h1ToChart_mem_euclidean_h1` as a codomain-restricted continuous
linear map landing in the Euclidean `H¹` submodule.
-/

omit [T2Space M] in
private noncomputable def h1ToChartH1 (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
        (μ := μchart) (E := E)) := by
  classical
  intro μM μchart
  refine
    (FiniteChartData.h1ToChart (d := dR.d) (I := I) (μ := μM) i).codRestrict
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E)) ?_
  intro x
  simpa using (h1ToChart_mem_euclidean_h1 (dR := dR) (I := I) (E := E) i x)

/-!
### Codomain restriction: chart coordinate in supported Euclidean `H¹`

Using the `L²` support lemma (`h1ToChartL2_mem_extendByZero_range`), we further restrict the
chartwise Euclidean `H¹` element to the supported subspace `h1OnMeasure μchart (rhoSupportImage i)`.
-/

omit [T2Space M] in
private lemma h1GraphChart_fst_mem_extendByZero_range (i : dR.d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ((FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f).1) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  -- Rewrite the chartwise `L²` component as the `toLp` class of the localized function.
  have hL2 :
      (FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f).1 =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
          (μ := μchart) (E := E)
          ⟨FiniteChartData.localize (d := dR.d) (I := I) f.1 i,
            FiniteChartData.localize_mem_C1c (d := dR.d) (I := I) (f := f.1) f.2 i⟩ := by
    simpa [μchart, μM, K] using
      (FiniteChartData.h1GraphChart_fst (d := dR.d) (I := I) (μ := μM) i f)
  -- Apply the general range characterization lemma.
  have hfK :
      MeasureTheory.MemLp
        (FiniteChartData.localize (d := dR.d) (I := I) f.1 i)
        (2 : ℝ≥0∞) μchart := by
    simpa using
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
          (μ := μchart) (E := E)
          (f := FiniteChartData.localize (d := dR.d) (I := I) f.1 i)
          (FiniteChartData.localize_mem_C1c (d := dR.d) (I := I) (f := f.1) f.2 i))
  have htsupp :
      tsupport (FiniteChartData.localize (d := dR.d) (I := I) f.1 i) ⊆ K := by
    simpa [K] using
      (FiniteChartData.tsupport_localize_subset_rhoSupportImage (d := dR.d) (I := I) (f := f.1) i)
  -- `toL2` is defined as `MemLp.toLp`, so `hL2` allows rewriting to use the range lemma.
  open Analysis.FunctionalSpaces.Sobolev.Euclidean in
  simpa [hL2, toL2] using
    (mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset
      (μ := μchart) (hKm := hKm)
      (f := FiniteChartData.localize
        (d := dR.d) (I := I) f.1 i)
      hfK htsupp)

omit [T2Space M] in
private lemma h1GraphChart_snd_mem_extendByZero_range (i : dR.d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ((FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f).2) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  -- Rewrite the chartwise `L²(E)` component as the `toLp` class of the localized gradient.
  have hL2Grad :
      (FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f).2 =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
          (μ := μchart) (E := E)
          ⟨FiniteChartData.localize (d := dR.d) (I := I) f.1 i,
            FiniteChartData.localize_mem_C1c (d := dR.d) (I := I) (f := f.1) f.2 i⟩ := by
    simpa [μchart, μM, K] using
      (FiniteChartData.h1GraphChart_snd (d := dR.d) (I := I) (μ := μM) i f)
  have hfK :
      MeasureTheory.MemLp
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E)
          (FiniteChartData.localize (d := dR.d) (I := I) f.1 i))
        (2 : ℝ≥0∞) μchart := by
    simpa using
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
          (μ := μchart) (E := E)
          (f := FiniteChartData.localize (d := dR.d) (I := I) f.1 i)
          (FiniteChartData.localize_mem_C1c (d := dR.d) (I := I) (f := f.1) f.2 i))
  have htsupp :
      tsupport (FiniteChartData.localize (d := dR.d) (I := I) f.1 i) ⊆ K := by
    simpa [K] using
      (FiniteChartData.tsupport_localize_subset_rhoSupportImage (d := dR.d) (I := I) (f := f.1) i)
  have htsuppGrad :
      tsupport
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E)
            (FiniteChartData.localize (d := dR.d) (I := I) f.1 i)) ⊆ K := by
    exact
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset
          (E := E) (f := FiniteChartData.localize (d := dR.d) (I := I) f.1 i)).trans
        htsupp
  open Analysis.FunctionalSpaces.Sobolev.Euclidean in
  simpa [hL2Grad, toL2Grad] using
    (mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset
      (μ := μchart) (hKm := hKm)
      (f := grad (E := E)
        (FiniteChartData.localize
          (d := dR.d) (I := I) f.1 i))
      hfK htsuppGrad)

omit [T2Space M] in
lemma h1ToChartL2_mem_extendByZero_range (i : dR.d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I)
            (μ :=
              RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                (M := M)))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    (FiniteChartData.h1ToChartL2 (d := dR.d) (I := I) (μ := μM) i x) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  let e :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hClosed : IsClosed (LinearMap.range e.toLinearMap : Set (E →₂[μchart] ℝ)) := by
    -- `e` is an isometry; with completeness of `Lp` it has closed range.
    have hcr : IsClosed (Set.range (fun u => e u)) :=
      (e.isometry.isClosedEmbedding).isClosed_range
    -- Convert `Set.range` to `LinearMap.range`.
    have hEq :
        (Set.range (fun u => e u)) = (LinearMap.range e.toLinearMap : Set (E →₂[μchart] ℝ)) := by
      ext y
      constructor <;> rintro ⟨u, rfl⟩ <;> exact ⟨u, rfl⟩
    simpa [hEq] using hcr
  -- Work in the ambient product space: `x` lies in the closure of `range h1Graph`.
  let A : Set (FiniteChartData.h1Target (d := dR.d) (I := I) μM) :=
    (LinearMap.range (FiniteChartData.h1Graph (d := dR.d) (I := I) (μ := μM)) : Set _)
  let fTarget :
      (FiniteChartData.h1Target (d := dR.d) (I := I) μM) →L[ℝ] (E →₂[μchart] ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.proj (R := ℝ) i)
  have hx_closure : (x.1 : FiniteChartData.h1Target (d := dR.d) (I := I) μM) ∈ closure A := by
    -- Unfold `h1` as a topological closure.
    simp only [FiniteChartData.h1, A]
    exact x.2
  have hf_mem : fTarget x.1 ∈ closure (Set.image fTarget A) :=
    mem_closure_image (f := fTarget) (s := A) (x := x.1)
      (fTarget.continuous.continuousAt) hx_closure
  have hImage :
      Set.image fTarget A ⊆
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] ℝ)) := by
    intro y hy
    rcases hy with ⟨z, hzA, rfl⟩
    rcases hzA with ⟨g, rfl⟩
    -- Reduce to the dense range used to define `h1`.
    simpa [fTarget, FiniteChartData.h1Graph, LinearMap.pi_apply] using
      (h1GraphChart_fst_mem_extendByZero_range (dR := dR) (I := I) i g)
  -- Close the argument using closedness of the range.
  have hClosure :
      closure (Set.image fTarget A) ⊆
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] ℝ)) := by
    have :
        closure (Set.image fTarget A) ⊆
          closure (LinearMap.range e.toLinearMap :
            Set (E →₂[μchart] ℝ)) :=
      closure_mono hImage
    simpa [hClosed.closure_eq] using this
  have :
      fTarget x.1 ∈
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] ℝ)) :=
    hClosure hf_mem
  -- Rewrite `fTarget x.1` back to `h1ToChartL2`.
  simpa [fTarget, FiniteChartData.h1ToChartL2, FiniteChartData.h1ToChart] using this

omit [T2Space M] in
lemma h1ToChartL2Grad_mem_extendByZero_range (i : dR.d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I)
            (μ :=
              RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                (M := M)))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    (FiniteChartData.h1ToChartL2Grad (d := dR.d) (I := I) (μ := μM) i x) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  let e :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hClosed : IsClosed (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
    have hcr : IsClosed (Set.range (fun u => e u)) :=
      (e.isometry.isClosedEmbedding).isClosed_range
    have hEq :
        (Set.range (fun u => e u)) = (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
      ext y
      constructor <;> rintro ⟨u, rfl⟩ <;> exact ⟨u, rfl⟩
    simpa [hEq] using hcr
  let A : Set (FiniteChartData.h1Target (d := dR.d) (I := I) μM) :=
    (LinearMap.range (FiniteChartData.h1Graph (d := dR.d) (I := I) (μ := μM)) : Set _)
  let fTarget :
      (FiniteChartData.h1Target (d := dR.d) (I := I) μM) →L[ℝ] (E →₂[μchart] E) :=
    (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.proj (R := ℝ) i)
  have hx_closure : (x.1 : FiniteChartData.h1Target (d := dR.d) (I := I) μM) ∈ closure A := by
    simp only [FiniteChartData.h1, A]
    exact x.2
  have hf_mem : fTarget x.1 ∈ closure (Set.image fTarget A) :=
    mem_closure_image (f := fTarget) (s := A) (x := x.1)
      (fTarget.continuous.continuousAt) hx_closure
  have hImage :
      Set.image fTarget A ⊆
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
    intro y hy
    rcases hy with ⟨z, hzA, rfl⟩
    rcases hzA with ⟨g, rfl⟩
    simpa [fTarget, FiniteChartData.h1Graph, LinearMap.pi_apply] using
      (h1GraphChart_snd_mem_extendByZero_range (dR := dR) (I := I) i g)
  have hClosure :
      closure (Set.image fTarget A) ⊆
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
    have :
        closure (Set.image fTarget A) ⊆
          closure (LinearMap.range e.toLinearMap :
            Set (E →₂[μchart] E)) :=
      closure_mono hImage
    simpa [hClosed.closure_eq] using this
  have :
      fTarget x.1 ∈
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) :=
    hClosure hf_mem
  simpa [fTarget, FiniteChartData.h1ToChartL2Grad,
    FiniteChartData.h1ToChart] using this

omit [T2Space M] in
private lemma h1ToChartH1_mem_h1OnMeasure (i : dR.d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I)
            (μ :=
              RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                (M := M)))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    (h1ToChartH1 (dR := dR) (I := I) (E := E) i x) ∈
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure
          (μ := μchart) (E := E) (K := K) (rhoSupportImage_measurable (dR := dR) (I := I) i) :
        Submodule ℝ
          (↥(Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
            (μ := μchart) (E := E)))) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  -- Unfold membership in `h1OnMeasure` and reduce to the chartwise `L²` support statement.
  have hxL2 :
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2 (μ := μchart) (E := E))
          (h1ToChartH1 (dR := dR) (I := I) (E := E) i x) ∈
        LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
    -- `h1ToL2` is the first projection from the ambient graph target;
    -- `codRestrict` does not change it.
    simpa [h1ToChartH1, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2,
      FiniteChartData.h1ToChartL2, FiniteChartData.h1ToChart] using
      (h1ToChartL2_mem_extendByZero_range (dR := dR) (I := I) i x)
  -- Finish by unfolding the `comap` definition.
  simpa [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure, hKm] using hxL2

omit [T2Space M] in
private noncomputable def h1ToChartH1OnMeasure (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure
            (μ := μchart) (E := E) (K := K)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  refine
    (h1ToChartH1 (dR := dR) (I := I) (E := E) i).codRestrict
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure
        (μ := μchart) (E := E) (K := K) hKm) ?_
  intro x
  simpa [hKm] using (h1ToChartH1_mem_h1OnMeasure (dR := dR) (I := I) (E := E) i x)

omit [I.Boundaryless] [T2Space M] in
lemma chartMeasure_restrict_rhoSupportImage_le_volume (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    (μchart.restrict (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)) ≤
      (((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
            ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
              ((volume : Measure E) (Metric.closedBall (0 : E) 1)))) •
        (volume : Measure E).restrict (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i) := by
  classical
  intro μM μchart
  have hKsub : FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i ⊆ chartBall dR i :=
    rhoSupportImage_subset_chartBall (dR := dR) (I := I) i
  have h :=
    RiemannianFiniteChartData.chartMeasure_restrict_le_volume (dR := dR) (I := I) i
  -- Restrict the chart-ball inequality to the smaller compact support set.
  exact
    restrict_le_of_subset (ht := rhoSupportImage_measurable (dR := dR) (I := I) i) (hts := hKsub) h

omit [I.Boundaryless] [T2Space M] in
lemma volume_restrict_rhoSupportImage_le_chartMeasure (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    (volume : Measure E).restrict (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i) ≤
      (((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
                ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
              ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ))) •
          μchart.restrict (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)) := by
  classical
  intro μM μchart
  have hKsub : FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i ⊆ chartBall dR i :=
    rhoSupportImage_subset_chartBall (dR := dR) (I := I) i
  have h :=
    RiemannianFiniteChartData.volume_restrict_le_chartMeasure (dR := dR) (I := I) i
  -- Restrict the chart-ball inequality to the smaller compact support set.
  exact
    restrict_le_of_subset (ht := rhoSupportImage_measurable (dR := dR) (I := I) i) (hts := hKsub) h

/-!
### `L²` equivalence on the compact support

On `FiniteChartData.rhoSupportImage i`, the chart pushforward measure of the Riemannian volume is
mutually comparable with Lebesgue `volume`. This yields a continuous linear equivalence between the
restricted `L²` spaces.
-/

/-- The `L²`-level equivalence between the chart pushforward measure and Lebesgue `volume`,
localized to the fixed compact support, for a general value type `F`. -/
noncomputable def l2EquivVolumeOnRhoSupportImage' (i : dR.d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (E →₂[
        (FiniteChartData.chartMeasure (d := dR.d) (I := I)
          (Riemannian.riemannianVolumeMeasure
            (I := I) (M := M)) i).restrict
          (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)
      ] F) ≃L[ℝ]
      (E →₂[
          (volume : Measure E).restrict
            (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)
        ] F) := by
  classical
  let μM :=
    Riemannian.riemannianVolumeMeasure (I := I) (M := M)
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  have hμ_le :
      μchart.restrict K ≤
        (((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
              ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
                ((volume : Measure E) (Metric.closedBall (0 : E) 1)))) •
          (volume : Measure E).restrict K := by
    simpa [μM, μchart, K] using
      chartMeasure_restrict_rhoSupportImage_le_volume (dR := dR) (I := I) i
  have hvol_le :
      (volume : Measure E).restrict K ≤
        (((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
                  ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
                ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ))) •
            μchart.restrict K) := by
    simpa [μM, μchart, K] using
      volume_restrict_rhoSupportImage_le_chartMeasure (dR := dR) (I := I) i
  have hVolBall_ne_zero : ((volume : Measure E) (Metric.closedBall (0 : E) 1)) ≠ 0 := by
    have hpos :
        0 < (volume : Measure E) (Metric.closedBall (0 : E) 1) := by
      simpa using
        (Metric.measure_closedBall_pos (μ := (volume : Measure E))
          (x := (0 : E)) (r := (1 : ℝ)) (by norm_num))
    exact hpos.ne'
  have hHausBall_ne_top :
      ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1)) ≠ ∞ := by
    have hcompact : IsCompact (Metric.closedBall (0 : E) (1 : ℝ)) :=
      isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))
    exact hcompact.measure_ne_top (μ := (μH[(Module.finrank ℝ E : ℝ)] : Measure E))
  have hVolBall_ne_top :
      ((volume : Measure E) (Metric.closedBall (0 : E) 1)) ≠ ∞ := by
    have hcompact : IsCompact (Metric.closedBall (0 : E) (1 : ℝ)) :=
      isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))
    exact hcompact.measure_ne_top (μ := (volume : Measure E))
  have hHausBall_ne_zero :
      ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1)) ≠ 0 := by
    have hpos :
        0 < (μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1) := by
      simpa using
        (Metric.measure_closedBall_pos
          (μ := (μH[(Module.finrank ℝ E : ℝ)] : Measure E))
          (x := (0 : E)) (r := (1 : ℝ)) (by norm_num))
    exact hpos.ne'
  have hHausDivVol_ne_top :
      ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
          ((volume : Measure E) (Metric.closedBall (0 : E) 1))) ≠ ∞ := by
    have hdenInv : (((volume : Measure E) (Metric.closedBall (0 : E) 1))⁻¹) ≠ ∞ := by
      simpa using (ENNReal.inv_ne_top.2 hVolBall_ne_zero)
    simpa [div_eq_mul_inv] using (ENNReal.mul_ne_top hHausBall_ne_top hdenInv)
  have hVolDivHaus_ne_top :
      (((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
          ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) ≠ ∞ := by
    have hdenInv :
        (((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))⁻¹) ≠ ∞ := by
      simpa using (ENNReal.inv_ne_top.2 hHausBall_ne_zero)
    simpa [div_eq_mul_inv] using (ENNReal.mul_ne_top hVolBall_ne_top hdenInv)
  have hcChartVol :
      (((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
            ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
              ((volume : Measure E) (Metric.closedBall (0 : E) 1)))) ≠ ∞ := by
    have hC : ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) ≠ ∞ := by
      have hbase : (dR.C i : ℝ≥0∞) ≠ ∞ := by simp
      have hexp : 0 ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast (Nat.zero_le _)
      exact ENNReal.rpow_ne_top_of_nonneg hexp hbase
    simpa using (ENNReal.mul_ne_top hC hHausDivVol_ne_top)
  have hcVolChart :
      ((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
                ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
              ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ))) ≠ ∞ := by
    have hCfwd : ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) ≠ ∞ := by
      have hbase : (dR.Cfwd i : ℝ≥0∞) ≠ ∞ := by simp
      have hexp : 0 ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast (Nat.zero_le _)
      exact ENNReal.rpow_ne_top_of_nonneg hexp hbase
    simpa [mul_assoc, mul_left_comm, mul_comm] using (ENNReal.mul_ne_top hVolDivHaus_ne_top hCfwd)
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by simp
  -- `Lp.changeMeasureEquiv` is the identity on functions, but changes the `Lp` carrier measure.
  exact
    (MeasureTheory.Lp.changeMeasureEquiv
      (μ := μchart.restrict K) (ν := (volume : Measure E).restrict K)
      (E := F) (p := (2 : ℝ≥0∞))
      hcVolChart hcChartVol hvol_le hμ_le hp)

/-- The scalar (`ℝ`-valued) `L²`-level equivalence between the chart pushforward measure and
Lebesgue `volume`, localized to the fixed compact support. -/
noncomputable def l2EquivVolumeOnRhoSupportImage (i : dR.d.ι) :
    (E →₂[
        (FiniteChartData.chartMeasure (d := dR.d) (I := I)
          (Riemannian.riemannianVolumeMeasure (I := I) (M := M))
          i).restrict
          (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)
      ] ℝ) ≃L[ℝ]
      (E →₂[
        (volume : Measure E).restrict
          (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)
        ] ℝ) :=
  l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) (F := ℝ) i

/-!
### Range equivalence for `extendByZeroₗᵢ` on the compact support

The range of extension-by-zero from `μ.restrict K` is canonically isomorphic to the restricted `L²`
space. Combining this with `l2EquivVolumeOnRhoSupportImage` yields a (continuous) linear equivalence
between the `extendByZero` ranges for `μchart` and Lebesgue `volume`.
-/

/-- The extension-by-zero range equivalence between the chart pushforward measure and Lebesgue
`volume` on the fixed compact support, for a general value type `F`. -/
noncomputable def l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage' (i : dR.d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := μchart) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) ≃L[ℝ]
        ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  -- Avoid carrying a local name for `MeasurableSet K` to keep definitional
  -- equalities stable across transports.
  let eChart :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := μchart) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
      (rhoSupportImage_measurable (dR := dR) (I := I) i)
  let eVol :=
    MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
      (rhoSupportImage_measurable (dR := dR) (I := I) i)
  -- Identify each range with the corresponding restricted `L²` space,
  -- then use `Lp.changeMeasureEquiv`.
  -- This is packaged as `extendByZeroRangeEquivOfRestrictChangeMeasureEquiv`.
  let cChartVol : ℝ≥0∞ :=
    (((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
          ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
            ((volume : Measure E) (Metric.closedBall (0 : E) 1))))
  let cVolChart : ℝ≥0∞ :=
    ((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
            ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)))
  have hμ_le : μchart.restrict K ≤ cChartVol • (volume : Measure E).restrict K := by
    simpa [cChartVol, μM, μchart, K] using
      chartMeasure_restrict_rhoSupportImage_le_volume (dR := dR) (I := I) i
  have hvol_le : (volume : Measure E).restrict K ≤ cVolChart • μchart.restrict K := by
    simpa [cVolChart, μM, μchart, K] using
      volume_restrict_rhoSupportImage_le_chartMeasure (dR := dR) (I := I) i
  have hcChartVol : cChartVol ≠ ∞ :=
    RiemannianFiniteChartData.chartMeasure_volume_constant_ne_top (dR := dR) (I := I) (E := E) i
  have hcVolChart : cVolChart ≠ ∞ :=
    RiemannianFiniteChartData.volume_chartMeasure_constant_ne_top (dR := dR) (I := I) (E := E) i
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by simp
  -- Transport the range through restricted `L²` and change-of-measure equivalence.
  simpa [cVolChart, cChartVol, eChart, eVol] using
    (MeasureTheory.Lp.extendByZeroRangeEquivOfRestrictChangeMeasureEquiv
      (μ := μchart) (ν := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
      (rhoSupportImage_measurable (dR := dR) (I := I) i)
      (c₁ := cVolChart) (c₂ := cChartVol) hcVolChart hcChartVol hvol_le hμ_le hp)

/-- The scalar (`ℝ`-valued) extension-by-zero range equivalence between the chart pushforward
measure and Lebesgue `volume` on the fixed compact support. -/
noncomputable def l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) ≃L[ℝ]
        ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) :=
  l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage' (dR := dR) (I := I) (F := ℝ) i

end RiemannianFiniteChartData

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
