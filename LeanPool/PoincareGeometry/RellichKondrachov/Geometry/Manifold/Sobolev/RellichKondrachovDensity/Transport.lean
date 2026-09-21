/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.SupportedH1
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.H1
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.Localization
public import LeanPool.PoincareGeometry.RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul
public import LeanPool.PoincareGeometry.RellichKondrachov.MeasureTheory.Function.LpSpace.ExtendByZeroRangeEquiv

/-! # Transport -/

@[expose] public section

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson

Adaptation: generic finite-measure, two-sided local-density comparison version,
derived from RellichKondrachovRiemannian at upstream commit
70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23 and its local Lean 4.33 migration.
The original support, graph-closure, and compactness proofs are retained;
Riemannian/Hausdorff-specific comparison constants are replaced by explicit
finite bounds on the compact localization supports. No measure equality,
compactness hypothesis, or Poincare inequality is assumed.
-/

/-! # Local measure comparison and support transport for finite chart data -/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped BigOperators ENNReal MeasureTheory Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

local notation "n∞" => (↑(⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

local instance densityTransportInstance0 : MeasurableSpace M := borel M
local instance densityTransportInstance1 : BorelSpace M := ⟨rfl⟩
local instance densityTransportInstance2 : MeasurableSpace E := borel E
local instance densityTransportInstance3 : BorelSpace E := ⟨rfl⟩
local instance densityTransportInstance4 : OpensMeasurableSpace E := by infer_instance

namespace Density
variable (d : FiniteChartData (H := H) (M := M) I)
  (μ : Measure M) [IsFiniteMeasure μ]

include μ
lemma rhoSupportImage_measurable (i : d.ι) :
    MeasurableSet (FiniteChartData.rhoSupportImage (d := d) (I := I) i) := by
  have hK : IsCompact (FiniteChartData.rhoSupportImage (d := d) (I := I) i) :=
    FiniteChartData.isCompact_rhoSupportImage (d := d) (I := I) i
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

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChart_mem_euclidean_h1 (i : d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := d) (I := I)
            (μ :=
              μ))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    (FiniteChartData.h1ToChart (d := d) (I := I) (μ := μM) i x) ∈
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
        (μ := μchart) (E := E) : Set _) := by
  classical
  intro μM μchart
  let A : Set (FiniteChartData.h1Target (d := d) (I := I) μM) :=
    (LinearMap.range (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM)) : Set _)
  have hx_closure : (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM) ∈ closure A := by
    simpa [FiniteChartData.h1, Submodule.topologicalClosure_coe, A] using! x.2
  -- Project to the `i`-th chart coordinate in the ambient product.
  let proj :
      (FiniteChartData.h1Target (d := d) (I := I) μM) →L[ℝ]
        (FiniteChartData.h1TargetE (d := d) (I := I) μM i) :=
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
        FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f ∈
          LinearMap.range
            (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
              (μ := μchart) (E := E)) := by
      simpa [μchart] using!
        (FiniteChartData.h1GraphChart_mem_range_euclidean_graph (d := d) (I := I) (μ := μM) i f)
    -- Conclude membership in the Euclidean `H¹` closure.
    exact (Submodule.le_topologicalClosure _ ) this
  have hClosed :
      IsClosed
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E) :
          Set (FiniteChartData.h1TargetE (d := d) (I := I) μM i)) := by
    simpa [FiniteChartData.h1TargetE, μchart] using!
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isClosed_h1
        (μ := μchart) (E := E))
  have hx_closure_h1 :
      proj x.1 ∈
        closure
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E) :
            Set (FiniteChartData.h1TargetE (d := d) (I := I) μM i)) :=
    (closure_mono hImage) hproj_mem
  have :
      proj x.1 ∈
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E) :
          Set (FiniteChartData.h1TargetE (d := d) (I := I) μM i)) := by
    simpa [hClosed.closure_eq] using! hx_closure_h1
  -- Rewrite the projection as `h1ToChart`.
  simpa [FiniteChartData.h1ToChart] using! this

/-!
### Codomain restriction: chart coordinate as a Euclidean `H¹` element

We package `vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChart_mem_euclidean_h1` as a codomain-restricted continuous
linear map landing in the Euclidean `H¹` submodule.
-/

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1 (i : d.ι) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
        (μ := μchart) (E := E)) := by
  classical
  intro μM μchart
  refine
    (FiniteChartData.h1ToChart (d := d) (I := I) (μ := μM) i).codRestrict
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := μchart) (E := E)) ?_
  intro x
  simpa using! (vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChart_mem_euclidean_h1 (d := d) (μ := μ) (I := I) (E := E) i x)

/-!
### Codomain restriction: chart coordinate in supported Euclidean `H¹`

Using the `L²` support lemma (`h1ToChartL2_mem_extendByZero_range`), we further restrict the
chartwise Euclidean `H¹` element to the supported subspace `h1OnMeasure μchart (rhoSupportImage i)`.
-/

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1GraphChart_fst_mem_extendByZero_range (i : d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ((FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f).1) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  -- Rewrite the chartwise `L²` component as the `toLp` class of the localized function.
  have hL2 :
      (FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f).1 =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
          (μ := μchart) (E := E)
          ⟨FiniteChartData.localize (d := d) (I := I) f.1 i,
            FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
    simpa [μchart, μM, K] using!
      (FiniteChartData.h1GraphChart_fst (d := d) (I := I) (μ := μM) i f)
  -- Apply the general range characterization lemma.
  have hfK :
      MeasureTheory.MemLp
        (FiniteChartData.localize (d := d) (I := I) f.1 i)
        (2 : ℝ≥0∞) μchart := by
    simpa using!
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
          (μ := μchart) (E := E)
          (f := FiniteChartData.localize (d := d) (I := I) f.1 i)
          (FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i))
  have htsupp :
      tsupport (FiniteChartData.localize (d := d) (I := I) f.1 i) ⊆ K := by
    simpa [K] using!
      (FiniteChartData.tsupport_localize_subset_rhoSupportImage (d := d) (I := I) (f := f.1) i)
  -- `toL2` is defined as `MemLp.toLp`, so `hL2` allows rewriting to use the range lemma.
  open Analysis.FunctionalSpaces.Sobolev.Euclidean in
  simpa [hL2, toL2] using!
    (mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset
      (μ := μchart) (hKm := hKm)
      (f := FiniteChartData.localize
        (d := d) (I := I) f.1 i)
      hfK htsupp)

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1GraphChart_snd_mem_extendByZero_range (i : d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ((FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f).2) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  -- Rewrite the chartwise `L²(E)` component as the `toLp` class of the localized gradient.
  have hL2Grad :
      (FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f).2 =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
          (μ := μchart) (E := E)
          ⟨FiniteChartData.localize (d := d) (I := I) f.1 i,
            FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
    simpa [μchart, μM, K] using!
      (FiniteChartData.h1GraphChart_snd (d := d) (I := I) (μ := μM) i f)
  have hfK :
      MeasureTheory.MemLp
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E)
          (FiniteChartData.localize (d := d) (I := I) f.1 i))
        (2 : ℝ≥0∞) μchart := by
    simpa using!
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
          (μ := μchart) (E := E)
          (f := FiniteChartData.localize (d := d) (I := I) f.1 i)
          (FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i))
  have htsupp :
      tsupport (FiniteChartData.localize (d := d) (I := I) f.1 i) ⊆ K := by
    simpa [K] using!
      (FiniteChartData.tsupport_localize_subset_rhoSupportImage (d := d) (I := I) (f := f.1) i)
  have htsuppGrad :
      tsupport
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E)
            (FiniteChartData.localize (d := d) (I := I) f.1 i)) ⊆ K := by
    exact
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset
          (E := E) (f := FiniteChartData.localize (d := d) (I := I) f.1 i)).trans
        htsupp
  open Analysis.FunctionalSpaces.Sobolev.Euclidean in
  simpa [hL2Grad, toL2Grad] using!
    (mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset
      (μ := μchart) (hKm := hKm)
      (f := grad (E := E)
        (FiniteChartData.localize
          (d := d) (I := I) f.1 i))
      hfK htsuppGrad)

lemma h1ToChartL2_mem_extendByZero_range (i : d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := d) (I := I)
            (μ :=
              μ))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    (FiniteChartData.h1ToChartL2 (d := d) (I := I) (μ := μM) i x) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
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
    simpa [hEq] using! hcr
  -- Work in the ambient product space: `x` lies in the closure of `range h1Graph`.
  let A : Set (FiniteChartData.h1Target (d := d) (I := I) μM) :=
    (LinearMap.range (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM)) : Set _)
  let fTarget :
      (FiniteChartData.h1Target (d := d) (I := I) μM) →L[ℝ] (E →₂[μchart] ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.proj (R := ℝ) i)
  have hx_closure : (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM) ∈ closure A := by
    -- Unfold `h1` as a topological closure.
    simpa [FiniteChartData.h1, Submodule.topologicalClosure_coe, A] using! x.2
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
    simpa [fTarget, FiniteChartData.h1Graph, LinearMap.pi_apply] using!
      (vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1GraphChart_fst_mem_extendByZero_range (d := d) (μ := μ) (I := I) i g)
  -- Close the argument using closedness of the range.
  have hClosure :
      closure (Set.image fTarget A) ⊆
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] ℝ)) := by
    have :
        closure (Set.image fTarget A) ⊆
          closure (LinearMap.range e.toLinearMap :
            Set (E →₂[μchart] ℝ)) :=
      closure_mono hImage
    simpa [hClosed.closure_eq] using! this
  have :
      fTarget x.1 ∈
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] ℝ)) :=
    hClosure hf_mem
  -- Rewrite `fTarget x.1` back to `h1ToChartL2`.
  simpa [fTarget, FiniteChartData.h1ToChartL2, FiniteChartData.h1ToChart] using! this

lemma h1ToChartL2Grad_mem_extendByZero_range (i : d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := d) (I := I)
            (μ :=
              μ))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    (FiniteChartData.h1ToChartL2Grad (d := d) (I := I) (μ := μM) i x) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  let e :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hClosed : IsClosed (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
    have hcr : IsClosed (Set.range (fun u => e u)) :=
      (e.isometry.isClosedEmbedding).isClosed_range
    have hEq :
        (Set.range (fun u => e u)) = (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
      ext y
      constructor <;> rintro ⟨u, rfl⟩ <;> exact ⟨u, rfl⟩
    simpa [hEq] using! hcr
  let A : Set (FiniteChartData.h1Target (d := d) (I := I) μM) :=
    (LinearMap.range (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM)) : Set _)
  let fTarget :
      (FiniteChartData.h1Target (d := d) (I := I) μM) →L[ℝ] (E →₂[μchart] E) :=
    (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.proj (R := ℝ) i)
  have hx_closure : (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM) ∈ closure A := by
    simpa [FiniteChartData.h1, Submodule.topologicalClosure_coe, A] using! x.2
  have hf_mem : fTarget x.1 ∈ closure (Set.image fTarget A) :=
    mem_closure_image (f := fTarget) (s := A) (x := x.1)
      (fTarget.continuous.continuousAt) hx_closure
  have hImage :
      Set.image fTarget A ⊆
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
    intro y hy
    rcases hy with ⟨z, hzA, rfl⟩
    rcases hzA with ⟨g, rfl⟩
    simpa [fTarget, FiniteChartData.h1Graph, LinearMap.pi_apply] using!
      (vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1GraphChart_snd_mem_extendByZero_range (d := d) (μ := μ) (I := I) i g)
  have hClosure :
      closure (Set.image fTarget A) ⊆
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) := by
    have :
        closure (Set.image fTarget A) ⊆
          closure (LinearMap.range e.toLinearMap :
            Set (E →₂[μchart] E)) :=
      closure_mono hImage
    simpa [hClosed.closure_eq] using! this
  have :
      fTarget x.1 ∈
        (LinearMap.range e.toLinearMap : Set (E →₂[μchart] E)) :=
    hClosure hf_mem
  simpa [fTarget, FiniteChartData.h1ToChartL2Grad,
    FiniteChartData.h1ToChart] using! this

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1_mem_h1OnMeasure (i : d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := d) (I := I)
            (μ :=
              μ))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    (vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1 (d := d) (μ := μ) (I := I) (E := E) i x) ∈
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure
          (μ := μchart) (E := E) (K := K) (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i) :
        Submodule ℝ
          (↥(Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
            (μ := μchart) (E := E)))) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  -- Unfold membership in `h1OnMeasure` and reduce to the chartwise `L²` support statement.
  have hxL2 :
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2 (μ := μchart) (E := E))
          (vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1 (d := d) (μ := μ) (I := I) (E := E) i x) ∈
        LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
    -- `h1ToL2` is the first projection from the ambient graph target;
    -- `codRestrict` does not change it.
    simpa [vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2,
      FiniteChartData.h1ToChartL2, FiniteChartData.h1ToChart] using!
      (h1ToChartL2_mem_extendByZero_range (d := d) (μ := μ) (I := I) i x)
  -- Finish by unfolding the `comap` definition.
  simpa [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure, hKm] using! hxL2

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1OnMeasure (i : d.ι) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure
            (μ := μchart) (E := E) (K := K)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)) := by
  classical
  intro μM μchart K
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  refine
    (vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1 (d := d) (μ := μ) (I := I) (E := E) i).codRestrict
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure
        (μ := μchart) (E := E) (K := K) hKm) ?_
  intro x
  simpa [hKm] using! (vendorGeometryManifoldSobolevRellichKondrachovDensityTransport_h1ToChartH1_mem_h1OnMeasure (d := d) (μ := μ) (I := I) (E := E) i x)



/-- Finite two-sided comparison with Lebesgue measure on each localization
support. These are measure inequalities, not compactness assumptions. -/
structure LocalMeasureComparison where
  chartToVolume : d.ι → ℝ≥0∞
  volumeToChart : d.ι → ℝ≥0∞
  chartToVolume_ne_top : ∀ i, chartToVolume i ≠ ∞
  volumeToChart_ne_top : ∀ i, volumeToChart i ≠ ∞
  chart_le_volume : ∀ i,
    (FiniteChartData.chartMeasure (d := d) (I := I) μ i).restrict
        (FiniteChartData.rhoSupportImage (d := d) (I := I) i) ≤
      chartToVolume i • (volume : Measure E).restrict
        (FiniteChartData.rhoSupportImage (d := d) (I := I) i)
  volume_le_chart : ∀ i,
    (volume : Measure E).restrict
        (FiniteChartData.rhoSupportImage (d := d) (I := I) i) ≤
      volumeToChart i • (FiniteChartData.chartMeasure (d := d) (I := I) μ i).restrict
        (FiniteChartData.rhoSupportImage (d := d) (I := I) i)

variable (hcomp : LocalMeasureComparison d μ)
include hcomp

lemma chartMeasure_restrict_rhoSupportImage_le_volume (i : d.ι) :
    (FiniteChartData.chartMeasure (d := d) (I := I) μ i).restrict
      (FiniteChartData.rhoSupportImage (d := d) (I := I) i) ≤
    hcomp.chartToVolume i • (volume : Measure E).restrict
      (FiniteChartData.rhoSupportImage (d := d) (I := I) i) :=
  hcomp.chart_le_volume i

lemma volume_restrict_rhoSupportImage_le_chartMeasure (i : d.ι) :
    (volume : Measure E).restrict (FiniteChartData.rhoSupportImage (d := d) (I := I) i) ≤
    hcomp.volumeToChart i • (FiniteChartData.chartMeasure (d := d) (I := I) μ i).restrict
      (FiniteChartData.rhoSupportImage (d := d) (I := I) i) :=
  hcomp.volume_le_chart i

lemma chartMeasure_volume_constant_ne_top (i : d.ι) : hcomp.chartToVolume i ≠ ∞ :=
  hcomp.chartToVolume_ne_top i

lemma volume_chartMeasure_constant_ne_top (i : d.ι) : hcomp.volumeToChart i ≠ ∞ :=
  hcomp.volumeToChart_ne_top i

/-- Comparison of the restricted L² spaces for scalar or vector-valued functions. -/
noncomputable def l2EquivVolumeOnRhoSupportImage' (i : d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (E →₂[(FiniteChartData.chartMeasure (d := d) (I := I) μ i).restrict
      (FiniteChartData.rhoSupportImage (d := d) (I := I) i)] F) ≃L[ℝ]
    (E →₂[(volume : Measure E).restrict
      (FiniteChartData.rhoSupportImage (d := d) (I := I) i)] F) :=
  MeasureTheory.Lp.changeMeasureEquiv
    (hcomp.volumeToChart_ne_top i) (hcomp.chartToVolume_ne_top i)
    (hcomp.volume_le_chart i) (hcomp.chart_le_volume i) (by simp)

/-- Comparison on the ranges of extension by zero, used for compactness transport. -/
noncomputable def l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage' (i : d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μ i
    let K := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ (μ := μchart) (E := F) (p := (2 : ℝ≥0∞))
        (s := K) (rhoSupportImage_measurable (d := d) (μ := μ) i)).toLinearMap)) ≃L[ℝ]
    ↥(LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞))
        (s := K) (rhoSupportImage_measurable (d := d) (μ := μ) i)).toLinearMap)) :=
  MeasureTheory.Lp.extendByZeroRangeEquivOfRestrictChangeMeasureEquiv
    (rhoSupportImage_measurable (d := d) (μ := μ) i)
    (hcomp.volumeToChart_ne_top i) (hcomp.chartToVolume_ne_top i)
    (hcomp.volume_le_chart i) (hcomp.chart_le_volume i) (by simp)


end Density
end
end Sobolev
end Manifold
end Geometry
end RellichKondrachov
