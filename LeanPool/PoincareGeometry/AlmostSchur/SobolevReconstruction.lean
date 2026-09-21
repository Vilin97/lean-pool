/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2
public import LeanPool.PoincareGeometry.AlmostSchur.DensityComparison

/-!
# Reconstruction of smooth functions from the chart Sobolev graph

The imported graph-closure Sobolev construction is due to Adam Benenson.
These new lemmas identify its assembled L2 projection with the actual original
function, rather than merely with a formal sum of chart components.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal BigOperators
open RellichKondrachov.Geometry.Manifold.Sobolev
open FiniteChartData

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M]

local instance reconstructionMeasurableM : MeasurableSpace M := borel M
local instance reconstructionBorelM : BorelSpace M := ⟨rfl⟩
local instance reconstructionMeasurableE : MeasurableSpace E := borel E
local instance reconstructionBorelE : BorelSpace E := ⟨rfl⟩

variable (d : FiniteChartData (H := H) (M := M) I)
  (μ : Measure M) [IsFiniteMeasure μ]
/-- Each pulled-back localized graph component is the cutoff times the
original function almost everywhere for the original manifold measure. -/
theorem chartToGlobalL2_graph_ae_eq (i : d.ι) (f : ↥(C1 (I := I))) :
    (chartToGlobalL2 (d := d) μ i ((h1GraphChart (d := d) μ i f).1) : M → ℝ) =ᵐ[μ]
      fun x => d.ρ i x * f.1 x := by
  classical
  let φ := extChartAt I (d.center i)
  let g := (h1GraphChart (d := d) μ i f).1
  have hs : MeasurableSet φ.source := (isOpen_extChartAt_source (I := I) (d.center i)).measurableSet
  have hg : (g : E → ℝ) =ᵐ[chartMeasure (d := d) μ i] localize (d := d) f.1 i := by
    dsimp only [g]
    rw [h1GraphChart_fst]
    exact MemLp.coeFn_toLp _
  have hmp := measurePreserving_extChartAtMk (d := d) μ i
  have hpull : (chartPullbackL2 (d := d) μ i g : M → ℝ) =ᵐ[μ.restrict φ.source]
      fun x => d.ρ i x * f.1 x := by
    have hcoe : (chartPullbackL2 (d := d) μ i g : M → ℝ) =ᵐ[μ.restrict φ.source]
        (g : E → ℝ) ∘ extChartAtMk (d := d) μ i :=
      Lp.coeFn_compMeasurePreserving g hmp
    have hlocal := hmp.quasiMeasurePreserving.ae_eq hg
    filter_upwards [hcoe, hlocal, extChartAt_ae_eq_extChartAtMk (d := d) μ i,
      ae_restrict_mem hs] with x hx hloc hchart hxs
    rw [hx, hloc]
    simp only [Function.comp_apply]
    rw [← hchart]
    change localize (d := d) f.1 i (φ x) = _
    rw [localize, indicator_of_mem (φ.map_source hxs)]
    change d.ρ i (φ.symm (φ x)) * f.1 (φ.symm (φ x)) = _
    rw [φ.left_inv hxs]
  have hext := Lp.extendByZeroₗᵢ_ae_eq (μ := μ) (p := 2) hs
    (chartPullbackL2 (d := d) μ i g)
  have hpull' := (ae_restrict_iff' hs).mp hpull
  filter_upwards [hext, hpull'] with x hx hp
  change (Lp.extendByZeroₗᵢ hs (chartPullbackL2 (d := d) μ i g)) x = _
  rw [hx]
  by_cases hxs : x ∈ φ.source
  · rw [indicator_of_mem hxs]
    exact hp hxs
  · rw [indicator_of_notMem hxs]
    have hρ : d.ρ i x = 0 := by
      by_contra hn
      exact hxs (by simpa [φ] using d.subordinate i (subset_closure hn))
    simp [hρ]
/-- The global projection of a smooth Sobolev graph is the actual function
almost everywhere; partition reconstruction is proved pointwise. -/
theorem h1ToL2_c1ToH1_ae_eq (f : ↥(C1 (I := I))) :
    (h1ToL2 (d := d) μ (c1ToH1 (d := d) μ f) : M → ℝ) =ᵐ[μ] f.1 := by
  classical
  rw [h1ToL2_c1ToH1]
  have hall : ∀ᵐ x ∂μ, ∀ i : d.ι,
      chartToGlobalL2 (d := d) μ i ((h1GraphChart (d := d) μ i f).1) x =
        d.ρ i x * f.1 x :=
    (ae_all_iff).mpr fun i => chartToGlobalL2_graph_ae_eq d μ i f
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : d.ι => chartToGlobalL2 (d := d) μ i ((h1GraphChart (d := d) μ i f).1))
  filter_upwards [hall, hsum] with x hx hs
  simp only [c1ToL2, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, ContinuousLinearMap.coe_coe]
  change (∑ i : d.ι, chartToGlobalL2 (d := d) μ i ((h1GraphChart (d := d) μ i f).1)) x = f.1 x
  rw [hs]
  simp_rw [hx]
  rw [← Finset.sum_mul]
  have hρ : ∑ i : d.ι, d.ρ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using d.ρ.sum_eq_one (mem_univ x)
  rw [hρ, one_mul]

end AlmostSchur
