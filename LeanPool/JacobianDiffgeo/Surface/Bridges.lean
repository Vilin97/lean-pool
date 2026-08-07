/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.Basic

/-!
# Bridges: `ContMDiff` over `𝓘(ℂ)` ↔ chart-local `ContDiff`/`AnalyticAt`

Unit: surfaces-and-charts (`docs/design/surfaces-and-charts.md` §3.1; Forster §1).

On a Riemann surface `X` (`ChartedSpace ℂ X` + `IsManifold 𝓘(ℂ) ω X`) these lemmas convert
manifold smoothness/holomorphy into planar statements about the chart composites, eliminating
`ContDiffWithinAt`-over-`range I` once and for all:

* `contMDiffAt_iff_contDiffAt_extChartAt`, `contMDiffAt_iff_analyticAt` for `f : X → ℂ`
  (no `ContinuousAt` side condition, no target chart), and their `𝓘(ℂ, F)`-target
  generalizations `contMDiffAt_iff_contDiffAt_extChartAt_comp`, `contMDiffAt_iff_analyticAt_comp`
  for any complex Banach space `F` (requested by holomorphic-forms);
* `contMDiffAt_iff_contDiffAt_writtenInExtChartAt`, `contMDiffAt_iff_analyticAt_writtenInExtChartAt`
  and the recentered `contMDiffAt_iff_analyticAt_inChartAt` (requested by local-multiplicity)
  for `f : X → Y` between surfaces;
* chart-invariance `contMDiffAt_iff_analyticAt_of_mem_source` and the set version
  `contMDiffOn_iff_analyticOnNhd_of_subset_source`: holomorphy may be read in ANY atlas chart.
-/

open scoped ContDiff Manifold
open Set Filter Topology IsManifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {n : ℕ∞ω}

/-! ### Maps into a complex Banach space (target = model space, no target chart) -/

section ModelTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `C^n` at `x` for `f : X → F` is exactly `C^n` of the chart composite (Banach-space target;
requested by holomorphic-forms for `(ℂ →L[ℂ] ℂ)`-valued maps). -/
theorem contMDiffAt_iff_contDiffAt_extChartAt_comp {f : X → F} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) n f x ↔
      ContDiffAt ℂ n (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) := by
  constructor
  · intro hf
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x x) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds x)
    exact (hf.comp_of_eq hsymm (extChartAt_to_inv x)).contDiffAt
  · intro hf
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) n ((f ∘ (extChartAt 𝓘(ℂ) x).symm) ∘ extChartAt 𝓘(ℂ) x)
        x := hf.contMDiffAt.comp x contMDiffAt_extChartAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x] with z hz
    simp only [Function.comp_apply, PartialEquiv.left_inv _ hz]

/-- Holomorphy at `x` for `f : X → F` is analyticity of the chart composite. -/
theorem contMDiffAt_iff_analyticAt_comp [CompleteSpace F] {f : X → F} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) ω f x ↔
      AnalyticAt ℂ (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
  contMDiffAt_iff_contDiffAt_extChartAt_comp.trans
    ⟨fun h => h.analyticAt, fun h => h.contDiffAt⟩

/-- `chartAt`-spelled variant (the exact statement requested by holomorphic-forms). -/
theorem contMDiffAt_iff_analyticAt_comp_chartAt [CompleteSpace F] {f : X → F} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) ω f x ↔
      AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  contMDiffAt_iff_analyticAt_comp

end ModelTarget

/-! ### Maps to `ℂ` (the frozen interface of the design) -/

/-- `C^n` at `x` for `f : X → ℂ` is exactly `C^n` of the chart composite. -/
theorem contMDiffAt_iff_contDiffAt_extChartAt {f : X → ℂ} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n f x ↔
      ContDiffAt ℂ n (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
  contMDiffAt_iff_contDiffAt_extChartAt_comp

/-- Holomorphy at `x` for `f : X → ℂ` is analyticity of the chart composite. -/
theorem contMDiffAt_iff_analyticAt {f : X → ℂ} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔
      AnalyticAt ℂ (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
  contMDiffAt_iff_analyticAt_comp

/-! ### Maps between surfaces (two charts) -/

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- Two-chart version, `f : X → Y`. `ContinuousAt` cannot be dropped on the `←` side (the
chart composite does not see `f` outside the chart sources). -/
theorem contMDiffAt_iff_contDiffAt_writtenInExtChartAt {f : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n f x ↔
      ContinuousAt f x ∧
        ContDiffAt ℂ n (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) := by
  rw [contMDiffAt_iff, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  exact Iff.rfl

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
theorem contMDiffAt_iff_analyticAt_writtenInExtChartAt {f : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔
      ContinuousAt f x ∧
        AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) :=
  contMDiffAt_iff_contDiffAt_writtenInExtChartAt.trans
    (and_congr_right fun _ => ⟨fun h => h.analyticAt, fun h => h.contDiffAt⟩)

/-- Subtracting a constant does not change analyticity (helper for the recentered bridge). -/
theorem analyticAt_sub_const_iff {g : ℂ → ℂ} {z c : ℂ} :
    AnalyticAt ℂ (fun w => g w - c) z ↔ AnalyticAt ℂ g z :=
  ⟨fun h => by simpa [sub_add_cancel] using h.fun_add (analyticAt_const (v := c)),
   fun h => h.fun_sub analyticAt_const⟩

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- Recentered two-chart bridge (the exact statement requested by local-multiplicity, matching
mathlib's `analyticOrderAt` normal form). -/
theorem contMDiffAt_iff_analyticAt_inChartAt {f : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔
      ContinuousAt f x ∧
        AnalyticAt ℂ
          (fun z => chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)) - chartAt ℂ (f x) (f x))
          (chartAt ℂ x x) := by
  rw [contMDiffAt_iff_analyticAt_writtenInExtChartAt]
  exact and_congr_right fun _ =>
    (analyticAt_sub_const_iff
      (g := fun z => chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)))).symm

/-! ### Chart invariance: read holomorphy in any atlas chart -/

/-- Analyticity may be read in ANY atlas chart whose source contains `x` (chart-invariance;
the workhorse for CC3/CC4-style definitions and for `coeffIn`). -/
theorem contMDiffAt_iff_analyticAt_of_mem_source {f : X → ℂ} {x : X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X) (hx : x ∈ e.source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ AnalyticAt ℂ (f ∘ e.symm) (e x) := by
  rw [ContMDiffAt,
    contMDiffWithinAt_iff_of_mem_maximalAtlas (subset_maximalAtlas he)
      (chart_mem_maximalAtlas (f x)) hx (mem_chart_source ℂ (f x)),
    continuousWithinAt_univ]
  simp only [preimage_univ, univ_inter, modelWithCornersSelf_coe, Set.range_id,
    contDiffWithinAt_univ]
  constructor
  · exact fun h => h.2.analyticAt
  · intro h
    refine ⟨?_, h.contDiffAt⟩
    have hc : ContinuousAt ((f ∘ e.symm) ∘ e) x := h.continuousAt.comp (e.continuousAt hx)
    refine hc.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    simp [e.left_inv hz]

/-- Set version on an open subset of a chart source. -/
theorem contMDiffOn_iff_analyticOnNhd_of_subset_source {f : X → ℂ} {s : Set X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X) (hs : s ⊆ e.source)
    (hso : IsOpen s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f s ↔ AnalyticOnNhd ℂ (f ∘ e.symm) (e '' s) := by
  constructor
  · rintro h _ ⟨z, hz, rfl⟩
    exact (contMDiffAt_iff_analyticAt_of_mem_source he (hs hz)).1
      (h.contMDiffAt (hso.mem_nhds hz))
  · intro h z hz
    exact ((contMDiffAt_iff_analyticAt_of_mem_source he (hs hz)).2
      (h _ (mem_image_of_mem e hz))).contMDiffWithinAt

end RS
