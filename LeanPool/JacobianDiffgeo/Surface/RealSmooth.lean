/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Surface.Bridges
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# CC7: the `𝓘(ℝ, ℂ)` bridge — real smoothness from holomorphy

Unit: surfaces-and-charts (`docs/design/surfaces-and-charts.md` §3.2, `core-choices.md` CC7).

`𝓘(ℂ)` and `𝓘(ℝ, ℂ)` are different terms of different types, but both have
`toPartialEquiv = PartialEquiv.refl ℂ` definitionally and share the same `ChartedSpace ℂ X`
instance. This file provides, once and for all:

* `instance isManifoldRealOfComplex : IsManifold 𝓘(ℝ, ℂ) ω X` — a holomorphic atlas is
  ℝ-analytically compatible; `IsManifold 𝓘(ℝ, ℂ) n X` for every `n` (in particular `∞`)
  then follows by instance search, unlocking `SmoothPartitionOfUnity` on `X`;
* the pinned `rfl` facts `extChartAt_real_eq`, `coe_extChartAt_real_eq`,
  `writtenInExtChartAt_real_eq` (consumed by dbar-solvability: the ℝ-charts ARE the ℂ-charts);
* ℝ-smoothness bridges `contMDiffAt_real_iff_contDiffAt`,
  `contMDiffAt_real_iff_contDiffAt_writtenInExtChartAt`;
* holomorphic ⇒ real-`C^n`: `contMDiffAt_real_of_holomorphicAt`, `contMDiff_real_of_holomorphic`,
  `contMDiffOn_real_of_holomorphicOn`;
* `exists_smoothPartitionOfUnity` on a compact T2 surface.
-/

open scoped ContDiff Manifold
open Set Filter Topology IsManifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {n : ℕ∞ω}

/-- CC7. A holomorphic atlas is ℝ-analytically compatible: ℂ-analytic transition maps are
ℝ-analytic. Priority below the model-space instance so `X := ℂ` resolves to mathlib's
`instIsManifoldModelSpace` first. -/
instance (priority := 100) isManifoldRealOfComplex : IsManifold 𝓘(ℝ, ℂ) ω X := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have h := (contDiffGroupoid ω 𝓘(ℂ)).compatible he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  have hs : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  have h1 : ContDiffOn ℂ ω (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    simpa [contDiffPregroupoid] using h.1
  have h2 := ((contDiffOn_omega_iff_analyticOn hs.uniqueDiffOn).1 h1).restrictScalars (𝕜 := ℝ)
  simpa using (contDiffOn_omega_iff_analyticOn hs.uniqueDiffOn).2 h2

-- `IsManifold 𝓘(ℝ, ℂ) ∞ X` and `IsManifold 𝓘(ℝ, ℂ) n X` need NO declaration: instance
-- search derives them from `ω`. Compile-time guarantees:
example : IsManifold 𝓘(ℝ, ℂ) ∞ X := inferInstance
example : IsManifold 𝓘(ℝ, ℂ) 2 X := inferInstance

omit [IsManifold 𝓘(ℂ) ω X] in
/-- CC7 pinned fact: the extended chart over `𝓘(ℝ, ℂ)` IS the extended chart over `𝓘(ℂ)`. -/
theorem extChartAt_real_eq (x : X) : extChartAt 𝓘(ℝ, ℂ) x = extChartAt 𝓘(ℂ) x := rfl

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Function-level variant. -/
theorem coe_extChartAt_real_eq (x : X) :
    (extChartAt 𝓘(ℝ, ℂ) x : X → ℂ) = extChartAt 𝓘(ℂ) x := rfl

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- The two-model chart composites agree definitionally (consumed by dbar-solvability). -/
theorem writtenInExtChartAt_real_eq {f : X → Y} (x : X) :
    writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x f = writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f := rfl

/-- ℝ-smoothness bridge in the (shared) charts, `f : X → ℂ`. -/
theorem contMDiffAt_real_iff_contDiffAt {f : X → ℂ} {x : X} :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f x ↔
      ContDiffAt ℝ n (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) := by
  constructor
  · intro hf
    have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (extChartAt 𝓘(ℝ, ℂ) x).symm
        (extChartAt 𝓘(ℝ, ℂ) x x) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds x)
    exact (hf.comp_of_eq hsymm (extChartAt_to_inv x)).contDiffAt
  · intro hf
    have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
        ((f ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm) ∘ extChartAt 𝓘(ℝ, ℂ) x) x :=
      hf.contMDiffAt.comp x contMDiffAt_extChartAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, ℂ)) x] with z hz
    simp only [Function.comp_apply, PartialEquiv.left_inv _ hz]

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- Two-chart ℝ-smoothness bridge, `f : X → Y`; the composite is written in the `𝓘(ℂ)` charts
(which are literally the `𝓘(ℝ, ℂ)` charts). -/
theorem contMDiffAt_real_iff_contDiffAt_writtenInExtChartAt {f : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f x ↔
      ContinuousAt f x ∧
        ContDiffAt ℝ n (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) := by
  rw [contMDiffAt_iff, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  exact Iff.rfl

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- Holomorphic ⇒ real-`C^n`, pointwise (`n` arbitrary, including `ω` and `∞`). -/
theorem contMDiffAt_real_of_holomorphicAt {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f x := by
  obtain ⟨hc, ha⟩ := contMDiffAt_iff_analyticAt_writtenInExtChartAt.1 hf
  exact contMDiffAt_real_iff_contDiffAt_writtenInExtChartAt.2
    ⟨hc, (ha.restrictScalars (𝕜 := ℝ)).contDiffAt⟩

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- Holomorphic ⇒ real-`C^n`, global. -/
theorem contMDiff_real_of_holomorphic {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f :=
  fun x => contMDiffAt_real_of_holomorphicAt (hf x)

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- Holomorphic ⇒ real-`C^n` on an open set. -/
theorem contMDiffOn_real_of_holomorphicOn {f : X → Y} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f s) : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f s :=
  fun _ hx => (contMDiffAt_real_of_holomorphicAt
    (hf.contMDiffAt (hs.mem_nhds hx))).contMDiffWithinAt

/-- Smooth partitions of unity subordinate to any open cover exist on a compact T2 surface
(restated on our surface as a compile-time guarantee for the PoU-based units). -/
theorem exists_smoothPartitionOfUnity [T2Space X] [CompactSpace X] {ι : Type*}
    (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : (univ : Set X) ⊆ ⋃ i, U i) :
    ∃ p : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X univ, p.IsSubordinate U :=
  SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ U ho hU

end RS
