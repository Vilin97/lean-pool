/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Charted-space kit, generalized to an arbitrary `NormedSpace ℂ` codomain

Unit: jacobian-construction (`docs/design/jacobian-construction.md` §4.2.1). Surface's
`Jacobian/Surface/ChartedSpaceKit.lean` hardcodes the chart codomain to literal `ℂ`; this file is
a **textually near-identical generalization** to an arbitrary `{E : Type*} [NormedAddCommGroup E]
[NormedSpace ℂ E]` (needed for `V := Fin n → ℂ`, the ambient space of the Jacobian torus). A
non-blocking request to generalize the upstream file instead is filed in
`docs/requests/surfaces-and-charts.md`; the two are `rfl`-compatible (identical proofs).

Namespace `RS` (Compat section, primed names to avoid clashing with Surface's originals):

* `chartedSpaceOfFamily'`: package a covering family `c : ι → OpenPartialHomeomorph Z E` as a
  `ChartedSpace E Z`;
* `isManifold_of_analyticOn_transitions'`: an atlas with `ℂ`-analytic transition maps is an
  `ω`-manifold (model `𝓘(ℂ, E)`);
* `isManifold_of_family'`: family version.
-/

open scoped ContDiff Manifold
open Set

namespace RS

variable {Z : Type*} [TopologicalSpace Z] {ι : Type*}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Package a covering family of `E`-valued charts as a `ChartedSpace`. -/
@[reducible] def chartedSpaceOfFamily' (c : ι → OpenPartialHomeomorph Z E) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source) : ChartedSpace E Z where
  atlas := Set.range c
  chartAt z := c (idx z)
  mem_chart_source := h
  chart_mem_atlas _ := Set.mem_range_self _

omit [NormedSpace ℂ E] in
@[simp] theorem chartedSpaceOfFamily'_chartAt (c : ι → OpenPartialHomeomorph Z E)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) (z : Z) :
    @chartAt E _ Z _ (chartedSpaceOfFamily' c idx h) z = c (idx z) := rfl

omit [NormedSpace ℂ E] in
@[simp] theorem chartedSpaceOfFamily'_atlas (c : ι → OpenPartialHomeomorph Z E)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) :
    @atlas E _ Z _ (chartedSpaceOfFamily' c idx h) = Set.range c := rfl

/-- An atlas with `ℂ`-analytic transition maps is an `ω`-manifold (model `𝓘(ℂ, E)`). -/
theorem isManifold_of_analyticOn_transitions' [ChartedSpace E Z]
    (h : ∀ e ∈ atlas E Z, ∀ e' ∈ atlas E Z,
      AnalyticOnNhd ℂ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    IsManifold 𝓘(ℂ, E) ω Z := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have hs : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  simpa using (contDiffOn_omega_iff_analyticOn hs.uniqueDiffOn).2 ((h e he e' he').analyticOn)

/-- Family version: pairwise-analytic transitions of the generating family suffice. -/
theorem isManifold_of_family' (c : ι → OpenPartialHomeomorph Z E) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source)
    (htrans : ∀ i j, AnalyticOnNhd ℂ ((c i).symm ≫ₕ c j) ((c i).symm ≫ₕ c j).source) :
    @IsManifold ℂ _ E _ _ E _ 𝓘(ℂ, E) ω Z _ (chartedSpaceOfFamily' c idx h) := by
  let : ChartedSpace E Z := chartedSpaceOfFamily' c idx h
  refine isManifold_of_analyticOn_transitions' ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact htrans i j

end RS
