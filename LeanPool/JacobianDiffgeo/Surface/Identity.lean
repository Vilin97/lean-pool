/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Surface.Bridges
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Identity theorem, isolated fibers, open mapping, surjectivity

Unit: surfaces-and-charts (`docs/design/surfaces-and-charts.md` §3.4; Forster 1.11, 2.4, 2.7).

For holomorphic maps between Riemann surfaces:

* `map_extChartAt_nhdsNE`, `nhdsNE_neBot`: punctured-neighborhood transport through charts;
* `eventually_eq_or_eventually_ne`: local dichotomy for a pair of maps agreeing at a point;
  `eventually_eq_const_or_eventually_ne`: locally constant value or isolated in its fiber;
* `eq_of_frequently_eq`: the **identity theorem** on a connected surface;
  `eq_of_eqOn_of_accPt`: accumulation-set formulation (consumed by meromorphic-and-divisors);
* `eventually_ne_of_not_const`: nonconstant holomorphic maps have **isolated fibers**;
* `isOpenMap_of_not_const`: nonconstant holomorphic maps are **open** (Forster 2.4);
* `surjective_of_not_const`: nonconstant + compact source + connected target ⇒ surjective
  (Forster 2.7; consumed by mapping-degree and the headline).
-/

open scoped ContDiff Manifold
open Set Filter Topology IsManifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ### Punctured-neighborhood transport through charts -/

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The preferred chart carries the punctured neighborhood filter of `x` to the punctured
neighborhood filter of `extChartAt 𝓘(ℂ) x x`. -/
theorem map_extChartAt_nhdsNE (x : X) :
    Filter.map (extChartAt 𝓘(ℂ) x) (𝓝[≠] x) = 𝓝[≠] (extChartAt 𝓘(ℂ) x x) := by
  have h1 : Filter.map (chartAt ℂ x) (𝓝[≠] x) =
      𝓝[(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ {x}ᶜ)] (chartAt ℂ x x) :=
    (chartAt ℂ x).map_nhdsWithin_eq (mem_chart_source ℂ x) _
  have h2 : 𝓝[(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ {x}ᶜ)] (chartAt ℂ x x) =
      𝓝[≠] (chartAt ℂ x x) := by
    rw [nhdsWithin_eq_iff_eventuallyEq, Filter.eventuallyEq_set]
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with w hw
    constructor
    · rintro ⟨z, ⟨hzs, hzx⟩, rfl⟩ h
      exact hzx ((chartAt ℂ x).injOn hzs (mem_chart_source ℂ x) h)
    · intro hw'
      refine ⟨(chartAt ℂ x).symm w, ⟨(chartAt ℂ x).map_target hw, fun h => hw' ?_⟩,
        (chartAt ℂ x).right_inv hw⟩
      simp only [mem_singleton_iff] at h ⊢
      rw [← (chartAt ℂ x).right_inv hw, h]
  exact h1.trans h2

omit [IsManifold 𝓘(ℂ) ω X] in
/-- No point of a Riemann surface is isolated. -/
instance nhdsNE_neBot (x : X) : (𝓝[≠] x).NeBot :=
  Filter.NeBot.of_map (m := (extChartAt 𝓘(ℂ) x : X → ℂ))
    (by rw [map_extChartAt_nhdsNE x]; infer_instance)

/-! ### The local dichotomy -/

private theorem analyticAt_pair {f g : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x)
    (hfg : f x = g x) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
        (extChartAt 𝓘(ℂ) x x) ∧
      AnalyticAt ℂ (extChartAt 𝓘(ℂ) (f x) ∘ g ∘ (extChartAt 𝓘(ℂ) x).symm)
        (extChartAt 𝓘(ℂ) x x) := by
  constructor
  · exact (contMDiffAt_iff_analyticAt_writtenInExtChartAt.1 hf).2
  · have hg' := (contMDiffAt_iff_of_mem_source (mem_chart_source ℂ x)
      (show g x ∈ (chartAt ℂ (f x)).source by
        rw [← hfg]; exact mem_chart_source ℂ (f x))).1 hg
    rw [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] at hg'
    exact hg'.2.analyticAt

/-- Local dichotomy for a pair of holomorphic maps agreeing at `x` (no connectedness, no T2):
they agree near `x`, or they differ everywhere near (but not at) `x`. -/
theorem eventually_eq_or_eventually_ne {f g : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x)
    (hfg : f x = g x) :
    (∀ᶠ z in 𝓝 x, f z = g z) ∨ (∀ᶠ z in 𝓝[≠] x, f z ≠ g z) := by
  obtain ⟨hF, hG⟩ := analyticAt_pair hf hg hfg
  have hgmem : (extChartAt 𝓘(ℂ) (f x)).source ∈ 𝓝 (g x) := by
    rw [← hfg]; exact extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x)
  rcases hF.eventually_eq_or_eventually_ne hG with h | h
  · left
    rw [← map_extChartAt_nhds_of_boundaryless x, Filter.eventually_map] at h
    filter_upwards [h, extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x,
      hf.continuousAt.eventually_mem (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x)),
      hg.continuousAt.eventually_mem hgmem] with z hz hzs hzf hzg
    have h1 : (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x z) = z :=
      PartialEquiv.left_inv _ hzs
    refine (extChartAt 𝓘(ℂ) (f x)).injOn hzf hzg ?_
    simpa only [Function.comp_apply, h1] using hz
  · right
    rw [← map_extChartAt_nhdsNE x, Filter.eventually_map] at h
    have hsrc : ∀ᶠ z in 𝓝[≠] x, z ∈ (extChartAt 𝓘(ℂ) x).source :=
      eventually_nhdsWithin_of_eventually_nhds (extChartAt_source_mem_nhds x)
    filter_upwards [h, hsrc] with z hz hzs heq
    have h1 : (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x z) = z :=
      PartialEquiv.left_inv _ hzs
    exact hz (by simp only [Function.comp_apply, h1, heq])

/-- Local dichotomy at a point: locally constant value or isolated in its fiber. -/
theorem eventually_eq_const_or_eventually_ne {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    (∀ᶠ z in 𝓝 x, f z = f x) ∨ (∀ᶠ z in 𝓝[≠] x, f z ≠ f x) :=
  eventually_eq_or_eventually_ne hf contMDiffAt_const rfl

/-! ### The identity theorem -/

variable [T2Space Y]   -- ℂ qualifies, so all lemmas below apply to `f g : X → ℂ`

/-- Local identity: holomorphic maps agreeing frequently near a point agree near it. -/
theorem eventuallyEq_of_frequently_eq {f g : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x)
    (hfg : ∃ᶠ z in 𝓝[≠] x, f z = g z) : f =ᶠ[𝓝 x] g := by
  have hx : f x = g x :=
    tendsto_nhds_unique_of_frequently_eq
      (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hfg
  rcases eventually_eq_or_eventually_ne hf hg hx with h | h
  · exact h
  · exact absurd (hfg.and_eventually h).exists (by simp)

/-- **Identity theorem** on a connected surface (Forster 1.11-adjacent): holomorphic maps
agreeing frequently near a point (equivalently: on a set accumulating at a point) are equal. -/
theorem eq_of_frequently_eq [PreconnectedSpace X] {f g : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) {z₀ : X}
    (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : f = g := by
  set S : Set X := {x | f =ᶠ[𝓝 x] g} with hS
  have hopen : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    exact (Filter.Eventually.eventually_nhds hx :)
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    by_contra hnot
    apply hx
    have hfreq : ∃ᶠ y in 𝓝 x, y ∈ S := by
      by_contra hf'
      exact hnot (Filter.not_frequently.1 hf' :)
    have hfreq' : ∃ᶠ y in 𝓝[≠] x, f y = g y := by
      rw [frequently_nhdsWithin_iff]
      refine hfreq.mono fun y hy => ⟨hy.eq_of_nhds, fun h => hx ?_⟩
      rw [mem_singleton_iff] at h
      exact h ▸ hy
    exact eventuallyEq_of_frequently_eq (hf x) (hg x) hfreq'
  have hz₀S : z₀ ∈ S := eventuallyEq_of_frequently_eq (hf z₀) (hg z₀) hfg
  have huniv : S = univ :=
    (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨z₀, hz₀S⟩)
  funext x
  exact Filter.EventuallyEq.eq_of_nhds (huniv ▸ Set.mem_univ x : x ∈ S)

/-- Accumulation-set formulation (the one meromorphic-and-divisors quotes for `div` support). -/
theorem eq_of_eqOn_of_accPt [PreconnectedSpace X] {f g : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    {s : Set X} {z₀ : X} (hz₀ : AccPt z₀ (𝓟 s)) (heq : EqOn f g s) : f = g := by
  refine eq_of_frequently_eq hf hg (z₀ := z₀) ?_
  exact (accPt_iff_frequently_nhdsNE.1 hz₀).mono fun z hz => heq hz

/-! ### Isolated fibers, open mapping, surjectivity -/

/-- Nonconstant holomorphic maps have **isolated fibers**. -/
theorem eventually_ne_of_not_const [PreconnectedSpace X] {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ y, ∀ x, f x = y) (x : X) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
  rcases eventually_eq_const_or_eventually_ne (hf x) with h | h
  · exfalso
    apply hne
    refine ⟨f x, fun z => congrFun (eq_of_frequently_eq hf contMDiff_const (z₀ := x) ?_) z⟩
    exact (h.filter_mono (nhdsWithin_le_nhds (s := {x}ᶜ))).frequently
  · exact h

/-- Nonconstant holomorphic maps are **open** (Forster 2.4 on surfaces). -/
theorem isOpenMap_of_not_const [PreconnectedSpace X] {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ y, ∀ x, f x = y) : IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  have hG : AnalyticAt ℂ (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
      (extChartAt 𝓘(ℂ) x x) := (contMDiffAt_iff_analyticAt_writtenInExtChartAt.1 (hf x)).2
  have hGx : (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) =
      extChartAt 𝓘(ℂ) (f x) (f x) := by
    simp only [Function.comp_apply, extChartAt_to_inv]
  rcases hG.eventually_constant_or_nhds_le_map_nhds with h | h
  · -- constant branch: contradicts isolated fibers
    exfalso
    rw [← map_extChartAt_nhds_of_boundaryless x, Filter.eventually_map] at h
    have hev : ∀ᶠ z in 𝓝 x, f z = f x := by
      filter_upwards [h, extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x,
        (hf x).continuousAt.eventually_mem
          (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x))] with z hz hzs hzf
      have h1 : (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x z) = z :=
        PartialEquiv.left_inv _ hzs
      refine (extChartAt 𝓘(ℂ) (f x)).injOn hzf (mem_extChartAt_source (f x)) ?_
      rw [hGx] at hz
      simpa only [Function.comp_apply, h1] using hz
    have hne' := eventually_ne_of_not_const hf hne x
    exact absurd ((((hev.filter_mono (nhdsWithin_le_nhds
      (s := {x}ᶜ))).frequently).and_eventually hne').exists) (by simp)
  · -- open branch: conjugate the filter inequality through the charts
    rw [hGx] at h
    calc 𝓝 (f x)
        = Filter.map (chartAt ℂ (f x)).symm (𝓝 (extChartAt 𝓘(ℂ) (f x) (f x))) := by
          have hmem : (chartAt ℂ (f x)) (f x) ∈ (chartAt ℂ (f x)).symm.source := by
            rw [OpenPartialHomeomorph.symm_source]
            exact (chartAt ℂ (f x)).map_source (mem_chart_source ℂ (f x))
          have h2 := (chartAt ℂ (f x)).symm.map_nhds_eq hmem
          rw [show (chartAt ℂ (f x)).symm ((chartAt ℂ (f x)) (f x)) = f x from
            (chartAt ℂ (f x)).left_inv (mem_chart_source ℂ (f x))] at h2
          exact h2.symm
      _ ≤ Filter.map (chartAt ℂ (f x)).symm
            (Filter.map (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
              (𝓝 (extChartAt 𝓘(ℂ) x x))) := Filter.map_mono h
      _ = Filter.map ((chartAt ℂ (f x)).symm ∘
            (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm))
            (Filter.map (extChartAt 𝓘(ℂ) x) (𝓝 x)) := by
          rw [Filter.map_map, map_extChartAt_nhds_of_boundaryless x]
      _ = Filter.map ((chartAt ℂ (f x)).symm ∘
            (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) ∘ extChartAt 𝓘(ℂ) x)
            (𝓝 x) := by rw [Filter.map_map]; rfl
      _ = Filter.map f (𝓝 x) := by
          refine Filter.map_congr ?_
          filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x,
            (hf x).continuousAt.eventually_mem
              (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x))] with z hzs hzf
          have h1 : (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x z) = z :=
            PartialEquiv.left_inv _ hzs
          simp only [Function.comp_apply, h1]
          exact PartialEquiv.left_inv (extChartAt 𝓘(ℂ) (f x)) hzf

/-- Forster 2.7: nonconstant + compact source + connected target ⇒ surjective (and the
target is then compact). Consumed by mapping-degree and the headline. -/
theorem surjective_of_not_const [ConnectedSpace X] [CompactSpace X] [PreconnectedSpace Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ y, ∀ x, f x = y) :
    Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := (isOpenMap_of_not_const hf hne).isOpen_range
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  exact Set.range_eq_univ.1
    (IsClopen.eq_univ ⟨hclosed, hopen⟩ (Set.range_nonempty f))

end RS
