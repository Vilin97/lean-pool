/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: local-multiplicity (CC4). Chart bridge: `inChartAt` and transitions.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Order.Filter.EventuallyConst

/-!
# Chart bridge for local multiplicity

* `RS.inChartAt F x : ℂ → ℂ` — the map `F : X → Y` read in the standard charts at `x` and `F x`,
  recentered to vanish at `chartAt ℂ x x`. This is the germ whose `analyticOrderAt` defines the
  local multiplicity (CC4).
* `RS.LMCompat.contMDiffAt_iff_analyticAt_inChartAt` — CC7 holomorphy bridge
  (`ContMDiffAt … ω ↔ ContinuousAt ∧ AnalyticAt` of the chart representative). Local copy;
  the canonical version is owned by surfaces-and-charts (request filed).
* `RS.eventuallyConst_inChartAt(_iff)` — local constancy transports through the charts.
* `RS.mem_contDiffGroupoid_iff_analytic` — `contDiffGroupoid ω 𝓘(ℂ)` membership is analyticity
  of both directions on source/target.
* `RS.analyticAt_transition` — maximal-atlas transitions are analytic with `deriv ≠ 0`.
* `RS.trans_mem_maximalAtlas` — the maximal atlas is stable under `≫ₕ` with a groupoid element.
* `RS.map_nhdsNE` — an `OpenPartialHomeomorph` maps `𝓝[≠] x` to `𝓝[≠] (e x)` on its source.
-/

open Filter Set OpenPartialHomeomorph
open scoped ContDiff Manifold Topology

namespace RS

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- `F` read in the standard charts at `x` and `F x`, recentered to vanish at `chartAt ℂ x x`.
Junk (from the charts' junk values) away from the chart sources; only its germ matters. -/
noncomputable def inChartAt (F : X → Y) (x : X) : ℂ → ℂ :=
  fun z ↦ chartAt ℂ (F x) (F ((chartAt ℂ x).symm z)) - chartAt ℂ (F x) (F x)

@[simp] theorem inChartAt_apply_chart (F : X → Y) (x : X) :
    inChartAt F x (chartAt ℂ x x) = 0 := by
  simp only [inChartAt, (chartAt ℂ x).left_inv (mem_chart_source ℂ x), sub_self]

/-- Recentering does not matter for analyticity of the chart representative. -/
theorem analyticAt_inChartAt_iff {F : X → Y} {x : X} :
    AnalyticAt ℂ (inChartAt F x) (chartAt ℂ x x) ↔
      AnalyticAt ℂ (⇑(chartAt ℂ (F x)) ∘ F ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  constructor
  · intro h
    have h3 : AnalyticAt ℂ (fun z ↦ inChartAt F x z + chartAt ℂ (F x) (F x))
        (chartAt ℂ x x) := h.add analyticAt_const
    exact h3.congr (Eventually.of_forall fun z ↦ by simp [inChartAt])
  · intro h
    exact h.sub analyticAt_const

namespace LMCompat

/-- CC7 holomorphy bridge (temporary local copy; canonical version owned by
surfaces-and-charts — see `docs/requests/surfaces-and-charts.md`). -/
theorem contMDiffAt_iff_analyticAt_inChartAt {F : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x ↔
      ContinuousAt F x ∧ AnalyticAt ℂ (inChartAt F x) (chartAt ℂ x x) := by
  rw [contMDiffAt_iff]
  refine and_congr_right fun _ ↦ ?_
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, Set.range_id,
    contDiffWithinAt_univ, Function.comp_apply, id_eq]
  rw [analyticAt_inChartAt_iff]
  exact ⟨fun h ↦ h.analyticAt, fun h ↦ h.contDiffAt⟩

end LMCompat

section EventuallyConst

/-- `EventuallyConst` at a neighborhood filter pins the constant to the value at the point. -/
theorem eventuallyConst_nhds_iff {α β : Type*} [TopologicalSpace α] {f : α → β} {x : α} :
    EventuallyConst f (𝓝 x) ↔ ∀ᶠ y in 𝓝 x, f y = f x := by
  have : Nonempty β := ⟨f x⟩
  rw [eventuallyConst_iff_exists_eventuallyEq]
  constructor
  · rintro ⟨c, hc⟩
    have hx : f x = c := hc.self_of_nhds
    filter_upwards [hc] with y hy using hy.trans hx.symm
  · intro h
    exact ⟨f x, h⟩

theorem eventuallyConst_inChartAt {F : X → Y} {x : X} (h : EventuallyConst F (𝓝 x)) :
    EventuallyConst (inChartAt F x) (𝓝 (chartAt ℂ x x)) := by
  have hmap : Filter.map (chartAt ℂ x).symm (𝓝 (chartAt ℂ x x)) = 𝓝 x :=
    (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)
  have h1 : EventuallyConst (F ∘ ⇑(chartAt ℂ x).symm) (𝓝 (chartAt ℂ x x)) := by
    change (Filter.map (F ∘ ⇑(chartAt ℂ x).symm) (𝓝 (chartAt ℂ x x))).Subsingleton
    rw [← Filter.map_map, hmap]
    exact h
  exact h1.comp (fun y ↦ chartAt ℂ (F x) y - chartAt ℂ (F x) (F x))

theorem eventuallyConst_inChartAt_iff {F : X → Y} {x : X} (hFc : ContinuousAt F x) :
    EventuallyConst (inChartAt F x) (𝓝 (chartAt ℂ x x)) ↔ EventuallyConst F (𝓝 x) := by
  refine ⟨fun h ↦ ?_, eventuallyConst_inChartAt⟩
  rw [eventuallyConst_nhds_iff] at h ⊢
  simp only [inChartAt_apply_chart] at h
  -- pull the eventual vanishing back through the chart at `x`
  have hx : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hmap : Filter.map (chartAt ℂ x) (𝓝 x) = 𝓝 (chartAt ℂ x x) :=
    (chartAt ℂ x).map_nhds_eq hx
  have h2 : ∀ᶠ y in 𝓝 x, inChartAt F x (chartAt ℂ x y) = 0 := by
    rw [← hmap] at h; exact h
  have hsrc : ∀ᶠ y in 𝓝 x, (chartAt ℂ x).symm (chartAt ℂ x y) = y :=
    (chartAt ℂ x).eventually_left_inverse hx
  have hFsrc : ∀ᶠ y in 𝓝 x, F y ∈ (chartAt ℂ (F x)).source :=
    hFc.preimage_mem_nhds ((chartAt ℂ (F x)).open_source.mem_nhds (mem_chart_source ℂ (F x)))
  filter_upwards [h2, hsrc, hFsrc] with y h2y hsy hFy
  -- `chartAt (F x) (F y) = chartAt (F x) (F x)`, and the chart is injective on its source
  rw [inChartAt, hsy, sub_eq_zero] at h2y
  exact (chartAt ℂ (F x)).injOn hFy (mem_chart_source ℂ (F x)) h2y

end EventuallyConst

section Transitions

/-- `contDiffGroupoid ω 𝓘(ℂ)` membership is analyticity of both directions. -/
theorem mem_contDiffGroupoid_iff_analytic {Φ : OpenPartialHomeomorph ℂ ℂ} :
    Φ ∈ contDiffGroupoid ω 𝓘(ℂ) ↔
      AnalyticOnNhd ℂ Φ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun z hz ↦ (h1.contDiffAt (Φ.open_source.mem_nhds hz)).analyticAt,
      fun z hz ↦ (h2.contDiffAt (Φ.open_target.mem_nhds hz)).analyticAt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun z hz ↦ (h1 z hz).contDiffAt.contDiffWithinAt,
      fun z hz ↦ (h2 z hz).contDiffAt.contDiffWithinAt⟩

/-- Transitions between maximal-atlas charts are analytic (one direction). -/
theorem analyticAt_transition_fun {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    {x : X} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    AnalyticAt ℂ (⇑e' ∘ ⇑e.symm) (e x) := by
  have hmem : e.symm ≫ₕ e' ∈ contDiffGroupoid ω 𝓘(ℂ) :=
    IsManifold.compatible_of_mem_maximalAtlas he he'
  rw [mem_contDiffGroupoid_iff_analytic] at hmem
  have hxmem : e x ∈ (e.symm ≫ₕ e').source := by
    rw [trans_source]
    exact ⟨e.map_source hx, by
      simp only [mem_preimage]
      rw [e.left_inv hx]; exact hx'⟩
  exact hmem.1 (e x) hxmem

/-- Transitions between maximal-atlas charts are analytic with nonvanishing derivative. -/
theorem analyticAt_transition {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    {x : X} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    AnalyticAt ℂ (⇑e' ∘ ⇑e.symm) (e x) ∧ deriv (⇑e' ∘ ⇑e.symm) (e x) ≠ 0 := by
  have hτ : AnalyticAt ℂ (⇑e' ∘ ⇑e.symm) (e x) := analyticAt_transition_fun he he' hx hx'
  have hσ : AnalyticAt ℂ (⇑e ∘ ⇑e'.symm) (e' x) := analyticAt_transition_fun he' he hx' hx
  refine ⟨hτ, fun hzero ↦ ?_⟩
  -- the inverse transition composes to the identity near `e x`
  have hid : (⇑e ∘ ⇑e'.symm) ∘ (⇑e' ∘ ⇑e.symm) =ᶠ[𝓝 (e x)] id := by
    have h1 : e.target ∈ 𝓝 (e x) := e.open_target.mem_nhds (e.map_source hx)
    have h2 : ⇑e.symm ⁻¹' e'.source ∈ 𝓝 (e x) := by
      apply (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
      rw [e.left_inv hx]
      exact e'.open_source.mem_nhds hx'
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [Function.comp_apply, id_eq]
    rw [e'.left_inv hz2, e.right_inv hz1]
  have hone : deriv ((⇑e ∘ ⇑e'.symm) ∘ (⇑e' ∘ ⇑e.symm)) (e x) = 1 := by
    rw [hid.deriv_eq, deriv_id]
  have hτx : (⇑e' ∘ ⇑e.symm) (e x) = e' x := by
    simp only [Function.comp_apply]
    rw [e.left_inv hx]
  have hchain : deriv ((⇑e ∘ ⇑e'.symm) ∘ (⇑e' ∘ ⇑e.symm)) (e x)
      = deriv (⇑e ∘ ⇑e'.symm) ((⇑e' ∘ ⇑e.symm) (e x)) * deriv (⇑e' ∘ ⇑e.symm) (e x) := by
    refine deriv_comp (e x) ?_ hτ.differentiableAt
    rw [hτx]
    exact hσ.differentiableAt
  rw [hchain, hzero, mul_zero] at hone
  exact zero_ne_one hone

/-- Trans with a groupoid element stays in the maximal atlas (upstreamable helper). -/
theorem trans_mem_maximalAtlas {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {Φ : OpenPartialHomeomorph ℂ ℂ}
    (hΦ : Φ ∈ contDiffGroupoid ω 𝓘(ℂ)) :
    e ≫ₕ Φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := by
  intro c hc
  obtain ⟨h1, h2⟩ := he c hc
  constructor
  · rw [trans_symm_eq_symm_trans_symm, trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℂ)).trans ((contDiffGroupoid ω 𝓘(ℂ)).symm hΦ) h1
  · rw [← trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℂ)).trans h2 hΦ

end Transitions

/-- An `OpenPartialHomeomorph` maps punctured neighborhoods of source points to punctured
neighborhoods. -/
theorem map_nhdsNE {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : OpenPartialHomeomorph α β) {x : α} (hx : x ∈ e.source) :
    Filter.map e (𝓝[≠] x) = 𝓝[≠] (e x) := by
  rw [e.map_nhdsWithin_eq hx]
  apply nhdsWithin_eq_nhdsWithin (e.map_source hx) e.open_target
  ext y
  simp only [mem_inter_iff, mem_image, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨z, ⟨hz, hzx⟩, rfl⟩, hyt⟩
    exact ⟨fun h ↦ hzx (e.injOn hz hx h), hyt⟩
  · rintro ⟨hyx, hyt⟩
    refine ⟨⟨e.symm y, ⟨e.map_target hyt, ?_⟩, e.right_inv hyt⟩, hyt⟩
    intro h
    exact hyx (by rw [← e.right_inv hyt, h])

end RS
