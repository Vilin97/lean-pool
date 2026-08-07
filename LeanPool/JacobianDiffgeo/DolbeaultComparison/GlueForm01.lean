/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Dbar.Operator

/-!
# `DbarGlueData`: the Mittag-Leffler-style gluing atom
(`Jacobian/DolbeaultComparison/GlueForm01.lean`)

Unit: dolbeault-comparison (`docs/design/dolbeault-comparison.md` §4.2/§6.1). The reusable
gluing atom of the comparison: local smooth functions with holomorphic discrepancies on a
chart-subordinate cover determine a UNIQUE global `Form01` solving `dbaru_i = ω` on each piece.

* `Form01.ext_center` [Compat]: a `Form01` is determined by its center-coefficients.
* `DbarGlueData`: the gluing data (member cover, per-member center/local solution, holomorphic
  discrepancies on overlaps).
* `DbarGlueData.form`: the glued `(0,1)`-form (via `Form01.ofCoeffs`/`Form01CoeffData`).
* `DbarGlueData.isDbarOn_form`, `DbarGlueData.form_unique`.
-/

open scoped ContDiff Manifold
open Set IsManifold TopologicalSpace

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `Form01.ext_center` (Compat, D4) -/

/-- Compat (candidate for upstreaming to dbar): a `Form01` is determined by its
center-coefficients. From the `compat` field applied at the pair `(p, x)` (`p` the base point of
`z` in `x`'s preferred chart) and `Form01.ext`. -/
theorem Form01.ext_center {η η' : Form01 X}
    (h : ∀ x : X, η.coeffAt x (chartAt ℂ x x) = η'.coeffAt x (chartAt ℂ x x)) : η = η' := by
  apply Form01.ext
  intro x z hz
  set p := (chartAt ℂ x).symm z with hp_def
  have hp_mem : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hz_eq : chartAt ℂ x p = z := (chartAt ℂ x).right_inv hz
  have hmem : z ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ p).source ∩ (chartAt ℂ x).source) :=
    ⟨p, ⟨mem_chart_source ℂ p, hp_mem⟩, hz_eq⟩
  rw [η.compat p x z hmem, η'.compat p x z hmem]
  congr 1
  exact h p

/-! ### Compat: a local repeat of `Jacobian.Dbar.Operator`'s private
`contDiffOn_comp_chartAt_symm_of_contMDiffOn` (needed here too, and not exported there). -/

private theorem contDiffOn_comp_chart_symm_of_contMDiffOn {u : X → ℂ} {s : Set X}
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u s) (x₀ : X) :
    ContDiffOn ℝ ∞ (u ∘ ⇑(chartAt ℂ x₀).symm) (⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source)) := by
  have hf' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑(chartAt ℂ x₀).symm) (chartAt ℂ x₀).target := by
    have h1 := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (n := (∞ : ℕ∞ω)) x₀
    have htarget : (extChartAt 𝓘(ℝ, ℂ) x₀).target = (chartAt ℂ x₀).target := by simp
    rwa [htarget] at h1
  have hsub : ⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source) ⊆ (chartAt ℂ x₀).target := by
    rintro w ⟨y, ⟨_, hy⟩, rfl⟩; exact (chartAt ℂ x₀).map_source hy
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (u ∘ ⇑(chartAt ℂ x₀).symm)
      (⇑(chartAt ℂ x₀) '' (s ∩ (chartAt ℂ x₀).source)) := by
    apply hu.comp (hf'.mono hsub)
    rintro w ⟨y, ⟨hys, hyx₀⟩, rfl⟩
    simp only [Set.mem_preimage, (chartAt ℂ x₀).left_inv hyx₀]
    exact hys
  exact contMDiffOn_iff_contDiffOn.1 hcomp

/-! ### `DbarGlueData` -/

/-- Local `dbar`-data: smooth local functions, a chart-subordinate cover, holomorphic discrepancies.
The single gluing atom of the comparison (D4). -/
structure DbarGlueData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  /-- The number of members. -/
  n : ℕ
  /-- The cover members. -/
  V : Fin n → Opens X
  covers : ∀ x : X, ∃ i, x ∈ V i
  /-- The chart center for each member. -/
  center : Fin n → X
  subChart : ∀ i, (V i : Set X) ⊆ (chartAt ℂ (center i)).source
  /-- The local `dbar`-solution on each member. -/
  u : Fin n → X → ℂ
  smoothOn : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (u i) (V i)
  holoSub : ∀ i j, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (u i - u j) ↑(V i ⊓ V j)

namespace DbarGlueData

variable (d : DbarGlueData X)

/-- The data chart at member `i`: the preferred chart at the center, restricted to the member. -/
def chart (i : Fin d.n) : OpenPartialHomeomorph X ℂ := (chartAt ℂ (d.center i)).restr (d.V i)

theorem chart_mem_maximalAtlas (i : Fin d.n) :
    d.chart i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
  restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas (d.center i)) (d.V i).isOpen

theorem chart_source (i : Fin d.n) : (d.chart i).source = (d.V i : Set X) := by
  rw [chart, (chartAt ℂ (d.center i)).restr_source' (d.V i : Set X) (d.V i).isOpen,
    Set.inter_eq_right.2 (d.subChart i)]

theorem coe_chart (i : Fin d.n) : ⇑(d.chart i) = ⇑(chartAt ℂ (d.center i)) := rfl

theorem coe_chart_symm (i : Fin d.n) : ⇑(d.chart i).symm = ⇑(chartAt ℂ (d.center i)).symm := rfl

theorem mem_chart_source_of_mem_V {i : Fin d.n} {x : X} (hx : x ∈ d.V i) :
    x ∈ (d.chart i).source := by rw [chart_source]; exact hx

/-- Real-smoothness of the chart representative of `u i`, at the data chart's own point. -/
theorem contDiffAt_u_comp_chart_symm (i : Fin d.n) {x : X} (hx : x ∈ d.V i) :
    ContDiffAt ℝ ∞ (d.u i ∘ ⇑(d.chart i).symm) (d.chart i x) := by
  have h := contDiffOn_comp_chart_symm_of_contMDiffOn (d.smoothOn i) (d.center i)
  rw [Set.inter_eq_left.2 (d.subChart i)] at h
  exact h.contDiffAt
    (((chartAt ℂ (d.center i)).isOpen_image_of_subset_source (d.V i).isOpen (d.subChart i)).mem_nhds
      (Set.mem_image_of_mem _ hx))

/-- Real-differentiability of `u i`'s chart-`i` representative, transported through the
transition to ANY other maximal-atlas chart `e` whose source contains the point. -/
theorem differentiableAt_u_comp_chart_symm_transition (i : Fin d.n) {x : X} (hx : x ∈ d.V i)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hex : x ∈ e.source) : DifferentiableAt ℝ (d.u i ∘ ⇑e.symm) (e x) := by
  have hxi_src : x ∈ (d.chart i).source := d.mem_chart_source_of_mem_V hx
  have hτ_diff : DifferentiableAt ℂ (⇑(d.chart i) ∘ ⇑e.symm) (e x) :=
    (analyticAt_trans (d.chart_mem_maximalAtlas i) he (e.map_source hex)
      (by rw [e.left_inv hex]; exact hxi_src)).differentiableAt
  have heqpt : (⇑(d.chart i) ∘ ⇑e.symm) (e x) = d.chart i x := by
    simp only [Function.comp_apply, e.left_inv hex]
  have hui_diff : DifferentiableAt ℝ (d.u i ∘ ⇑(d.chart i).symm) ((⇑(d.chart i) ∘ ⇑e.symm) (e x)) :=
      by
    rw [heqpt]
    exact (d.contDiffAt_u_comp_chart_symm i hx).differentiableAt (by norm_num)
  have hcomp : DifferentiableAt ℝ ((d.u i ∘ ⇑(d.chart i).symm) ∘ (⇑(d.chart i) ∘ ⇑e.symm)) (e x) :=
    hui_diff.comp (e x) (hτ_diff.restrictScalars ℝ)
  have heqfun : ((d.u i ∘ ⇑(d.chart i).symm) ∘ (⇑(d.chart i) ∘ ⇑e.symm)) =ᶠ[nhds (e x)]
      (d.u i ∘ ⇑e.symm) := by
    have hWopen : IsOpen (⇑e '' ((d.chart i).source ∩ e.source)) :=
      e.isOpen_image_of_subset_source ((d.chart i).open_source.inter e.open_source)
        inter_subset_right
    have hzW : e x ∈ ⇑e '' ((d.chart i).source ∩ e.source) := ⟨x, ⟨hxi_src, hex⟩, rfl⟩
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, ⟨hqi, hqe⟩, rfl⟩ := hw
    simp only [Function.comp_apply, e.left_inv hqe, (d.chart i).left_inv hqi]
  exact hcomp.congr_of_eventuallyEq heqfun.symm

/-- The `(0,1)`-transport identity: `wirtingerDbar` of `u i`'s representative in ANY maximal-atlas
chart `e` (whose source contains the point) is the `conj`-transition of its value in the data
chart `i`. Used both for `Form01CoeffData.compat` (`e := chart j`) and `isDbarOn_form`
(`e := chartAt x`). -/
theorem wirtingerDbar_u_transport (i : Fin d.n) {x : X} (hx : x ∈ d.V i)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hex : x ∈ e.source) :
    wirtingerDbar (d.u i ∘ ⇑e.symm) (e x) =
      (starRingEnd ℂ) (deriv (⇑(d.chart i) ∘ ⇑e.symm) (e x)) *
        wirtingerDbar (d.u i ∘ ⇑(d.chart i).symm) (d.chart i x) := by
  have hxi_src : x ∈ (d.chart i).source := d.mem_chart_source_of_mem_V hx
  have hτ_diff : DifferentiableAt ℂ (⇑(d.chart i) ∘ ⇑e.symm) (e x) :=
    (analyticAt_trans (d.chart_mem_maximalAtlas i) he (e.map_source hex)
      (by rw [e.left_inv hex]; exact hxi_src)).differentiableAt
  have heqpt : (⇑(d.chart i) ∘ ⇑e.symm) (e x) = d.chart i x := by
    simp only [Function.comp_apply, e.left_inv hex]
  have hui_diff : DifferentiableAt ℝ (d.u i ∘ ⇑(d.chart i).symm) ((⇑(d.chart i) ∘ ⇑e.symm) (e x)) :=
      by
    rw [heqpt]
    exact (d.contDiffAt_u_comp_chart_symm i hx).differentiableAt (by norm_num)
  have hchain := wirtingerDbar_comp_differentiableAt (f := d.u i ∘ ⇑(d.chart i).symm)
    (τ := ⇑(d.chart i) ∘ ⇑e.symm) (z := e x) hui_diff hτ_diff
  rw [heqpt] at hchain
  have heqfun : ((d.u i ∘ ⇑(d.chart i).symm) ∘ (⇑(d.chart i) ∘ ⇑e.symm)) =ᶠ[nhds (e x)]
      (d.u i ∘ ⇑e.symm) := by
    have hWopen : IsOpen (⇑e '' ((d.chart i).source ∩ e.source)) :=
      e.isOpen_image_of_subset_source ((d.chart i).open_source.inter e.open_source)
        inter_subset_right
    have hzW : e x ∈ ⇑e '' ((d.chart i).source ∩ e.source) := ⟨x, ⟨hxi_src, hex⟩, rfl⟩
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, ⟨hqi, hqe⟩, rfl⟩ := hw
    simp only [Function.comp_apply, e.left_inv hqe, (d.chart i).left_inv hqi]
  rw [← wirtingerDbar_congr_nhds _ _ (e x) heqfun]
  exact hchain

/-- The `Form01CoeffData` underlying the glued form (design §6.1). -/
noncomputable def coeffData : Form01CoeffData X (Fin d.n) where
  chart := d.chart
  mem_maximalAtlas := d.chart_mem_maximalAtlas
  exists_mem x := by
    obtain ⟨i, hi⟩ := d.covers x
    exact ⟨i, d.mem_chart_source_of_mem_V hi⟩
  coeff i := wirtingerDbar (d.u i ∘ ⇑(d.chart i).symm)
  contDiffOn i := by
    apply contDiffOn_wirtingerDbar _ (d.chart i).open_target
    intro z hz
    have hx : (d.chart i).symm z ∈ d.V i := by
      change (d.chart i).symm z ∈ (d.V i : Set X)
      rw [← d.chart_source i]; exact (d.chart i).map_target hz
    have h := d.contDiffAt_u_comp_chart_symm i hx
    rw [(d.chart i).right_inv hz] at h
    exact h.contDiffWithinAt
  compat i j x hx := by
    rw [d.chart_source i, d.chart_source j] at hx
    obtain ⟨hxi, hxj⟩ := hx
    show wirtingerDbar (d.u j ∘ ⇑(d.chart j).symm) (d.chart j x) =
      (starRingEnd ℂ) (deriv (⇑(d.chart i) ∘ ⇑(d.chart j).symm) (d.chart j x)) *
        wirtingerDbar (d.u i ∘ ⇑(d.chart i).symm) (d.chart i x)
    have hxij : x ∈ (d.V i ⊓ d.V j : Opens X) := ⟨hxi, hxj⟩
    have hhol : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (d.u j - d.u i) (d.V i ⊓ d.V j : Opens X) := by
      have hneg := (d.holoSub i j).neg
      have heq : (fun y => -(d.u i - d.u j) y) = d.u j - d.u i := by
        funext y; simp only [Pi.sub_apply]; ring
      rwa [heq] at hneg
    have hxj_src : x ∈ (chartAt ℂ (d.center j)).source := d.subChart j hxj
    have hCM : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (d.u j - d.u i) x :=
      hhol.contMDiffAt ((d.V i ⊓ d.V j : Opens X).isOpen.mem_nhds hxij)
    have hAn : AnalyticAt ℂ ((d.u j - d.u i) ∘ ⇑(chartAt ℂ (d.center j)).symm)
        (chartAt ℂ (d.center j) x) :=
      (contMDiffAt_iff_analyticAt_of_mem_source (chart_mem_atlas ℂ (d.center j)) hxj_src).1 hCM
    have hdiffC : DifferentiableAt ℂ ((d.u j - d.u i) ∘ ⇑(d.chart j).symm) (d.chart j x) :=
      hAn.differentiableAt
    have hzero : wirtingerDbar ((d.u j - d.u i) ∘ ⇑(d.chart j).symm) (d.chart j x) = 0 :=
      wirtingerDbar_eq_zero_of_differentiableAt _ _ hdiffC
    have hdecomp : d.u j ∘ ⇑(d.chart j).symm =
        ((d.u j - d.u i) ∘ ⇑(d.chart j).symm) + (d.u i ∘ ⇑(d.chart j).symm) := by
      funext w; simp
    have hdiffR1 : DifferentiableAt ℝ ((d.u j - d.u i) ∘ ⇑(d.chart j).symm) (d.chart j x) :=
      hdiffC.restrictScalars ℝ
    have hdiffR2 : DifferentiableAt ℝ (d.u i ∘ ⇑(d.chart j).symm) (d.chart j x) :=
      d.differentiableAt_u_comp_chart_symm_transition i hxi (d.chart j)
        (d.chart_mem_maximalAtlas j) (d.mem_chart_source_of_mem_V hxj)
    rw [hdecomp, wirtingerDbar_add _ _ _ hdiffR1 hdiffR2, hzero, zero_add]
    exact d.wirtingerDbar_u_transport i hxi (d.chart j) (d.chart_mem_maximalAtlas j)
      (d.mem_chart_source_of_mem_V hxj)

/-- The glued global `(0,1)`-form: `ω|V i = dbar(u i)` (design §6.1). -/
noncomputable def form : Form01 X := Form01.ofCoeffs d.coeffData

theorem isDbarOn_form (i : Fin d.n) : IsDbarOn (d.u i) d.form (d.V i) := by
  intro x hx
  have hxi_src : x ∈ (d.chart i).source := d.mem_chart_source_of_mem_V hx
  change wirtingerDbar (d.u i ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
    (Form01.ofCoeffs d.coeffData).coeffAt x (chartAt ℂ x x)
  rw [Form01.coeffAt_ofCoeffs d.coeffData hxi_src]
  exact d.wirtingerDbar_u_transport i hx (chartAt ℂ x) (IsManifold.chart_mem_maximalAtlas x)
    (mem_chart_source ℂ x)

/-- Uniqueness — every well-definedness question of the comparison reduces to this. -/
theorem form_unique {η : Form01 X} (h : ∀ i, IsDbarOn (d.u i) η (d.V i)) : η = d.form := by
  apply Form01.ext_center
  intro x
  obtain ⟨i, hi⟩ := d.covers x
  have h1 := h i x hi
  have h2 := d.isDbarOn_form i x hi
  rw [← h1]
  exact h2

end DbarGlueData

end RS
