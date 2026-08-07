/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PeriodLattice.GenericPoints
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Identity theorem for 1-form coefficients (§6.4)

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md` §6.4). A self-contained clopen
propagation argument: if `η ∈ Form1 X`'s preferred-chart coefficient at some point vanishes on a
whole neighborhood, `η = 0` identically. Needed by `Nondegeneracy.lean`'s maximum-principle route
(the last step, replacing Forster's Thm 19.4).

Main declaration: `RS.form1_eq_zero_of_eventually_coeffIn_zero`.
-/

open scoped ContDiff Manifold
open Set Filter Topology Metric IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The set of points around whose preferred chart the coefficient of `η` vanishes near the
chart's center. -/
private def genericVanishing (η : Form1 X) : Set X :=
  {x : X | ∀ᶠ z in 𝓝 (chartAt ℂ x x), coeffIn (chartAt ℂ x) η z = 0}

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
private theorem mem_genericVanishing {η : Form1 X} {x : X} :
    x ∈ genericVanishing η ↔ ∀ᶠ z in 𝓝 (chartAt ℂ x x), coeffIn (chartAt ℂ x) η z = 0 := Iff.rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- `genericVanishing η` is open: chart-transport of "vanishing near the center" through
`coeffIn_trans`, multiplying by a (possibly zero, irrelevant) transition factor. -/
private theorem isOpen_genericVanishing (η : Form1 X) : IsOpen (genericVanishing η) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ∀ᶠ w in 𝓝 x, coeffIn (chartAt ℂ x) η (chartAt ℂ x w) = 0 :=
    ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).eventually hx
  have hsrc : ∀ᶠ w in 𝓝 x, w ∈ (chartAt ℂ x).source :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  have hcomb : ∀ᶠ w in 𝓝 x,
      coeffIn (chartAt ℂ x) η (chartAt ℂ x w) = 0 ∧ w ∈ (chartAt ℂ x).source := hx'.and hsrc
  filter_upwards [hcomb.eventually_nhds] with y hy
  change ∀ᶠ z in 𝓝 (chartAt ℂ y y), coeffIn (chartAt ℂ y) η z = 0
  rw [← (chartAt ℂ y).map_nhds_eq (mem_chart_source ℂ y), Filter.eventually_map]
  have hysrc : ∀ᶠ w in 𝓝 y, w ∈ (chartAt ℂ y).source :=
    (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)
  filter_upwards [hy, hysrc] with w hw hwysrc
  have hz : chartAt ℂ y w ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source) :=
    ⟨w, ⟨hw.2, hwysrc⟩, rfl⟩
  have heq := coeffIn_trans (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) η hz
  rw [(chartAt ℂ y).left_inv hwysrc] at heq
  rw [heq, hw.1, mul_zero]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- `genericVanishing η` is closed: if `x` is a limit of it, the analytic coefficient in `x`'s own
chart vanishes near some nearby point of the set (chart-transport again), hence vanishes on a
whole convex ball around the chart's center (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_
eventuallyEq_zero`), so `x` itself is in the set. -/
private theorem isClosed_genericVanishing (η : Form1 X) : IsClosed (genericVanishing η) := by
  apply isClosed_of_closure_subset
  intro x hx
  set e := chartAt ℂ x with he_def
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := chart_mem_maximalAtlas x
  obtain ⟨r, hr, hballsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) (mem_chart_target ℂ x)
  have hUmem : e ⁻¹' ball (e x) r ∩ e.source ∈ 𝓝 x := by
    apply Filter.inter_mem
    · exact (e.continuousAt (mem_chart_source ℂ x)).preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr)
    · exact e.open_source.mem_nhds (mem_chart_source ℂ x)
  obtain ⟨x', hx'mem⟩ :=
    (mem_closure_iff_nhds.mp hx) (e ⁻¹' ball (e x) r ∩ e.source) hUmem
  obtain ⟨⟨hx'ball, hx'src⟩, hx'S⟩ := hx'mem
  -- `hx'S : x' ∈ genericVanishing η`; transport its vanishing data to `e`'s chart.
  have hx'ev : ∀ᶠ z in 𝓝 (chartAt ℂ x' x'), coeffIn (chartAt ℂ x') η z = 0 := hx'S
  have hzero : ∀ᶠ z in 𝓝 (e x'), coeffIn e η z = 0 := by
    rw [← e.map_nhds_eq hx'src, Filter.eventually_map]
    have hx'ev' : ∀ᶠ p in 𝓝 x', coeffIn (chartAt ℂ x') η (chartAt ℂ x' p) = 0 :=
      ((chartAt ℂ x').continuousAt (mem_chart_source ℂ x')).eventually hx'ev
    have hEsrc : ∀ᶠ p in 𝓝 x', p ∈ (chartAt ℂ x').source :=
      (chartAt ℂ x').open_source.mem_nhds (mem_chart_source ℂ x')
    have hesrc : ∀ᶠ p in 𝓝 x', p ∈ e.source := e.open_source.mem_nhds hx'src
    filter_upwards [hx'ev', hEsrc, hesrc] with p hp hpE hpe
    have hz : e p ∈ ⇑e '' ((chartAt ℂ x').source ∩ e.source) := ⟨p, ⟨hpE, hpe⟩, rfl⟩
    have heq := coeffIn_trans (chart_mem_maximalAtlas x') he η hz
    rw [e.left_inv hpe] at heq
    rw [heq, hp, mul_zero]
  have hanalytic : AnalyticOnNhd ℂ (coeffIn e η) (ball (e x) r) :=
    fun z hz => η.analyticOnNhd_coeffIn he z (hballsub hz)
  have hpre : IsPreconnected (ball (e x) r) := (convex_ball (e x) r).isPreconnected
  have heqon : Set.EqOn (coeffIn e η) 0 (ball (e x) r) :=
    hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hx'ball hzero
  change x ∈ genericVanishing η
  rw [mem_genericVanishing]
  filter_upwards [Metric.ball_mem_nhds (e x) hr] with z hz using heqon hz

omit [T2Space X] [CompactSpace X] in
/-- **The identity theorem**: eventual vanishing of `η`'s coefficient in one chart forces `η = 0`
everywhere. -/
theorem form1_eq_zero_of_eventually_coeffIn_zero {η : Form1 X} {x₀ : X}
    (h : ∀ᶠ z in 𝓝 ((chartAt ℂ x₀) x₀), coeffIn (chartAt ℂ x₀) η z = 0) : η = 0 := by
  have hSclopen : IsClopen (genericVanishing η) :=
    ⟨isClosed_genericVanishing η, isOpen_genericVanishing η⟩
  have hSne : (genericVanishing η).Nonempty := ⟨x₀, h⟩
  have hSuniv : genericVanishing η = Set.univ := by
    rcases isClopen_iff.mp hSclopen with hE | hU
    · exact absurd hE hSne.ne_empty
    · exact hU
  apply Form1.ext_coeffAt (η' := (0 : Form1 X))
  intro x
  rw [coeffAt_zero]
  have hxS : x ∈ genericVanishing η := hSuniv ▸ Set.mem_univ x
  exact hxS.self_of_nhds

end RS

end
