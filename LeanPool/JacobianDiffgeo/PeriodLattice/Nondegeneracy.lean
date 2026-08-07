/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PeriodLattice.FormIdentity
import LeanPool.JacobianDiffgeo.PeriodLattice.Segment
import LeanPool.JacobianDiffgeo.JacobianConstruction.OfCurve
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Order.Compact

/-!
# Nondegeneracy via the maximum principle (Forster 21.4(c), §5.1)

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md` §5.1, §6.5). The make-or-break
routing call: instead of Forster's `L²`-orthogonality chain (19.4–19.8, which needs a
chart-independent integral of smooth 2-forms this project does not have), we use the classical
"no nonconstant harmonic function on a compact surface" argument, localized to a single chart via
the complex open mapping theorem — no Hodge, no de Rham, no dissection, no 2-form integral.

Main declaration: `RS.form1_eq_zero_of_re_period_eq_zero`.
-/

open scoped ContDiff Manifold Topology
open Set Filter Metric IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] in
/-- **Nondegeneracy** (Forster 21.4(c)): if every based loop's period has vanishing real part, the
form is identically zero. Proof: the maximum principle (§5.1), replacing Forster's
19.4+19.5+19.7+10.15 chain. -/
theorem form1_eq_zero_of_re_period_eq_zero {η : Form1 X}
    (h : ∀ γ : Path (Classical.arbitrary X) (Classical.arbitrary X), (period γ η).re = 0) :
    η = 0 := by
  set P₀ := Classical.arbitrary X with hP₀_def
  -- **Step 1**: the global real primitive `F`, and its difference identity along any path.
  set F : X → ℝ := fun x => (pathIntegral (PathConnectedSpace.somePath P₀ x) η).re with hF_def
  have hFsub : ∀ {x y : X} (σ : Path x y), F y - F x = (pathIntegral σ η).re := by
    intro x y σ
    set α : Path P₀ P₀ := ((PathConnectedSpace.somePath P₀ x).trans σ).trans
      (PathConnectedSpace.somePath P₀ y).symm with hα_def
    have hα_int : pathIntegral α η = pathIntegral (PathConnectedSpace.somePath P₀ x) η
        + pathIntegral σ η - pathIntegral (PathConnectedSpace.somePath P₀ y) η := by
      rw [hα_def]
      show pathIntegral (((PathConnectedSpace.somePath P₀ x).trans σ).trans
        (PathConnectedSpace.somePath P₀ y).symm) η = _
      rw [pathIntegral_trans, pathIntegral_trans, pathIntegral_symm]
      ring
    have hre : (pathIntegral α η).re = 0 := h α
    rw [hα_int] at hre
    simp only [Complex.sub_re, Complex.add_re] at hre
    change F y - F x = (pathIntegral σ η).re
    rw [hF_def]
    linarith
  -- **Step 2**: local expression of `F` through each chart, as an eventual equality.
  have hFlocal : ∀ x₀ : X, ∃ r : ℝ, ∃ g : ℂ → ℂ, 0 < r ∧
      ball (chartAt ℂ x₀ x₀) r ⊆ (chartAt ℂ x₀).target ∧
      g (chartAt ℂ x₀ x₀) = 0 ∧
      (∀ z ∈ ball (chartAt ℂ x₀ x₀) r, HasDerivAt g (coeffIn (chartAt ℂ x₀) η z) z) ∧
      (F =ᶠ[𝓝 x₀] fun x => F x₀ + (g (chartAt ℂ x₀ x)).re) := by
    intro x₀
    set e := chartAt ℂ x₀ with he_def
    have he : e ∈ maximalAtlas 𝓘(ℂ) ω X := chart_mem_maximalAtlas x₀
    obtain ⟨r, hr, hballsub⟩ := Metric.isOpen_iff.mp e.open_target (e x₀) (mem_chart_target ℂ x₀)
    obtain ⟨g, hg0, hg⟩ := exists_hasDerivAt_ball (η.analyticOnNhd_coeffIn he) hballsub
      (mem_ball_self hr) (w := 0)
    refine ⟨r, g, hr, hballsub, hg0, hg, ?_⟩
    have hnbhd : e.source ∩ e ⁻¹' ball (e x₀) r ∈ 𝓝 x₀ :=
      Filter.inter_mem (e.open_source.mem_nhds (mem_chart_source ℂ x₀))
        ((e.continuousAt (mem_chart_source ℂ x₀)).preimage_mem_nhds (ball_mem_nhds _ hr))
    filter_upwards [hnbhd] with x hx
    obtain ⟨hxsrc, hxball⟩ := hx
    have hint := pathIntegral_segmentPath he hballsub (mem_chart_source ℂ x₀) hxsrc
      (mem_ball_self hr) hxball hg
    rw [hg0, sub_zero] at hint
    have hsub :=
        hFsub (segmentPath hballsub (mem_chart_source ℂ x₀) hxsrc (mem_ball_self hr) hxball)
    rw [hint] at hsub
    linarith
  -- **Step 3**: `F` is continuous, and (`X` compact nonempty) attains a maximum at some `p`.
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨r, g, hr, hballsub, hg0, hg, hFeq⟩ := hFlocal x₀
    set e := chartAt ℂ x₀ with he_def
    have hgcont : ContinuousAt g (e x₀) := (hg (e x₀) (mem_ball_self hr)).continuousAt
    have hecont : ContinuousAt (fun x => (e x : ℂ)) x₀ := e.continuousAt (mem_chart_source ℂ x₀)
    have hgecont : ContinuousAt (fun x => g (e x)) x₀ := hgcont.comp hecont
    have hmodel : ContinuousAt (fun x => F x₀ + (g (e x)).re) x₀ :=
      continuousAt_const.add (Complex.continuous_re.continuousAt.comp hgecont)
    exact hmodel.congr hFeq.symm
  obtain ⟨p, -, hpmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hFcont.continuousOn
  have hlocalmax : IsLocalMax F p := hpmax.isLocalMax Filter.univ_mem
  -- **Step 4**: the open-mapping dichotomy at `p`'s chart.
  obtain ⟨r, g, hr, hballsub, hg0, hg, hFeq⟩ := hFlocal p
  set e := chartAt ℂ p with he_def
  have hdiffon : DifferentiableOn ℂ g (ball (e p) r) :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  have hgan : AnalyticAt ℂ g (e p) :=
    hdiffon.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hlocalmax_g : ∀ᶠ z in 𝓝 (e p), (g z).re ≤ (g (e p)).re := by
    rw [← e.map_nhds_eq (mem_chart_source ℂ p), Filter.eventually_map, hg0, Complex.zero_re]
    filter_upwards [hFeq, hlocalmax] with x hxeq hxle
    rw [hxeq] at hxle
    linarith
  rcases hgan.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · -- **Step 5**: `g` is constant near `e p`, hence its derivative (= `coeffIn e η`) vanishes
    -- there; the identity theorem finishes.
    obtain ⟨V, hVsub, hVopen, hVmem⟩ := _root_.mem_nhds_iff.mp hconst
    set V' := V ∩ ball (e p) r with hV'_def
    have hV'open : IsOpen V' := hVopen.inter isOpen_ball
    have hV'mem : e p ∈ V' := ⟨hVmem, mem_ball_self hr⟩
    have hzero : ∀ᶠ z in 𝓝 (e p), coeffIn e η z = 0 := by
      apply Filter.eventually_of_mem (hV'open.mem_nhds hV'mem)
      intro z hz
      obtain ⟨hzV, hzball⟩ := hz
      have heqconst : g =ᶠ[𝓝 z] (fun _ => g (e p)) :=
        Filter.eventually_of_mem (hVopen.mem_nhds hzV) fun w hw => hVsub hw
      have hderiv0 : HasDerivAt g 0 z :=
          (hasDerivAt_const z (g (e p))).congr_of_eventuallyEq heqconst
      have hderivη : HasDerivAt g (coeffIn e η z) z := hg z hzball
      exact (hderiv0.unique hderivη).symm
    exact form1_eq_zero_of_eventually_coeffIn_zero hzero
  · exfalso
    set T : Set ℂ := {u : ℂ | u.re ≤ (g (e p)).re} with hT_def
    have hTmap : T ∈ Filter.map g (𝓝 (e p)) := Filter.mem_map.mpr hlocalmax_g
    have hTnhds : T ∈ 𝓝 (g (e p)) := hopen hTmap
    obtain ⟨δ, hδ, hballsub'⟩ := Metric.mem_nhds_iff.mp hTnhds
    set w : ℂ := g (e p) + (δ / 2 : ℝ) with hw_def
    have hwmem : w ∈ ball (g (e p)) δ := by
      rw [mem_ball, hw_def, dist_eq_norm]
      have heq : g (e p) + (δ / 2 : ℝ) - g (e p) = ((δ / 2 : ℝ) : ℂ) := by ring
      rw [heq, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ δ / 2)]
      linarith
    have hwT : w ∈ T := hballsub' hwmem
    have hwre : w.re ≤ (g (e p)).re := hwT
    rw [hw_def] at hwre
    simp only [Complex.add_re, Complex.ofReal_re] at hwre
    linarith

end RS

end
