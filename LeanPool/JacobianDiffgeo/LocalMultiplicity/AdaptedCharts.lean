/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: local-multiplicity (CC4). Adapted charts: the local normal form `z ↦ z ^ k`.
-/
import LeanPool.JacobianDiffgeo.LocalMultiplicity.Multiplicity

/-!
# Adapted charts (Forster Thm 2.1)

* `RS.AdaptedChartsAt F x k` — a pair of centered maximal-atlas charts with round-ball targets
  in which `F` reads exactly as `z ↦ z ^ k`.
* `RS.exists_adaptedChartsAt` — THE atom: a holomorphic nonconstant germ admits adapted charts
  with `k = multiplicity F x`, and the source can be shrunk into any given neighborhood.
* Derived API: `eqOn_symm`, `image_source` (`F` maps the chart source ONTO the target chart
  source), `contMDiffOn_e/e'(_symm)`, and `multiplicity_eq` (adapted charts pin down the
  multiplicity).
-/

open Filter Set OpenPartialHomeomorph Metric
open scoped ContDiff Manifold Topology

namespace RS

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Adapted chart pair at `x` exhibiting `F` as `z ↦ z ^ k` (Forster Thm 2.1).
Both charts belong to the analytic maximal atlases (so all holomorphy transports), both are
centered, targets are round balls, and `F` is exactly `(· ^ k)` in these coordinates. -/
structure AdaptedChartsAt (F : X → Y) (x : X) (k : ℕ) where
  /-- The source chart, centred at the point. -/
  e : OpenPartialHomeomorph X ℂ
  /-- The target chart, centred at the image point. -/
  e' : OpenPartialHomeomorph Y ℂ
  mem_maximalAtlas : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X
  mem_maximalAtlas' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y
  /-- The radius of the source disc on which the normal form holds. -/
  radius : ℝ
  radius_pos : 0 < radius
  mem_source : x ∈ e.source
  mem_source' : F x ∈ e'.source
  map_eq_zero : e x = 0
  map_eq_zero' : e' (F x) = 0
  target_eq : e.target = Metric.ball 0 radius
  target_eq' : e'.target = Metric.ball 0 (radius ^ k)
  mapsTo : Set.MapsTo F e.source e'.source
  eqOn_pow : ∀ z ∈ e.source, e' (F z) = e z ^ k

namespace AdaptedChartsAt

variable {F : X → Y} {x : X} {k : ℕ}

theorem eqOn_symm (A : AdaptedChartsAt F x k) : ∀ z ∈ A.e.source, F z = A.e'.symm (A.e z ^ k) := by
  intro z hz
  rw [← A.eqOn_pow z hz, A.e'.left_inv (A.mapsTo hz)]

/-- `F` maps the adapted source onto the adapted target source (uses `image_pow_ball`). -/
theorem image_source (hk : k ≠ 0) (A : AdaptedChartsAt F x k) :
    F '' A.e.source = A.e'.source := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact A.mapsTo hz
  · intro y hy
    have hy' : A.e' y ∈ Metric.ball (0 : ℂ) (A.radius ^ k) := by
      rw [← A.target_eq']
      exact A.e'.map_source hy
    rw [← image_pow_ball hk A.radius_pos.le] at hy'
    obtain ⟨w, hw, hwk⟩ := hy'
    have hwt : w ∈ A.e.target := by rw [A.target_eq]; exact hw
    have hzs : A.e.symm w ∈ A.e.source := A.e.map_target hwt
    refine ⟨A.e.symm w, hzs, ?_⟩
    apply A.e'.injOn (A.mapsTo hzs) hy
    rw [A.eqOn_pow _ hzs, A.e.right_inv hwt]
    exact hwk

section ContMDiff

theorem contMDiffOn_e (A : AdaptedChartsAt F x k) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω A.e A.e.source :=
  contMDiffOn_of_mem_maximalAtlas A.mem_maximalAtlas

theorem contMDiffOn_e_symm (A : AdaptedChartsAt F x k) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω A.e.symm A.e.target :=
  contMDiffOn_symm_of_mem_maximalAtlas A.mem_maximalAtlas

theorem contMDiffOn_e' (A : AdaptedChartsAt F x k) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω A.e' A.e'.source :=
  contMDiffOn_of_mem_maximalAtlas A.mem_maximalAtlas'

theorem contMDiffOn_e'_symm (A : AdaptedChartsAt F x k) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω A.e'.symm A.e'.target :=
  contMDiffOn_symm_of_mem_maximalAtlas A.mem_maximalAtlas'

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

/-- Adapted charts pin down the multiplicity: if `F` reads as `z ^ k` in adapted charts,
then `k` IS the local multiplicity. (The hypothesis `hk` is kept for interface stability;
it is not needed for this direction.) -/
theorem multiplicity_eq (_hk : k ≠ 0) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (A : AdaptedChartsAt F x k) : multiplicity F x = k := by
  have hinv := analyticOrderAt_charts_eq_multiplicityENat hF
    A.mem_maximalAtlas A.mem_source A.mem_maximalAtlas' A.mem_source'
  have hev : (fun z ↦ A.e' (F (A.e.symm z)) - A.e' (F x)) =ᶠ[𝓝 (A.e x)]
      fun z ↦ z ^ k := by
    have h0 : A.e x ∈ A.e.target := A.e.map_source A.mem_source
    filter_upwards [A.e.open_target.mem_nhds h0] with z hz
    rw [A.eqOn_pow _ (A.e.map_target hz), A.e.right_inv hz, A.map_eq_zero', sub_zero]
  rw [analyticOrderAt_congr hev, A.map_eq_zero] at hinv
  have hpow : analyticOrderAt (fun z : ℂ ↦ z ^ k) 0 = (k : ℕ∞) := by
    have ha : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k) 0 := by fun_prop
    rw [ha.analyticOrderAt_eq_natCast]
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun z ↦ by simp⟩
  rw [hpow] at hinv
  rw [multiplicity_def, ← hinv]
  exact ENat.toNat_natCast k

end ContMDiff

end AdaptedChartsAt

section Existence

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

/-- Existence of adapted charts (Forster Thm 2.1), with source shrinkable into any given
neighborhood. Here `k = multiplicity F x ≥ 1`. -/
theorem exists_adaptedChartsAt {F : X → Y} {x : X}
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hnc : ¬ EventuallyConst F (𝓝 x))
    {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ A : AdaptedChartsAt F x (multiplicity F x), A.e.source ⊆ U := by
  obtain ⟨hFc, hchart⟩ := LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hF
  have hk0 : multiplicity F x ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_multiplicity hF hnc)
  have hxc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hxc' : F x ∈ (chartAt ℂ (F x)).source := mem_chart_source ℂ (F x)
  -- the uncentered composite in the standard charts
  set g : ℂ → ℂ := fun z ↦ chartAt ℂ (F x) (F ((chartAt ℂ x).symm z)) with hg_def
  have hg : AnalyticAt ℂ g (chartAt ℂ x x) := analyticAt_inChartAt_iff.mp hchart
  have hgz₀ : g (chartAt ℂ x x) = chartAt ℂ (F x) (F x) := by
    rw [hg_def]
    simp only
    rw [(chartAt ℂ x).left_inv hxc]
  -- its recentered vanishing order is the multiplicity
  have hord : analyticOrderAt (g · - g (chartAt ℂ x x)) (chartAt ℂ x x)
      = ((multiplicity F x : ℕ) : ℕ∞) := by
    have h1 : analyticOrderAt (g · - g (chartAt ℂ x x)) (chartAt ℂ x x)
        = multiplicityENat F x := by
      rw [multiplicityENat_def]
      apply analyticOrderAt_congr
      apply Eventually.of_forall
      intro z
      simp only [hg_def, inChartAt]
      rw [(chartAt ℂ x).left_inv hxc]
    rw [h1, ← natCast_multiplicity hF hnc]
  -- the planar normal form, packaged
  obtain ⟨Φ, hz₀Φ, hΦ0, hΦan, hΦsymm, hΦeq⟩ :=
    AnalyticAt.exists_normal_form_openPartialHomeomorph hg hord hk0
  have hΦgrp : Φ ∈ contDiffGroupoid ω 𝓘(ℂ) := mem_contDiffGroupoid_iff_analytic.mpr ⟨hΦan, hΦsymm⟩
  -- the recentering translation on the target side
  set T : OpenPartialHomeomorph ℂ ℂ :=
    (Homeomorph.subRight (chartAt ℂ (F x) (F x))).toOpenPartialHomeomorph with hT_def
  have hTcoe : ∀ w, T w = w - chartAt ℂ (F x) (F x) := fun w ↦ rfl
  have hTsymm : ∀ w, T.symm w = w + chartAt ℂ (F x) (F x) := fun w ↦ rfl
  have hTsrc : T.source = univ := rfl
  have hTtgt : T.target = univ := rfl
  have hTgrp : T ∈ contDiffGroupoid ω 𝓘(ℂ) := by
    apply mem_contDiffGroupoid_iff_analytic.mpr
    refine ⟨fun w _ ↦ ?_, fun w _ ↦ ?_⟩
    · exact (analyticAt_id.sub analyticAt_const).congr
        (Eventually.of_forall fun v ↦ (hTcoe v).symm)
    · exact (analyticAt_id.add analyticAt_const).congr
        (Eventually.of_forall fun v ↦ (hTsymm v).symm)
  -- collect the neighborhood conditions on the chart side
  have h0t : (0 : ℂ) ∈ Φ.target := by rw [← hΦ0]; exact Φ.map_source hz₀Φ
  have hΦsymm0 : Φ.symm (0 : ℂ) = chartAt ℂ x x := by rw [← hΦ0, Φ.left_inv hz₀Φ]
  have hΦsymm_cont : Tendsto Φ.symm (𝓝 0) (𝓝 (chartAt ℂ x x)) := by
    have h := (Φ.continuousAt_symm h0t).tendsto
    rwa [hΦsymm0] at h
  have hsymm_cont : ContinuousAt (chartAt ℂ x).symm (chartAt ℂ x x) :=
    (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxc)
  have hE : ∀ᶠ w in 𝓝 (chartAt ℂ x x), w ∈ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm w ∈ U ∧ F ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (F x)).source := by
    have h1 : (chartAt ℂ x).target ∈ 𝓝 (chartAt ℂ x x) :=
      (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxc)
    have h2 : ∀ᶠ w in 𝓝 (chartAt ℂ x x), (chartAt ℂ x).symm w ∈ U := by
      have h := hsymm_cont.tendsto
      rw [(chartAt ℂ x).left_inv hxc] at h
      exact h.eventually hU
    have h3 : ∀ᶠ w in 𝓝 (chartAt ℂ x x), F ((chartAt ℂ x).symm w) ∈
        (chartAt ℂ (F x)).source := by
      have hcF : ContinuousAt (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
        apply ContinuousAt.comp ?_ hsymm_cont
        rw [(chartAt ℂ x).left_inv hxc]
        exact hFc
      have h := hcF.tendsto
      have hval : (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = F x := by
        simp only [Function.comp_apply]
        rw [(chartAt ℂ x).left_inv hxc]
      rw [hval] at h
      exact h.eventually ((chartAt ℂ (F x)).open_source.mem_nhds hxc')
    filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
    exact ⟨hw1, hw2, hw3⟩
  have hEv : ∀ᶠ v in 𝓝 (0 : ℂ), (v ∈ Φ.target ∧
      (Φ.symm v ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm (Φ.symm v) ∈ U ∧
        F ((chartAt ℂ x).symm (Φ.symm v)) ∈ (chartAt ℂ (F x)).source)) ∧
      v + chartAt ℂ (F x) (F x) ∈ (chartAt ℂ (F x)).target := by
    have haddcont : Tendsto (fun v : ℂ ↦ v + chartAt ℂ (F x) (F x)) (𝓝 0)
        (𝓝 (chartAt ℂ (F x) (F x))) := by
      have h := (continuous_add_const (chartAt ℂ (F x) (F x))).tendsto (0 : ℂ)
      simpa using h
    filter_upwards [Φ.open_target.mem_nhds h0t, hΦsymm_cont.eventually hE,
      haddcont.eventually ((chartAt ℂ (F x)).open_target.mem_nhds
        ((chartAt ℂ (F x)).map_source hxc'))] with v hv1 hv2 hv3
    exact ⟨⟨hv1, hv2⟩, hv3⟩
  obtain ⟨ε, hε0, hεsub⟩ := Metric.eventually_nhds_iff_ball.mp hEv
  -- choose the radius
  set ρ : ℝ := min ε 1 / 2 with hρ_def
  have hρ0 : 0 < ρ := div_pos (lt_min hε0 one_pos) two_pos
  have hρε : ρ < ε := by
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    have h2 : 0 < ε := hε0
    rw [hρ_def]; linarith
  have hρ1 : ρ ≤ 1 := by
    have h1 : min ε 1 ≤ 1 := min_le_right _ _
    rw [hρ_def]; linarith
  have hρk : ρ ^ multiplicity F x ≤ ρ := pow_le_of_le_one hρ0.le hρ1 hk0
  have hballρ : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 ε := Metric.ball_subset_ball hρε.le
  have hballρk : Metric.ball (0 : ℂ) (ρ ^ multiplicity F x) ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρk.trans hρε.le)
  -- the adapted charts
  set e : OpenPartialHomeomorph X ℂ :=
    (chartAt ℂ x ≫ₕ Φ) ≫ₕ ofSet (Metric.ball 0 ρ) Metric.isOpen_ball with he_def
  set e' : OpenPartialHomeomorph Y ℂ :=
    (chartAt ℂ (F x) ≫ₕ T) ≫ₕ ofSet (Metric.ball 0 (ρ ^ multiplicity F x)) Metric.isOpen_ball
    with he'_def
  have hecoe : ∀ z, e z = Φ (chartAt ℂ x z) := fun z ↦ rfl
  have he'coe : ∀ y', e' y' = chartAt ℂ (F x) y' - chartAt ℂ (F x) (F x) := fun y' ↦ rfl
  -- source membership descriptions
  have hesrc : ∀ z, z ∈ e.source ↔
      (z ∈ (chartAt ℂ x).source ∧ chartAt ℂ x z ∈ Φ.source) ∧
        Φ (chartAt ℂ x z) ∈ Metric.ball (0 : ℂ) ρ := by
    intro z
    rw [he_def]
    simp only [trans_source, ofSet_source, mem_inter_iff, mem_preimage, coe_trans,
      Function.comp_apply]
  have he'src : ∀ y', y' ∈ e'.source ↔
      y' ∈ (chartAt ℂ (F x)).source ∧
        chartAt ℂ (F x) y' - chartAt ℂ (F x) (F x) ∈
          Metric.ball (0 : ℂ) (ρ ^ multiplicity F x) := by
    intro y'
    rw [he'_def]
    simp only [trans_source, ofSet_source, mem_inter_iff, mem_preimage, coe_trans,
      Function.comp_apply, hTsrc, mem_univ, and_true, hTcoe]
  -- the key pointwise facts on the source
  have hkey : ∀ z ∈ e.source, z ∈ U ∧ F z ∈ (chartAt ℂ (F x)).source ∧
      chartAt ℂ (F x) (F z) - chartAt ℂ (F x) (F x) = Φ (chartAt ℂ x z) ^ multiplicity F x := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, hz3⟩ := (hesrc z).mp hz
    have hw := (hεsub _ (hballρ hz3)).1
    rw [Φ.left_inv hz2] at hw
    rw [(chartAt ℂ x).left_inv hz1] at hw
    refine ⟨hw.2.2.1, hw.2.2.2, ?_⟩
    have heq := hΦeq (chartAt ℂ x z) hz2
    simp only [hg_def] at heq
    rw [(chartAt ℂ x).left_inv hz1, (chartAt ℂ x).left_inv hxc] at heq
    rw [heq, add_sub_cancel_left]
  -- assemble the structure
  have hxe : x ∈ e.source := by
    rw [hesrc]
    exact ⟨⟨hxc, hz₀Φ⟩, by rw [hΦ0]; exact mem_ball_self hρ0⟩
  have hez : e x = 0 := by rw [hecoe, hΦ0]
  have he'z : e' (F x) = 0 := by rw [he'coe, sub_self]
  have hxe' : F x ∈ e'.source := by
    rw [he'src]
    exact ⟨hxc', by rw [sub_self]; exact mem_ball_self (pow_pos hρ0 _)⟩
  have htgt : e.target = Metric.ball 0 ρ := by
    rw [he_def]
    rw [trans_target, trans_target, ofSet_target, ofSet_symm]
    simp only [ofSet_apply, preimage_id_eq, id_eq]
    apply Set.inter_eq_left.mpr
    intro v hv
    have h := (hεsub v (hballρ hv)).1
    exact ⟨h.1, h.2.1⟩
  have htgt' : e'.target = Metric.ball 0 (ρ ^ multiplicity F x) := by
    rw [he'_def]
    rw [trans_target, trans_target, ofSet_target, ofSet_symm]
    simp only [ofSet_apply, preimage_id_eq, id_eq, hTtgt, univ_inter]
    apply Set.inter_eq_left.mpr
    intro v hv
    rw [mem_preimage, hTsymm]
    exact (hεsub v (hballρk hv)).2
  have hmapsto : Set.MapsTo F e.source e'.source := by
    intro z hz
    obtain ⟨-, hz2, hz3⟩ := hkey z hz
    rw [he'src]
    refine ⟨hz2, ?_⟩
    rw [hz3, mem_ball_zero_iff, norm_pow]
    have hzball : Φ (chartAt ℂ x z) ∈ Metric.ball (0 : ℂ) ρ := ((hesrc z).mp hz).2
    exact pow_lt_pow_left₀ (mem_ball_zero_iff.mp hzball) (norm_nonneg _) hk0
  have heqpow : ∀ z ∈ e.source, e' (F z) = e z ^ multiplicity F x := by
    intro z hz
    rw [he'coe, hecoe]
    exact (hkey z hz).2.2
  exact ⟨⟨e, e', trans_mem_maximalAtlas
      (trans_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hΦgrp)
      (ofSet_mem_contDiffGroupoid Metric.isOpen_ball),
    trans_mem_maximalAtlas
      (trans_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (F x)) hTgrp)
      (ofSet_mem_contDiffGroupoid Metric.isOpen_ball),
    ρ, hρ0, hxe, hxe', hez, he'z, htgt, htgt', hmapsto, heqpow⟩,
    fun z hz ↦ (hkey z hz).1⟩

end Existence

end RS
