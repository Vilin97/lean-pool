/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.MappingDegree.LocalStructure

/-!
# Calibrated fiber stacks (residue-theorem, general-`X` reduction support)

Unit: residue-theorem (`docs/design/residue-theorem.md` §6 route, primary per the orchestrator
addendum). `Jacobian/FormTrace/ResidueTraceCompat.lean`'s main theorem `resAtP1_trace_eq_sum`
takes an explicit calibration hypothesis `hcal`: the stack's adapted TARGET charts must be
translates of `chartAt ℂ y₀`. That hypothesis is satisfied by the concrete construction of
`RS.exists_adaptedChartsAt` (whose target chart is literally
`(chartAt ℂ (F x) ≫ₕ subRight …) ≫ₕ ofSet …`) but is NOT exposed by the abstract existential.

This file re-runs the two existence proofs (`exists_adaptedChartsAt`,
`exists_fiberStack` — `Jacobian/LocalMultiplicity/AdaptedCharts.lean` and
`Jacobian/MappingDegree/LocalStructure.lean`, copied with attribution per CONVENTIONS.md's
Compat discipline; residue-theorem may not edit those units' files) with the single extra
conclusion `∀ y, A.e' y = chartAt ℂ (F x) y - chartAt ℂ (F x) (F x)` threaded through:

* `RS.exists_adaptedChartsAt_translated` — adapted charts whose target chart is, as a raw
  function, the recentered preferred chart at `F x`.
* `RS.exists_fiberStack_translated` — a `FiberStack` all of whose target charts are the
  recentered `chartAt ℂ y₀`; this discharges `resAtP1_trace_eq_sum`'s `hcal` verbatim.
-/

open Filter Set OpenPartialHomeomorph Metric Function
open scoped ContDiff Manifold Topology

namespace RS

section Existence

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Near the chart image of `x`, points stay in the chart target, pull back into `U`, and their
`F`-images stay in the target chart's source. Split out of `exists_adaptedChartsAt_translated`
to keep that proof under the 200-line size we hold ourselves to. -/
private theorem eventually_target_mem_source {F : X → Y} {x : X} (hFc : ContinuousAt F x)
    {U : Set X} (hU : U ∈ 𝓝 x) (hxc : x ∈ (chartAt ℂ x).source)
    (hxc' : F x ∈ (chartAt ℂ (F x)).source)
    (hsymm_cont : ContinuousAt (chartAt ℂ x).symm (chartAt ℂ x x)) :
    ∀ᶠ w in 𝓝 (chartAt ℂ x x), w ∈ (chartAt ℂ x).target ∧
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

/-- `RS.exists_adaptedChartsAt`, strengthened with the (construction-inherent) conclusion that
the adapted target chart is, as a raw function on all of `Y`, the recentered preferred chart at
`F x`. Proof copied from `Jacobian/LocalMultiplicity/AdaptedCharts.lean` (the extra conclusion
is `rfl` for that construction). -/
theorem exists_adaptedChartsAt_translated {F : X → Y} {x : X}
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hnc : ¬ EventuallyConst F (𝓝 x))
    {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ A : AdaptedChartsAt F x (multiplicity F x), A.e.source ⊆ U ∧
      ∀ y : Y, A.e' y = chartAt ℂ (F x) y - chartAt ℂ (F x) (F x) := by
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
  have hE := eventually_target_mem_source hFc hU hxc hxc' hsymm_cont
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
    fun z hz ↦ (hkey z hz).1, he'coe⟩

end Existence

/-! ### Calibrated fiber stacks (standing surface hypotheses) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

/-- `RS.exists_fiberStack`, strengthened: a stack of adapted charts over `y₀` all of whose
target charts are, as raw functions, the recentered `chartAt ℂ y₀` — exactly
`resAtP1_trace_eq_sum`'s calibration hypothesis `hcal`. Proof copied from
`Jacobian/MappingDegree/LocalStructure.lean`, seeded with
`exists_adaptedChartsAt_translated`. -/
theorem exists_fiberStack_translated (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (y₀ : Y) :
    ∃ S : FiberStack F y₀, ∀ i : Fin S.n, ∀ y : Y,
      (S.A i).e' y = chartAt ℂ y₀ y - chartAt ℂ y₀ y₀ := by
  have hnc : ∀ x : X, ¬ EventuallyConst F (𝓝 x) := not_eventuallyConst hF hne
  have hfin : (F ⁻¹' {y₀}).Finite := fiber_finite hF hne y₀
  -- 1. enumerate the fiber
  obtain ⟨n, pt, hrange⟩ := hfin.fin_embedding
  have hmem_fiber : ∀ i, (pt : Fin n → X) i ∈ F ⁻¹' {y₀} := fun i ↦ by
    rw [← hrange]; exact Set.mem_range_self i
  -- 2. pairwise-disjoint open neighborhoods of the fiber points
  obtain ⟨U, hU, hUdisj⟩ := hfin.t2_separation
  -- 3. calibrated adapted charts at each fiber point, shrunk into the disjoint opens
  have hex : ∀ i : Fin n, ∃ A : AdaptedChartsAt F (pt i) (multiplicity F (pt i)),
      A.e.source ⊆ U (pt i) ∧
        ∀ y : Y, A.e' y = chartAt ℂ (F (pt i)) y - chartAt ℂ (F (pt i)) (F (pt i)) := fun i ↦
    exists_adaptedChartsAt_translated (hF (pt i)) (hnc (pt i))
      ((hU (pt i)).2.mem_nhds (hU (pt i)).1)
  choose A hA hA' using hex
  have hdisj : Pairwise (Disjoint on fun i ↦ (A i).e.source) := fun i j hij ↦
    (hUdisj (hmem_fiber i) (hmem_fiber j) (pt.injective.ne hij)).mono (hA i) (hA j)
  -- 4. trap the fiber
  have hW₀open : IsOpen (⋃ i, (A i).e.source) := isOpen_iUnion fun i ↦ (A i).e.open_source
  have hfiber_sub : F ⁻¹' {y₀} ⊆ ⋃ i, (A i).e.source := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Set.mem_iUnion.mpr ⟨i, (A i).mem_source⟩
  have hW₀mem : (⋃ i, (A i).e.source) ∈ 𝓝ˢ (F ⁻¹' {y₀}) :=
    hW₀open.mem_nhdsSet.mpr hfiber_sub
  obtain ⟨W, hWmem, hWsub⟩ := mem_comap.mp (hF.continuous.isClosedMap.comap_nhds_le hW₀mem)
  obtain ⟨W', hW'sub, hW'open, hyW'⟩ := mem_nhds_iff.mp hWmem
  -- 5. assemble `V`, and the calibration conclusion
  refine ⟨⟨n, pt, pt.injective, hrange,
    fun i ↦ one_le_multiplicity_of_not_const hF hne (pt i), A, hdisj,
    W' ∩ ⋂ i, ((A i).e'.source ∩
      (A i).e' ⁻¹' Metric.ball 0 ((A i).radius ^ multiplicity F (pt i))),
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- open
    apply hW'open.inter
    apply isOpen_iInter_of_finite
    intro i
    exact (A i).e'.continuousOn.isOpen_inter_preimage (A i).e'.open_source Metric.isOpen_ball
  · -- `y₀ ∈ V`
    refine ⟨hyW', Set.mem_iInter.mpr fun i ↦ ⟨?_, ?_⟩⟩
    · rw [show y₀ = F (pt i) from (hmem_fiber i : F (pt i) = y₀).symm]
      exact (A i).mem_source'
    · rw [Set.mem_preimage, show y₀ = F (pt i) from (hmem_fiber i : F (pt i) = y₀).symm,
        (A i).map_eq_zero']
      exact Metric.mem_ball_self (pow_pos (A i).radius_pos _)
  · -- `V ⊆ e'.source`
    exact fun i y hy ↦ (Set.mem_iInter.mp hy.2 i).1
  · -- images in the normal-form balls
    exact fun i y hy ↦ (Set.mem_iInter.mp hy.2 i).2
  · -- `F ⁻¹' V` trapped in the chart sources
    exact fun x hx ↦ hWsub (hW'sub hx.1)
  · -- calibration
    intro i y
    have h := hA' i y
    rwa [show F (pt i) = y₀ from hmem_fiber i] at h

end RS
