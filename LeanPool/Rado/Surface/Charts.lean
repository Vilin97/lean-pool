/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Topology.SecondCountable
import LeanPool.Rado.Surface.HolomorphicCompat

/-!
# Riemann-surface chart conventions

`X` is the eval problem's Riemann surface: `[TopologicalSpace X] [T2Space X]
[ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]` (connectedness
is only needed at the very end). This file sets up the chart-level toolkit:

* transition maps between maximal-atlas charts are analytic (C¹ over `ℂ` means
  complex-differentiable on an open set, hence analytic by
  `DifferentiableOn.analyticOnNhd`);
* `Rado.HolomorphicOn F s`: chartwise holomorphy of `F : X → ℂ`, with chart
  independence;
* the identity theorem on connected open subsets of `X`;
* stability of the maximal atlas under affine post-composition (used to
  normalize a chart so that its target contains the standard configuration of
  `Rado/Complex/PlanarConnected.lean`);
* point-set instances: local compactness, local (path-)connectedness, local
  second countability.
-/

open Set Topology Metric Manifold Filter

namespace Rado

/-- The maximal C¹ (equivalently, holomorphic) atlas of a Riemann surface. -/
abbrev riemannAtlas (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    Set (OpenPartialHomeomorph X ℂ) :=
  IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Transition maps between maximal-atlas charts are analytic. -/
theorem transition_analyticAt {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) (he' : e' ∈ riemannAtlas X) {x : X}
    (hx : x ∈ e.source ∩ e'.source) :
    AnalyticAt ℂ (e' ∘ e.symm) (e x) := by
  have hmem := IsManifold.compatible_of_mem_maximalAtlas he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hmem
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] at hmem
  have hopen : IsOpen (e.symm.trans e').source := (e.symm.trans e').open_source
  have han : AnalyticOnNhd ℂ (e.symm.trans e') (e.symm.trans e').source :=
    (hmem.1.differentiableOn one_ne_zero).analyticOnNhd hopen
  have hxmem : e x ∈ (e.symm.trans e').source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    refine ⟨e.map_source hx.1, ?_⟩
    rw [mem_preimage, e.left_inv hx.1]
    exact hx.2
  have hana := han _ hxmem
  rwa [OpenPartialHomeomorph.coe_trans] at hana

/-- The preferred chart at a point belongs to the maximal atlas. -/
theorem chartAt_mem_riemannAtlas (x : X) : chartAt ℂ x ∈ riemannAtlas X :=
  IsManifold.chart_mem_maximalAtlas x

/-- Chartwise holomorphy of a map `X → ℂ` on a set, via the preferred charts. -/
def HolomorphicOn (F : X → ℂ) (s : Set X) : Prop :=
  ∀ x ∈ s, AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

namespace HolomorphicOn

variable {F G : X → ℂ} {s : Set X}

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem continuousOn (hF : HolomorphicOn F s) : ContinuousOn F s := by
  intro x hx
  have h1 : ContinuousAt ((F ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) x :=
    (hF x hx).continuousAt.comp ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))
  refine (h1.congr ?_).continuousWithinAt
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem mono (hF : HolomorphicOn F s) {t : Set X} (hts : t ⊆ s) : HolomorphicOn F t :=
  fun x hx ↦ hF x (hts hx)

/-- Chart independence: a chartwise-holomorphic map reads as analytic through
every maximal-atlas chart. -/
theorem analyticAt_comp_symm (hF : HolomorphicOn F s)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ riemannAtlas X) {x : X}
    (hx : x ∈ s ∩ e.source) : AnalyticAt ℂ (F ∘ e.symm) (e x) := by
  obtain ⟨hxs, hxe⟩ := hx
  set c := chartAt ℂ x with hc
  have hF₁ : AnalyticAt ℂ (F ∘ c.symm) (c x) := hF x hxs
  have htrans : AnalyticAt ℂ (c ∘ e.symm) (e x) :=
    transition_analyticAt he (chartAt_mem_riemannAtlas x) ⟨hxe, mem_chart_source ℂ x⟩
  have hpt : (c ∘ e.symm) (e x) = c x := by
    simp only [Function.comp_apply, e.left_inv hxe]
  have hcomp : AnalyticAt ℂ ((F ∘ c.symm) ∘ (c ∘ e.symm)) (e x) :=
    AnalyticAt.comp (by rw [hpt]; exact hF₁) htrans
  have hU : IsOpen (e.target ∩ e.symm ⁻¹' c.source) :=
    e.isOpen_inter_preimage_symm c.open_source
  have hexU : e x ∈ e.target ∩ e.symm ⁻¹' c.source := by
    refine ⟨e.map_source hxe, ?_⟩
    rw [mem_preimage, e.left_inv hxe]
    exact mem_chart_source ℂ x
  refine hcomp.congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hexU) fun z hz ↦ ?_)
  simp only [Function.comp_apply, c.left_inv hz.2]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- If `F` agrees with a holomorphic map near each point of `s`, it is
holomorphic on `s`. -/
theorem congr_of_eventuallyEq (hG : HolomorphicOn G s)
    (h : ∀ x ∈ s, F =ᶠ[𝓝 x] G) : HolomorphicOn F s := by
  intro x hx
  have htend : Filter.Tendsto (chartAt ℂ x).symm (𝓝 (chartAt ℂ x x)) (𝓝 x) :=
    ((chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)).le
  exact (hG x hx).congr (((h x hx).symm).comp_tendsto htend)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **Identity theorem** on a Riemann surface: two maps holomorphic on a
connected open set that agree near one of its points agree everywhere on it. -/
theorem eqOn_of_eventuallyEq (hF : HolomorphicOn F s) (hG : HolomorphicOn G s)
    (hs : IsOpen s) (hsc : IsPreconnected s) {x : X} (hx : x ∈ s)
    (hFG : F =ᶠ[𝓝 x] G) : EqOn F G s := by
  have key : s ⊆ {y | y ∈ s ∧ F =ᶠ[𝓝 y] G} := by
    refine hsc.subset_of_closure_inter_subset ?_ ⟨x, hx, hx, hFG⟩ ?_
    · -- the agreement set is open
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨hys, hyFG⟩
      filter_upwards [hs.mem_nhds hys, eventually_eventuallyEq_nhds.mpr hyFG] with z hzs hz
      exact ⟨hzs, hz⟩
    · -- the agreement set is relatively closed in `s` (identity theorem in a chart)
      rintro y ⟨hyc, hys⟩
      by_cases hyT : y ∈ {y | y ∈ s ∧ F =ᶠ[𝓝 y] G}
      · exact hyT
      refine ⟨hys, ?_⟩
      set c := chartAt ℂ y with hc
      have hcy : y ∈ c.source := mem_chart_source ℂ y
      have hfreq : ∃ᶠ w in 𝓝[≠] (c y), (F ∘ c.symm) w = (G ∘ c.symm) w := by
        rw [frequently_nhdsWithin_iff, ← c.map_nhds_eq hcy, Filter.frequently_map]
        have h1 : ∃ᶠ z in 𝓝 y, z ∈ {y | y ∈ s ∧ F =ᶠ[𝓝 y] G} :=
          mem_closure_iff_frequently.mp hyc
        refine (h1.and_eventually (c.open_source.mem_nhds hcy)).mono ?_
        rintro z ⟨hzT, hzc⟩
        refine ⟨?_, ?_⟩
        · simp only [Function.comp_apply, c.left_inv hzc]
          exact hzT.2.eq_of_nhds
        · simp only [mem_compl_iff, mem_singleton_iff]
          intro hzy
          exact hyT (c.injOn hzc hcy hzy ▸ hzT)
      have hev : F ∘ c.symm =ᶠ[𝓝 (c y)] G ∘ c.symm :=
        ((hF y hys).frequently_eq_iff_eventually_eq (hG y hys)).mp hfreq
      have htend : Filter.Tendsto c (𝓝 y) (𝓝 (c y)) := c.continuousAt hcy
      filter_upwards [htend.eventually hev, c.open_source.mem_nhds hcy] with z h1 h2
      simpa only [Function.comp_apply, c.left_inv h2] using h1
  exact fun y hy ↦ ((key hy).2).eq_of_nhds

end HolomorphicOn

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Post-composing a maximal-atlas chart with a complex affine map `z ↦ a z + b`
(`a ≠ 0`) stays in the maximal atlas. -/
theorem affine_trans_mem_riemannAtlas {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) {a b : ℂ} (ha : a ≠ 0) :
    ∃ e' ∈ riemannAtlas X, e'.source = e.source ∧
      ∀ x ∈ e.source, e' x = a * e x + b := by
  set A : OpenPartialHomeomorph ℂ ℂ := (affineHomeomorph a b ha).toOpenPartialHomeomorph with hA
  have hAcoe : (A : ℂ → ℂ) = fun z ↦ a * z + b := rfl
  have hAsymm : (A.symm : ℂ → ℂ) = fun z ↦ (z - b) / a := rfl
  have hAsource : A.source = univ := rfl
  have hAmem : A ∈ contDiffGroupoid 1 𝓘(ℂ, ℂ) := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ,
      hAcoe, hAsymm]
    constructor
    · exact ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn
    · exact ((contDiff_id.sub contDiff_const).div_const a).contDiffOn
  have he₀ : ∀ f ∈ atlas ℂ X, e.symm.trans f ∈ contDiffGroupoid 1 𝓘(ℂ, ℂ) ∧
      f.symm.trans e ∈ contDiffGroupoid 1 𝓘(ℂ, ℂ) :=
    mem_maximalAtlas_iff.1 (IsManifold.mem_maximalAtlas_iff.1 he)
  refine ⟨e.trans A, ?_, ?_, ?_⟩
  · refine IsManifold.mem_maximalAtlas_iff.2 (mem_maximalAtlas_iff.2 fun f hf ↦ ⟨?_, ?_⟩)
    · have hrw : (e.trans A).symm.trans f = A.symm.trans ((e.symm.trans f)) := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc]
      rw [hrw]
      exact (contDiffGroupoid 1 𝓘(ℂ, ℂ)).trans
        ((contDiffGroupoid 1 𝓘(ℂ, ℂ)).symm hAmem) (he₀ f hf).1
    · have hrw : f.symm.trans (e.trans A) = (f.symm.trans e).trans A :=
        (OpenPartialHomeomorph.trans_assoc _ _ _).symm
      rw [hrw]
      exact (contDiffGroupoid 1 𝓘(ℂ, ℂ)).trans (he₀ f hf).2 hAmem
  · rw [OpenPartialHomeomorph.trans_source, hAsource, preimage_univ, inter_univ]
  · intro x hx
    rw [OpenPartialHomeomorph.trans_apply, hAcoe]

section Instances

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Riemann surfaces are locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace X :=
  ChartedSpace.locallyCompactSpace ℂ X

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Riemann surfaces are locally connected. -/
theorem locallyConnectedSpace : LocallyConnectedSpace X :=
  ChartedSpace.locallyConnectedSpace ℂ X

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Riemann surfaces are locally second countable. -/
theorem locally_secondCountable (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ SecondCountableTopology U :=
  ⟨(chartAt ℂ x).source, mem_chart_source ℂ x, (chartAt ℂ x).open_source,
    (chartAt ℂ x).secondCountableTopology_source⟩

end Instances

end Rado
