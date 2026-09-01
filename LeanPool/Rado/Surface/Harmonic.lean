/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Complex.Dirichlet
import LeanPool.Rado.Surface.Charts

/-!
# Harmonic and subharmonic functions on a Riemann surface

Chartwise notions for `u : X → ℝ` on the eval problem's Riemann surface
(step 3 of `Rado/PLAN.md`): `SurfaceHarmonicOn` / `SurfaceSubharmonicOn` via
chart representatives over the maximal atlas (so no `subharmonic ∘ holomorphic`
invariance is ever needed), chart invariance (`of_chartwise`), and the
local-to-global bridge `SubMeanLocalOn` — the sub-mean-value inequality on
small circles implies it on all circles, via the maximum principle and
comparison with the Poisson extension.
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The image of `s` in the chart `e`. -/
def chartImage (e : OpenPartialHomeomorph X ℂ) (s : Set X) : Set ℂ :=
  e '' (s ∩ e.source)

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem isOpen_chartImage (e : OpenPartialHomeomorph X ℂ) {s : Set X} (hs : IsOpen s) :
    IsOpen (chartImage e s) :=
  e.isOpen_image_of_subset_source (hs.inter e.open_source) inter_subset_right

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem chartImage_subset_target (e : OpenPartialHomeomorph X ℂ) (s : Set X) :
    chartImage e s ⊆ e.target := fun _ ⟨_, hx, hex⟩ ↦ hex ▸ e.map_source hx.2

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem mem_chartImage_of_mem {e : OpenPartialHomeomorph X ℂ} {s : Set X} {x : X}
    (hx : x ∈ s) (hxe : x ∈ e.source) : e x ∈ chartImage e s :=
  ⟨x, ⟨hx, hxe⟩, rfl⟩

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem mapsTo_symm_chartImage {e : OpenPartialHomeomorph X ℂ} {s : Set X} :
    MapsTo e.symm (chartImage e s) s := by
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  rw [e.left_inv hxe]
  exact hxs

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A continuous function on `s` reads as continuous through any chart. -/
theorem continuousOn_comp_chart_symm {g : X → ℝ} (e : OpenPartialHomeomorph X ℂ) {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (g ∘ e.symm) (chartImage e s) :=
  hg.comp (e.symm.continuousOn.mono (chartImage_subset_target e s)) mapsTo_symm_chartImage

/-! ## Harmonic and subharmonic functions on a Riemann surface -/

/-- `u : X → ℝ` is harmonic on `s`: every chart representative is harmonic. -/
def SurfaceHarmonicOn (u : X → ℝ) (s : Set X) : Prop :=
  ∀ e ∈ riemannAtlas X, HarmonicOnNhd (u ∘ e.symm) (chartImage e s)

/-- `g : X → ℝ` is subharmonic on `s`: continuous, and every chart
representative satisfies the sub-mean-value inequality. -/
structure SurfaceSubharmonicOn (g : X → ℝ) (s : Set X) : Prop where
  continuousOn : ContinuousOn g s
  subMeanOn : ∀ e ∈ riemannAtlas X, SubMeanOn (g ∘ e.symm) (chartImage e s)

namespace SurfaceHarmonicOn

variable {u v : X → ℝ} {s : Set X}

theorem continuousOn (hu : SurfaceHarmonicOn u s) : ContinuousOn u s := by
  intro x hx
  have h1 : ContinuousAt (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (hu _ (chartAt_mem_riemannAtlas x) _
      (mem_chartImage_of_mem hx (mem_chart_source ℂ x))).1.continuousAt
  have h2 : ContinuousAt ((u ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) x :=
    h1.comp ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))
  refine (h2.congr ?_).continuousWithinAt
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with z hz
  simp [(chartAt ℂ x).left_inv hz]

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem mono (hu : SurfaceHarmonicOn u s) {t : Set X} (hts : t ⊆ s) :
    SurfaceHarmonicOn u t := fun e he z hz ↦
  hu e he z (image_mono (inter_subset_inter_left _ hts) hz)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- To be harmonic it suffices to be harmonic in one maximal-atlas chart around
each point (chart invariance, via `HarmonicOnNhd.comp_analytic`). -/
theorem of_chartwise
    (h : ∀ x ∈ s, ∃ e ∈ riemannAtlas X, x ∈ e.source ∧ HarmonicAt (u ∘ e.symm) (e x)) :
    SurfaceHarmonicOn u s := by
  rintro e' he' z ⟨x, ⟨hxs, hxe'⟩, rfl⟩
  obtain ⟨e, he, hxe, hharm⟩ := h x hxs
  -- a ball around `e x` on which `u ∘ e.symm` is harmonic
  obtain ⟨ρ, hρpos, hball⟩ := Metric.eventually_nhds_iff_ball.mp hharm.eventually
  -- the transition `φ = e ∘ e'.symm` is analytic near `e' x`
  have htrans : AnalyticAt ℂ (e ∘ e'.symm) (e' x) := transition_analyticAt he' he ⟨hxe', hxe⟩
  -- the open set where the congruence `u ∘ e'.symm = (u ∘ e.symm) ∘ (e ∘ e'.symm)` holds
  have hWopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) :=
    e'.symm.continuousOn.isOpen_inter_preimage e'.open_target e.open_source
  have hxW : e' x ∈ e'.target ∩ e'.symm ⁻¹' e.source :=
    ⟨e'.map_source hxe', by rw [mem_preimage, e'.left_inv hxe']; exact hxe⟩
  -- a small ball around `e' x` inside all the relevant sets
  have hnhds : (e'.target ∩ e'.symm ⁻¹' e.source) ∩
      ((e ∘ e'.symm) ⁻¹' ball (e x) ρ ∩ {w | AnalyticAt ℂ (e ∘ e'.symm) w}) ∈ 𝓝 (e' x) := by
    refine Filter.inter_mem (hWopen.mem_nhds hxW) (Filter.inter_mem ?_ ?_)
    · refine ContinuousAt.preimage_mem_nhds htrans.continuousAt ?_
      have hφx : (e ∘ e'.symm) (e' x) = e x := by simp [Function.comp, e'.left_inv hxe']
      rw [hφx]
      exact ball_mem_nhds _ hρpos
    · exact htrans.eventually_analyticAt
  obtain ⟨δ, hδpos, hδball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnhds
  -- harmonicity of the composition on that ball
  have hcomp : HarmonicOnNhd ((u ∘ e.symm) ∘ (e ∘ e'.symm)) (ball (e' x) δ) := by
    refine HarmonicOnNhd.comp_analytic (fun y hy ↦ hball y hy) isOpen_ball
      (fun w hw ↦ (hδball hw).2.2) fun w hw ↦ (hδball hw).2.1
  -- transfer along the congruence
  have hcongr : u ∘ e'.symm =ᶠ[𝓝 (e' x)] (u ∘ e.symm) ∘ (e ∘ e'.symm) := by
    filter_upwards [hWopen.mem_nhds hxW] with w hw
    simp [Function.comp, e.left_inv hw.2]
  exact (harmonicAt_congr_nhds hcongr).mpr (hcomp _ (mem_ball_self hδpos))

theorem surfaceSubharmonicOn (hu : SurfaceHarmonicOn u s) :
    SurfaceSubharmonicOn u s where
  continuousOn := hu.continuousOn
  subMeanOn e he :=
    (HarmonicOnNhd.meanEqOn (hu e he)).subMeanOn

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem neg (hu : SurfaceHarmonicOn u s) : SurfaceHarmonicOn (-u) s :=
  fun e he z hz ↦ (hu e he z hz).neg

end SurfaceHarmonicOn

namespace SurfaceSubharmonicOn

variable {g g₁ g₂ : X → ℝ} {s : Set X}

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem mono (hg : SurfaceSubharmonicOn g s) {t : Set X} (hts : t ⊆ s) :
    SurfaceSubharmonicOn g t where
  continuousOn := hg.continuousOn.mono hts
  subMeanOn e he := (hg.subMeanOn e he).mono (image_mono (inter_subset_inter_left _ hts))

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem max (h₁ : SurfaceSubharmonicOn g₁ s) (h₂ : SurfaceSubharmonicOn g₂ s) :
    SurfaceSubharmonicOn (fun x ↦ Max.max (g₁ x) (g₂ x)) s where
  continuousOn := ContinuousOn.sup h₁.continuousOn h₂.continuousOn
  subMeanOn e he := (h₁.subMeanOn e he).max (h₂.subMeanOn e he)

end SurfaceSubharmonicOn

/-! ## Local-to-global bridge for the sub-mean-value property

`SubMeanOn` (in `Rado/Complex/SubMean.lean`) demands the sub-mean inequality on
*every* circle whose closed disk lies in the domain. Verifications (gluing in
the harmonic replacement) naturally produce only *small* circles. The bridge is
classical: small circles give the maximum principle, the maximum principle
gives comparison with the Poisson extension on any closed disk, and comparison
gives the inequality on the full circle
(`InnerProductSpace.HarmonicContOnCl.circleAverage_eq` closes the loop at the boundary radius).
-/

/-- Continuity plus the sub-mean-value inequality on all sufficiently small
circles around each point. -/
structure SubMeanLocalOn (g : ℂ → ℝ) (s : Set ℂ) : Prop where
  continuousOn : ContinuousOn g s
  submean_small : ∀ z ∈ s, ∀ᶠ r in 𝓝[>] (0 : ℝ), g z ≤ Real.circleAverage g z r

theorem SubMeanLocalOn.mono {g : ℂ → ℝ} {s t : Set ℂ} (hg : SubMeanLocalOn g s) (hts : t ⊆ s) :
    SubMeanLocalOn g t :=
  ⟨hg.continuousOn.mono hts, fun z hz ↦ hg.submean_small z (hts hz)⟩

/-- If a continuous function is at most `M` on a sphere of positive radius while its
circle average is at least `M`, then it equals `M` everywhere on the sphere. -/
private lemma eqOn_sphere_of_le_of_circleAverage_ge {g : ℂ → ℝ} {a : ℂ} {r M : ℝ}
    (hr : 0 < r) (hc : ContinuousOn g (sphere a r)) (hle : ∀ z ∈ sphere a r, g z ≤ M)
    (havg : M ≤ Real.circleAverage g a r) : ∀ z ∈ sphere a r, g z = M := by
  intro z hz
  by_contra hne
  have hzlt : g z < M := lt_of_le_of_ne (hle z hz) hne
  -- find a parameter `θ₀ ∈ Icc 0 (2π)` hitting `z`
  have hz' : z ∈ Set.range (circleMap a r) := by
    rw [range_circleMap, abs_of_pos hr]; exact hz
  obtain ⟨θ, hθ⟩ := hz'
  have hmem : toIocMod Real.two_pi_pos 0 θ ∈ Set.Ioc 0 (2 * Real.pi) := by
    simpa using toIocMod_mem_Ioc Real.two_pi_pos 0 θ
  have hθ₀ : circleMap a r (toIocMod Real.two_pi_pos 0 θ) = z := by
    rw [← self_sub_toIocDiv_zsmul Real.two_pi_pos 0 θ, (periodic_circleMap a r).sub_zsmul_eq]
    exact hθ
  -- strict inequality of interval integrals
  have hcont : Continuous fun θ ↦ g (circleMap a r θ) :=
    hc.comp_continuous (continuous_circleMap a r) fun θ ↦ circleMap_mem_sphere a hr.le θ
  have hint : (∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap a r θ))
      < ∫ _ in (0:ℝ)..2 * Real.pi, M := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      Real.two_pi_pos hcont.continuousOn continuousOn_const
      (fun x _ ↦ hle _ (circleMap_mem_sphere a hr.le x)) ?_
    exact ⟨toIocMod Real.two_pi_pos 0 θ, Set.Ioc_subset_Icc_self hmem, by rw [hθ₀]; exact hzlt⟩
  have hlt : Real.circleAverage g a r < M := by
    rw [Real.circleAverage_def, smul_eq_mul]
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap a r θ)
        < (2 * Real.pi)⁻¹ * ∫ _ in (0:ℝ)..2 * Real.pi, M := by
          exact mul_lt_mul_of_pos_left hint (by positivity)
      _ = M := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc,
            inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]
  exact absurd havg (not_le.mpr hlt)

/-- Small circles suffice for the strong maximum principle. -/
theorem SubMeanLocalOn.eqOn_const_of_isMaxOn {g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hsc : IsPreconnected s) (hg : SubMeanLocalOn g s) {x₀ : ℂ} (hx₀ : x₀ ∈ s)
    (hmax : IsMaxOn g s x₀) : EqOn g (fun _ ↦ g x₀) s := by
  set M := g x₀ with hM
  set A : Set ℂ := {x ∈ s | g x = M} with hA
  set B : Set ℂ := {x ∈ s | g x ≠ M} with hB
  -- `A` is open: around each of its points, `g = M` on all small spheres
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro a ⟨has, hga⟩
    obtain ⟨ε, hε, hballs⟩ := Metric.isOpen_iff.mp hs a has
    obtain ⟨ρ, hρ, hsmall⟩ : ∃ ρ > (0:ℝ), ∀ r ∈ Ioo (0:ℝ) ρ, g a ≤ Real.circleAverage g a r := by
      obtain ⟨u, hu, huss⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hg.submean_small a has)
      exact ⟨u, hu, fun r hr ↦ huss hr⟩
    refine ⟨min ε ρ, lt_min hε hρ, fun y hy ↦ ?_⟩
    have hylt : dist y a < min ε ρ := mem_ball.mp hy
    rcases eq_or_ne y a with rfl | hne
    · exact ⟨has, hga⟩
    · have hrpos : 0 < dist y a := dist_pos.mpr hne
      have hcb : closedBall a (dist y a) ⊆ s :=
        (closedBall_subset_ball (hylt.trans_le (min_le_left _ _))).trans hballs
      have hsph : sphere a (dist y a) ⊆ s := sphere_subset_closedBall.trans hcb
      have h1 : ∀ z ∈ sphere a (dist y a), g z ≤ M := fun z hz ↦ hmax (hsph hz)
      have h2 : M ≤ Real.circleAverage g a (dist y a) := by
        rw [← hga]
        exact hsmall _ ⟨hrpos, hylt.trans_le (min_le_right _ _)⟩
      have heq := eqOn_sphere_of_le_of_circleAverage_ge hrpos
        (hg.continuousOn.mono hsph) h1 h2
      exact ⟨hballs (mem_ball.mpr (hylt.trans_le (min_le_left _ _))),
        heq y (mem_sphere.mpr rfl)⟩
  -- `B` is open by continuity
  have hBopen : IsOpen B := by
    have hBeq : B = s ∩ g ⁻¹' {M}ᶜ := by
      ext x
      simp [hB]
    rw [hBeq]
    exact hg.continuousOn.isOpen_inter_preimage hs isOpen_compl_singleton
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hxM⟩ ⟨_, hxM'⟩
    exact hxM' hxM
  have hcover : s ⊆ A ∪ B := fun x hx ↦ by
    by_cases h : g x = M
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  rcases hsc.subset_or_subset hAopen hBopen hdisj hcover with hsA | hsB
  · intro x hx
    exact (hsA hx).2
  · exact absurd hM.symm (hsB hx₀).2

/-- Small circles suffice for the boundary comparison principle. -/
theorem SubMeanLocalOn.le_of_frontier_le {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hg : SubMeanLocalOn g U)
    (hgc : ContinuousOn g (closure U)) {M : ℝ} (hbd : ∀ x ∈ frontier U, g x ≤ M) :
    ∀ x ∈ closure U, g x ≤ M := by
  intro x hx
  have hKc : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨z, hzK, hzmax⟩ := hKc.exists_isMaxOn ⟨x, hx⟩ hgc
  suffices h : g z ≤ M from le_trans (hzmax hx) h
  by_cases hzU : z ∈ U
  · -- interior maximum: `g` is constant on the connected component of `z` in `U`
    have hCopen : IsOpen (connectedComponentIn U z) := hU.connectedComponentIn
    have hCU : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
    have hzC : z ∈ connectedComponentIn U z := mem_connectedComponentIn hzU
    have hmaxC : IsMaxOn g (connectedComponentIn U z) z := fun y hy ↦
      hzmax (subset_closure (hCU hy))
    have heq : EqOn g (fun _ ↦ g z) (connectedComponentIn U z) :=
      (hg.mono hCU).eqOn_const_of_isMaxOn hCopen isPreconnected_connectedComponentIn hzC hmaxC
    -- the component has nonempty frontier since it is bounded and nonempty
    have hfr : (frontier (connectedComponentIn U z)).Nonempty := by
      rw [nonempty_frontier_iff]
      refine ⟨⟨z, hzC⟩, fun huniv ↦ ?_⟩
      have hCb : Bornology.IsBounded (connectedComponentIn U z) := hUb.subset hCU
      rw [huniv] at hCb
      exact NormedSpace.unbounded_univ ℝ ℂ hCb
    obtain ⟨b, hb⟩ := hfr
    have hbC : b ∈ closure (connectedComponentIn U z) := frontier_subset_closure hb
    have hbU : b ∈ closure U := closure_mono hCU hbC
    -- `g b = g z` by continuity up to the closure
    have hgb : g b = g z := by
      have h1 : ContinuousWithinAt g (connectedComponentIn U z) b :=
        (hgc.continuousWithinAt hbU).mono (hCU.trans subset_closure)
      have hne : (𝓝[connectedComponentIn U z] b).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp hbC
      have h2 : Filter.Tendsto g (𝓝[connectedComponentIn U z] b) (𝓝 (g z)) :=
        Filter.Tendsto.congr'
          (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun y hy ↦ (heq hy).symm)
          tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    -- `b` lies on the frontier of `U`
    have hbfr : b ∈ frontier U := by
      rw [hU.frontier_eq]
      refine ⟨hbU, fun hbU' ↦ ?_⟩
      have hCb' : connectedComponentIn U b ∈ 𝓝 b :=
        (hU.connectedComponentIn).mem_nhds (mem_connectedComponentIn hbU')
      obtain ⟨y, hyt, hyC⟩ := mem_closure_iff_nhds.mp hbC _ hCb'
      have hcomp : connectedComponentIn U b = connectedComponentIn U z := by
        rw [connectedComponentIn_eq hyt, connectedComponentIn_eq hyC]
      have hbmem : b ∈ connectedComponentIn U z := hcomp ▸ mem_connectedComponentIn hbU'
      have hbnot : b ∉ connectedComponentIn U z := by
        rw [hCopen.frontier_eq] at hb
        exact hb.2
      exact hbnot hbmem
    calc g z = g b := hgb.symm
      _ ≤ M := hbd b hbfr
  · exact hbd z (by rw [hU.frontier_eq]; exact ⟨hzK, hzU⟩)

/-- The bridge: on an open set, the sub-mean-value inequality on small circles
implies it on all circles (compare with the Poisson extension on any legal
closed disk). -/
theorem SubMeanLocalOn.subMeanOn {g : ℂ → ℝ} {s : Set ℂ}
    (hg : SubMeanLocalOn g s) : SubMeanOn g s := by
  refine ⟨hg.continuousOn, fun c R hR hsub ↦ ?_⟩
  have hgs : ContinuousOn g (sphere c R) :=
    hg.continuousOn.mono (sphere_subset_closedBall.trans hsub)
  have hPc : ContinuousOn (poissonExtension g c R) (closedBall c R) :=
    poissonExtension_continuousOn hR hgs
  have hPh : HarmonicOnNhd (poissonExtension g c R) (ball c R) :=
    poissonExtension_harmonicOnNhd hR hgs
  have hPm : MeanEqOn (poissonExtension g c R) (ball c R) :=
    HarmonicOnNhd.meanEqOn hPh
  -- `g - P` satisfies the small-circle sub-mean inequality on the open ball
  have hloc : SubMeanLocalOn (fun z ↦ g z - poissonExtension g c R z) (ball c R) := by
    constructor
    · exact (hg.continuousOn.mono (ball_subset_closedBall.trans hsub)).sub
        (hPc.mono ball_subset_closedBall)
    · intro z hz
      have hzs : z ∈ s := hsub (ball_subset_closedBall hz)
      have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall z r ⊆ ball c R := by
        have hpos : 0 < R - dist z c := by
          rw [mem_ball] at hz; linarith
        filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
        exact closedBall_subset_ball' (by have := hr.2; linarith)
      filter_upwards [hg.submean_small z hzs, h2, self_mem_nhdsWithin] with r hr1 hr2 hr3
      have hrpos : (0:ℝ) < r := hr3
      have hsph_s : sphere z r ⊆ s :=
        sphere_subset_closedBall.trans (hr2.trans (ball_subset_closedBall.trans hsub))
      have hsph_cb : sphere z r ⊆ closedBall c R :=
        sphere_subset_closedBall.trans (hr2.trans ball_subset_closedBall)
      have hig : CircleIntegrable g z r :=
        (hg.continuousOn.mono hsph_s).circleIntegrable hrpos.le
      have hiP : CircleIntegrable (poissonExtension g c R) z r :=
        (hPc.mono hsph_cb).circleIntegrable hrpos.le
      have havg : Real.circleAverage (fun w ↦ g w - poissonExtension g c R w) z r
          = Real.circleAverage g z r - Real.circleAverage (poissonExtension g c R) z r :=
        Real.circleAverage_fun_sub hig hiP
      change g z - poissonExtension g c R z
          ≤ Real.circleAverage (fun w ↦ g w - poissonExtension g c R w) z r
      rw [havg, hPm.mean_eq z r hrpos hr2]
      exact sub_le_sub_right hr1 _
  -- comparison on the closed ball
  have hcl : closure (ball c R) = closedBall c R := closure_ball c hR.ne'
  have hfr : ∀ x ∈ frontier (ball c R), g x - poissonExtension g c R x ≤ 0 := by
    intro x hx
    rw [frontier_ball c hR.ne'] at hx
    rw [poissonExtension_eqOn_sphere hR hgs hx]
    simp
  have hcomp := hloc.le_of_frontier_le isOpen_ball isBounded_ball
    (by rw [hcl]; exact (hg.continuousOn.mono hsub).sub hPc) hfr
  have h0 := hcomp c (by rw [hcl]; exact mem_closedBall_self hR.le)
  simp only [sub_nonpos] at h0
  -- mean value at the boundary radius
  have hPcirc : Real.circleAverage (poissonExtension g c R) c R = poissonExtension g c R c := by
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_eq
    rw [abs_of_pos hR]
    exact HarmonicContOnCl.mk_ball hPh hPc
  have hcongr : Real.circleAverage (poissonExtension g c R) c R = Real.circleAverage g c R := by
    apply Real.circleAverage_congr_sphere
    rw [abs_of_pos hR]
    exact poissonExtension_eqOn_sphere hR hgs
  calc g c ≤ poissonExtension g c R c := h0
    _ = Real.circleAverage (poissonExtension g c R) c R := hPcirc.symm
    _ = Real.circleAverage g c R := hcongr

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Subharmonicity is local. -/
theorem SurfaceSubharmonicOn.of_locally {g : X → ℝ} {s : Set X}
    (h : ∀ x ∈ s, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ s ∧ SurfaceSubharmonicOn g V) :
    SurfaceSubharmonicOn g s := by
  have hcont : ContinuousOn g s := by
    intro x hx
    obtain ⟨V, hVo, hxV, hVs, hgV⟩ := h x hx
    exact (hgV.continuousOn.continuousAt (hVo.mem_nhds hxV)).continuousWithinAt
  refine ⟨hcont, fun e he ↦ ?_⟩
  refine SubMeanLocalOn.subMeanOn ?_
  refine ⟨continuousOn_comp_chart_symm e hcont, ?_⟩
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  obtain ⟨V, hVo, hxV, hVs, hgV⟩ := h x hxs
  have hsm : SubMeanOn (g ∘ e.symm) (chartImage e V) := hgV.subMeanOn e he
  have hmem : e x ∈ chartImage e V := mem_chartImage_of_mem hxV hxe
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage e hVo) _ hmem
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  exact hsm.submean (e x) r hr.1 ((closedBall_subset_ball hr.2).trans hball)

end Rado
