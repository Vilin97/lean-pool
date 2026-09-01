/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sub-mean-value functions on `ℂ` and maximum principles

`SubMeanOn g s`: `g` is continuous on `s` and satisfies the sub-mean-value
inequality `g c ≤ circleAverage g c r` for every circle whose closed disk lies
in `s`. `MeanEqOn` is the two-sided variant. These are the working notions of
sub/harmonicity at the `ℂ`-chart level (Anghel–Stan arXiv:2008.12189,
Definition 2, with all radii; Hubbard §1.2, Definition 1.2.1).

Main results: closure under `max` and under addition of a `MeanEqOn` function,
the strong maximum principle on connected opens, and the boundary comparison
principle on bounded opens. All are elementary consequences of the circle
average inequality and a clopen argument.
-/

open Set Topology Metric MeasureTheory Real

namespace Rado

/-- `g` is continuous and satisfies the sub-mean-value inequality on every
circle whose closed disk lies in `s`. -/
structure SubMeanOn (g : ℂ → ℝ) (s : Set ℂ) : Prop where
  continuousOn : ContinuousOn g s
  submean : ∀ c r, 0 < r → closedBall c r ⊆ s → g c ≤ circleAverage g c r

/-- `h` is continuous and satisfies the mean-value equality on every circle
whose closed disk lies in `s`. -/
structure MeanEqOn (h : ℂ → ℝ) (s : Set ℂ) : Prop where
  continuousOn : ContinuousOn h s
  mean_eq : ∀ c r, 0 < r → closedBall c r ⊆ s → circleAverage h c r = h c

/-- The circle average of a negated real function is the negated circle average. -/
private lemma circleAverage_neg (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    circleAverage (-f) c R = -circleAverage f c R := by
  simp only [Real.circleAverage_def, Pi.neg_apply, intervalIntegral.integral_neg, smul_neg]

theorem MeanEqOn.subMeanOn {h : ℂ → ℝ} {s : Set ℂ} (hh : MeanEqOn h s) : SubMeanOn h s :=
  ⟨hh.continuousOn, fun c r hr hsub ↦ (hh.mean_eq c r hr hsub).ge⟩

theorem MeanEqOn.neg {h : ℂ → ℝ} {s : Set ℂ} (hh : MeanEqOn h s) : MeanEqOn (-h) s := by
  refine ⟨hh.continuousOn.neg, fun c r hr hsub ↦ ?_⟩
  rw [circleAverage_neg, hh.mean_eq c r hr hsub, Pi.neg_apply]

theorem SubMeanOn.mono {g : ℂ → ℝ} {s t : Set ℂ} (hg : SubMeanOn g s) (hts : t ⊆ s) :
    SubMeanOn g t :=
  ⟨hg.continuousOn.mono hts, fun c r hr hsub ↦ hg.submean c r hr (hsub.trans hts)⟩

theorem SubMeanOn.max {g₁ g₂ : ℂ → ℝ} {s : Set ℂ} (h₁ : SubMeanOn g₁ s) (h₂ : SubMeanOn g₂ s) :
    SubMeanOn (fun z ↦ Max.max (g₁ z) (g₂ z)) s := by
  have hcmax : ContinuousOn (fun z ↦ Max.max (g₁ z) (g₂ z)) s := fun x hx ↦
    Filter.Tendsto.max (h₁.continuousOn x hx) (h₂.continuousOn x hx)
  refine ⟨hcmax, fun c r hr hsub ↦ ?_⟩
  have hsphere : sphere c r ⊆ s := sphere_subset_closedBall.trans hsub
  have hi₁ : CircleIntegrable g₁ c r := (h₁.continuousOn.mono hsphere).circleIntegrable hr.le
  have hi₂ : CircleIntegrable g₂ c r := (h₂.continuousOn.mono hsphere).circleIntegrable hr.le
  have him : CircleIntegrable (fun z ↦ Max.max (g₁ z) (g₂ z)) c r :=
    (hcmax.mono hsphere).circleIntegrable hr.le
  have le₁ : circleAverage g₁ c r ≤ circleAverage (fun z ↦ Max.max (g₁ z) (g₂ z)) c r :=
    circleAverage_mono hi₁ him fun x _ ↦ le_max_left _ _
  have le₂ : circleAverage g₂ c r ≤ circleAverage (fun z ↦ Max.max (g₁ z) (g₂ z)) c r :=
    circleAverage_mono hi₂ him fun x _ ↦ le_max_right _ _
  exact max_le ((h₁.submean c r hr hsub).trans le₁) ((h₂.submean c r hr hsub).trans le₂)

theorem SubMeanOn.add_meanEq {g h : ℂ → ℝ} {s : Set ℂ} (hg : SubMeanOn g s)
    (hh : MeanEqOn h s) : SubMeanOn (g + h) s := by
  refine ⟨hg.continuousOn.add hh.continuousOn, fun c r hr hsub ↦ ?_⟩
  have hsphere : sphere c r ⊆ s := sphere_subset_closedBall.trans hsub
  have hig : CircleIntegrable g c r := (hg.continuousOn.mono hsphere).circleIntegrable hr.le
  have hih : CircleIntegrable h c r := (hh.continuousOn.mono hsphere).circleIntegrable hr.le
  rw [circleAverage_add hig hih, hh.mean_eq c r hr hsub, Pi.add_apply]
  exact add_le_add (hg.submean c r hr hsub) le_rfl

theorem SubMeanOn.const {a : ℝ} {s : Set ℂ} : SubMeanOn (fun _ ↦ a) s :=
  ⟨continuousOn_const, fun c r _ _ ↦ (circleAverage_const a c r).ge⟩

/-- If a continuous function is at most `M` on a sphere of positive radius while its
circle average is at least `M`, then it equals `M` everywhere on the sphere. -/
private lemma eqOn_sphere_of_le_of_circleAverage_ge {g : ℂ → ℝ} {a : ℂ} {r M : ℝ}
    (hr : 0 < r) (hc : ContinuousOn g (sphere a r)) (hle : ∀ z ∈ sphere a r, g z ≤ M)
    (havg : M ≤ circleAverage g a r) : ∀ z ∈ sphere a r, g z = M := by
  intro z hz
  by_contra hne
  have hzlt : g z < M := lt_of_le_of_ne (hle z hz) hne
  -- find a parameter `θ₀ ∈ Icc 0 (2π)` hitting `z`
  have hz' : z ∈ Set.range (circleMap a r) := by
    rw [range_circleMap, abs_of_pos hr]; exact hz
  obtain ⟨θ, hθ⟩ := hz'
  have hmem : toIocMod two_pi_pos 0 θ ∈ Set.Ioc 0 (2 * π) := by
    simpa using toIocMod_mem_Ioc two_pi_pos 0 θ
  have hθ₀ : circleMap a r (toIocMod two_pi_pos 0 θ) = z := by
    rw [← self_sub_toIocDiv_zsmul two_pi_pos 0 θ, (periodic_circleMap a r).sub_zsmul_eq]
    exact hθ
  -- strict inequality of interval integrals
  have hcont : Continuous fun θ ↦ g (circleMap a r θ) :=
    hc.comp_continuous (continuous_circleMap a r) fun θ ↦ circleMap_mem_sphere a hr.le θ
  have hint : (∫ θ in (0:ℝ)..2 * π, g (circleMap a r θ)) < ∫ _ in (0:ℝ)..2 * π, M := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt two_pi_pos
      hcont.continuousOn continuousOn_const
      (fun x _ ↦ hle _ (circleMap_mem_sphere a hr.le x)) ?_
    exact ⟨toIocMod two_pi_pos 0 θ, Set.Ioc_subset_Icc_self hmem, by rw [hθ₀]; exact hzlt⟩
  have hlt : circleAverage g a r < M := by
    rw [Real.circleAverage_def, smul_eq_mul]
    calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, g (circleMap a r θ)
        < (2 * π)⁻¹ * ∫ _ in (0:ℝ)..2 * π, M := by
          exact mul_lt_mul_of_pos_left hint (by positivity)
      _ = M := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc,
            inv_mul_cancel₀ two_pi_pos.ne', one_mul]
  exact absurd havg (not_le.mpr hlt)

/-- **Strong maximum principle.** A sub-mean-value function on a connected open
set that attains its supremum is constant. -/
theorem SubMeanOn.eqOn_const_of_isMaxOn {g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hsc : IsPreconnected s) (hg : SubMeanOn g s) {x₀ : ℂ} (hx₀ : x₀ ∈ s)
    (hmax : IsMaxOn g s x₀) : EqOn g (fun _ ↦ g x₀) s := by
  set M := g x₀ with hM
  set A : Set ℂ := {x ∈ s | g x = M} with hA
  set B : Set ℂ := {x ∈ s | g x ≠ M} with hB
  -- `A` is open: around each of its points, `g = M` on all small spheres
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro a ⟨has, hga⟩
    obtain ⟨ε, hε, hballs⟩ := Metric.isOpen_iff.mp hs a has
    refine ⟨ε, hε, fun y hy ↦ ?_⟩
    rcases eq_or_ne y a with rfl | hne
    · exact ⟨has, hga⟩
    · have hrpos : 0 < dist y a := dist_pos.mpr hne
      have hrlt : dist y a < ε := mem_ball.mp hy
      have hcb : closedBall a (dist y a) ⊆ s := (closedBall_subset_ball hrlt).trans hballs
      have hsph : sphere a (dist y a) ⊆ s := sphere_subset_closedBall.trans hcb
      have h1 : ∀ z ∈ sphere a (dist y a), g z ≤ M := fun z hz ↦ hmax (hsph hz)
      have h2 : M ≤ circleAverage g a (dist y a) := by
        rw [← hga]; exact hg.submean a _ hrpos hcb
      have heq := eqOn_sphere_of_le_of_circleAverage_ge hrpos
        (hg.continuousOn.mono hsph) h1 h2
      exact ⟨hballs hy, heq y (mem_sphere.mpr rfl)⟩
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

/-- **Boundary comparison principle.** A sub-mean-value function on a bounded
open set, continuous up to the closure and `≤ M` on the frontier, is `≤ M`
everywhere on the closure. -/
theorem SubMeanOn.le_of_frontier_le {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hg : SubMeanOn g U) (hgc : ContinuousOn g (closure U))
    {M : ℝ} (hbd : ∀ x ∈ frontier U, g x ≤ M) : ∀ x ∈ closure U, g x ≤ M := by
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

/-- Uniqueness from boundary values: two mean-value functions on a bounded open
set, continuous up to the closure and equal on the frontier, agree on the
closure. -/
theorem MeanEqOn.eqOn_closure_of_frontier {u v : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hu : MeanEqOn u U) (hv : MeanEqOn v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hb : EqOn u v (frontier U)) : EqOn u v (closure U) := by
  have h1 : SubMeanOn (u + -v) U := hu.subMeanOn.add_meanEq hv.neg
  have h2 : SubMeanOn (v + -u) U := hv.subMeanOn.add_meanEq hu.neg
  have hb1 : ∀ x ∈ frontier U, (u + -v) x ≤ 0 := fun x hx ↦ by
    simp [hb hx]
  have hb2 : ∀ x ∈ frontier U, (v + -u) x ≤ 0 := fun x hx ↦ by
    simp [hb hx]
  have hle1 := h1.le_of_frontier_le hU hUb (huc.add hvc.neg) hb1
  have hle2 := h2.le_of_frontier_le hU hUb (hvc.add huc.neg) hb2
  intro x hx
  have e1 := hle1 x hx
  have e2 := hle2 x hx
  simp only [Pi.add_apply, Pi.neg_apply] at e1 e2
  linarith

end Rado
