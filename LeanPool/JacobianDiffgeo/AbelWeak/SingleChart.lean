/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.AbelWeak.PlanarLogBranch
import LeanPool.JacobianDiffgeo.AbelWeak.WeakSolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The single-chart weak solution (`abel-weak-solutions`, §6.2-6.3)

Unit: abel-weak-solutions (`docs/design/abel-weak-solutions.md` §6.2-6.3). Given two distinct
points `P, Q` lying inside a common chart `e`, both within `ball c ρ` for some `c, ρ`, and a
`ContDiffBump (0 : ℂ)` cutoff `ψ` with `ρ < ψ.rIn`, `closedBall c ψ.rOut ⊆ e.target`: builds a
weak solution of the pair `(P, Q)`, equal to `1` outside the compact set
`e.symm '' closedBall c ψ.rOut`.

The construction (`exists_weakSolutionOfPair_chart`): the planar function
`g z := if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q) else exp(ψ(z - c) * L(z - c))`, where `L` is
the exterior log-branch (`PlanarLogBranch.exists_exteriorLogBranch`) of `(z-eP)/(z-eQ)` recentred
at `c`. The bump's `one_of_mem_closedBall`/`zero_of_le_dist` make `g` interpolate exactly from the
rational function (near `c`) to the constant `1` (far from `c`), with **no matching argument
beyond `Set.EqOn`-rewriting** on the transition annulus (the same shape the design's §6.2 step 1
describes).
-/

open scoped ContDiff Manifold
open IsManifold Metric Set Filter Topology

noncomputable section

namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [ChartedSpace ℂ X] in
/-- The planar model is real-smooth away from the two marked points. Split out of
`exists_weakSolutionOfPair_chart` to keep that proof under the 200-line size we hold ourselves
to; `g` is rebuilt here so the argument reads exactly as it did inline. -/
private theorem contDiffAt_planar_model {P Q : X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {ρ : ℝ}
    (ψ : ContDiffBump (0 : ℂ)) (hρψ : ρ < ψ.rIn) (L : ℂ → ℂ)
    (heq_inner : Set.EqOn (fun z => if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q)
        else Complex.exp ((ψ (z - c) : ℝ) * L (z - c)))
      (fun z => (z - e P) / (z - e Q)) (Metric.ball c ψ.rIn))
    (hLderiv : ∀ z ∈ {z : ℂ | ρ < ‖z‖}, HasDerivAt L
      (1 / (z - (e P - c)) - 1 / (z - (e Q - c))) z) :
    ∀ z : ℂ, z ≠ e Q → ContDiffAt ℝ ∞ (fun z => if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q)
      else Complex.exp ((ψ (z - c) : ℝ) * L (z - c))) z := by
  set g : ℂ → ℂ := fun z =>
    if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q) else Complex.exp ((ψ (z - c) : ℝ) * L (z - c))
    with hg_def
  change ∀ z : ℂ, z ≠ e Q → ContDiffAt ℝ ∞ g z
  intro z hzQ
  by_cases hcase : ‖z - c‖ < ψ.rIn
  · have hzmem : z ∈ Metric.ball c ψ.rIn := by rw [Metric.mem_ball, dist_eq_norm]; exact hcase
    have heq : g =ᶠ[𝓝 z] (fun w => (w - e P) / (w - e Q)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with w hw using heq_inner hw
    have hdiff : ContDiffAt ℝ ∞ (fun w : ℂ => (w - e P) / (w - e Q)) z := by
      have h1 : ContDiffAt ℂ ∞ (fun w : ℂ => (w - e P) / (w - e Q)) z :=
        (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const)
          (sub_ne_zero.mpr hzQ)
      exact h1.restrict_scalars ℝ
    exact hdiff.congr_of_eventuallyEq heq
  · rw [not_lt] at hcase
    have hzρ : ρ < ‖z - c‖ := lt_of_lt_of_le hρψ hcase
    have hopen : IsOpen {w : ℂ | ρ < ‖w - c‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    have heq : g =ᶠ[𝓝 z] (fun w => Complex.exp ((ψ (w - c) : ℝ) * L (w - c))) := by
      filter_upwards [hopen.mem_nhds hzρ] with w hw
      change (if ‖w - c‖ ≤ ρ then (w - e P) / (w - e Q) else
        Complex.exp ((ψ (w - c) : ℝ) * L (w - c))) = Complex.exp ((ψ (w - c) : ℝ) * L (w - c))
      exact if_neg (not_le.mpr hw)
    have hL_diffOn : DifferentiableOn ℂ L {w : ℂ | ρ < ‖w‖} :=
      fun w hw => (hLderiv w hw).differentiableAt.differentiableWithinAt
    have hL_contDiffAt : ContDiffAt ℝ ∞ (fun w : ℂ => L (w - c)) z := by
      have hLan : AnalyticOnNhd ℂ L {w : ℂ | ρ < ‖w‖} := hL_diffOn.analyticOnNhd
        (isOpen_lt continuous_const continuous_norm)
      have h1 : ContDiffAt ℂ ∞ L (z - c) := (hLan (z - c) hzρ).contDiffAt
      have h2 : ContDiffAt ℝ ∞ L (z - c) := h1.restrict_scalars ℝ
      have hsub : ContDiffAt ℝ ∞ (fun w : ℂ => w - c) z :=
        contDiffAt_id.sub contDiffAt_const
      exact h2.comp z hsub
    have hψ_contDiffAt : ContDiffAt ℝ ∞ (fun w : ℂ => ψ (w - c)) z := by
      have hsub : ContDiffAt ℝ ∞ (fun w : ℂ => w - c) z := contDiffAt_id.sub contDiffAt_const
      have hcomp : ContDiffAt ℝ ∞ ((⇑ψ) ∘ (fun w : ℂ => w - c)) z :=
        ψ.contDiffAt.comp z hsub
      exact hcomp
    have hψ_ofReal : ContDiffAt ℝ ∞ (fun w : ℂ => ((ψ (w - c) : ℝ) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z hψ_contDiffAt
    have hprod : ContDiffAt ℝ ∞ (fun w : ℂ => ((ψ (w - c) : ℝ) : ℂ) * L (w - c)) z :=
      hψ_ofReal.mul hL_contDiffAt
    have hexp : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.exp (((ψ (w - c) : ℝ) : ℂ) * L (w - c))) z :=
      (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z hprod
    exact hexp.congr_of_eventuallyEq heq

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **The single-chart weak solution** (§6.2-6.3). -/
theorem exists_weakSolutionOfPair_chart {P Q : X} (hPQ : P ≠ Q)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hPs : P ∈ e.source) (hQs : Q ∈ e.source)
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (haQ : e Q - c ∈ Metric.ball (0 : ℂ) ρ) (haP : e P - c ∈ Metric.ball (0 : ℂ) ρ)
    (ψ : ContDiffBump (0 : ℂ)) (hρψ : ρ < ψ.rIn)
    (hballsub : Metric.closedBall c ψ.rOut ⊆ e.target) :
    ∃ f : X → ℂ, IsWeakSolutionOfPair f P Q ∧
      IsOpen (e.symm '' Metric.ball c ψ.rOut) ∧
      IsCompact (closure (e.symm '' Metric.ball c ψ.rOut)) ∧
      P ∈ e.symm '' Metric.ball c ψ.rOut ∧ Q ∈ e.symm '' Metric.ball c ψ.rOut ∧
      (∀ x ∉ e.symm '' Metric.ball c ψ.rOut, f x = 1) := by
  classical
  -- `e P ≠ e Q` from `P ≠ Q` and injectivity of `e` on its source.
  have hePQ : e P ≠ e Q := fun h => hPQ (by rw [← e.left_inv hPs, h, e.left_inv hQs])
  set a' : ℂ := e Q - c with ha'_def
  set b' : ℂ := e P - c with hb'_def
  obtain ⟨L, hLderiv, hLexp⟩ := exists_exteriorLogBranch hρ haQ haP
  -- The planar construction, as a function of the ORIGINAL chart coordinate `z` (not `z - c`).
  set g : ℂ → ℂ := fun z =>
    if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q) else Complex.exp ((ψ (z - c) : ℝ) * L (z - c))
    with hg_def
  -- Step 1: consistency on the transition annulus `{ρ < ‖z-c‖ ≤ ψ.rIn}`.
  have hg_consistent : ∀ z : ℂ, ρ < ‖z - c‖ → ‖z - c‖ ≤ ψ.rIn → g z = (z - e P) / (z - e Q) := by
    intro z hz1 hz2
    have hψ1 : ψ (z - c) = 1 := ψ.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using hz2)
    have hzne : ¬ ‖z - c‖ ≤ ρ := not_le.mpr hz1
    change (if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q) else
      Complex.exp ((ψ (z - c) : ℝ) * L (z - c))) = (z - e P) / (z - e Q)
    rw [if_neg hzne, hψ1]
    have := hLexp (z - c) hz1
    change Complex.exp ((1 : ℝ) * L (z - c)) = (z - e P) / (z - e Q)
    rw [show ((1 : ℝ) : ℂ) * L (z - c) = L (z - c) by push_cast; ring, this]
    show (z - c - b') / (z - c - a') = (z - e P) / (z - e Q)
    rw [ha'_def, hb'_def]
    congr 1 <;> ring
  -- Step 2: `g ≡ 1` outside `closedBall c ψ.rOut`.
  have hg_one : ∀ z : ℂ, ψ.rOut ≤ ‖z - c‖ → g z = 1 := by
    intro z hz
    have hzρ : ρ < ‖z - c‖ := lt_of_lt_of_le (hρψ.trans ψ.rIn_lt_rOut) hz
    have hψ0 : ψ (z - c) = 0 := ψ.zero_of_le_dist (by rw [dist_zero_right]; exact hz)
    change (if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q) else
      Complex.exp ((ψ (z - c) : ℝ) * L (z - c))) = 1
    rw [if_neg (not_le.mpr hzρ), hψ0]
    simp
  -- Step 3: `g` agrees with the rational function on the whole ball `ball c ψ.rIn`.
  have heq_inner : Set.EqOn g (fun z => (z - e P) / (z - e Q)) (Metric.ball c ψ.rIn) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    by_cases h : ‖z - c‖ ≤ ρ
    · change (if ‖z - c‖ ≤ ρ then (z - e P) / (z - e Q) else
        Complex.exp ((ψ (z - c) : ℝ) * L (z - c))) = (z - e P) / (z - e Q)
      rw [if_pos h]
    · exact hg_consistent z (not_le.mp h) hz.le
  -- Step 4: `ContDiffAt ℝ ∞ g z` for every `z ≠ e Q`.
  have hg_contDiffAt := contDiffAt_planar_model ψ hρψ L heq_inner hLderiv
  -- `ψ.rIn < ψ.rOut`, hence `ρ < ψ.rOut` (needed repeatedly below).
  have hρψ'' : ρ < ψ.rOut := hρψ.trans ψ.rIn_lt_rOut
  have hball_sub_target : Metric.ball c ψ.rOut ⊆ e.target :=
    Metric.ball_subset_closedBall.trans hballsub
  -- The global function on `X`.
  set f : X → ℂ := Set.piecewise e.source (fun x => g (e x)) (fun _ => 1) with hf_def
  have hf_source : ∀ x ∈ e.source, f x = g (e x) := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hf_not_source : ∀ x, x ∉ e.source → f x = 1 :=
    fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx
  -- `K`: the compact "support" of the transition, `U`: the open set the deliverable needs.
  set K : Set X := e.symm '' Metric.closedBall c ψ.rOut with hK_def
  set U : Set X := e.symm '' Metric.ball c ψ.rOut with hU_def
  have hK_sub_source : K ⊆ e.source := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_target (hballsub hz)
  have hK_compact : IsCompact K :=
    (isCompact_closedBall c ψ.rOut).image_of_continuousOn (e.symm.continuousOn.mono hballsub)
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hU_open : IsOpen U :=
      e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hball_sub_target
  have hU_sub_K : U ⊆ K := Set.image_mono Metric.ball_subset_closedBall
  have hclosureU_sub_K : closure U ⊆ K := closure_minimal hU_sub_K hK_closed
  have hclosureU_compact : IsCompact (closure U) :=
    hK_compact.of_isClosed_subset isClosed_closure hclosureU_sub_K
  -- Membership of `y ∈ e.source` in `K`/`U` reads off `e y`.
  have hmem_K_iff : ∀ y, y ∈ e.source → (y ∈ K ↔ e y ∈ Metric.closedBall c ψ.rOut) := by
    intro y hy
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hez : e y = z := by rw [← hzy, e.right_inv (hballsub hz)]
      rwa [hez]
    · intro hz
      exact ⟨e y, hz, e.left_inv hy⟩
  have hmem_U_iff : ∀ y, y ∈ e.source → (y ∈ U ↔ e y ∈ Metric.ball c ψ.rOut) := by
    intro y hy
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hez : e y = z := by rw [← hzy, e.right_inv (hball_sub_target hz)]
      rwa [hez]
    · intro hz
      exact ⟨e y, hz, e.left_inv hy⟩
  -- `f ≡ 1` off `K` (hence off `U ⊆ K` too), used for the smoothness argument.
  have hf_one_off_K : ∀ y ∉ K, f y = 1 := by
    intro y hyK
    by_cases hye : y ∈ e.source
    · have hnotmem : ¬ e y ∈ Metric.closedBall c ψ.rOut := fun h => hyK ((hmem_K_iff y hye).2 h)
      rw [Metric.mem_closedBall] at hnotmem
      push Not at hnotmem
      have hgeq1 : g (e y) = 1 := hg_one (e y) (le_of_lt (by rwa [dist_eq_norm] at hnotmem))
      rw [hf_source y hye, hgeq1]
    · exact hf_not_source y hye
  have hf_one_off_U : ∀ x ∉ U, f x = 1 := by
    intro x hxU
    by_cases hxe : x ∈ e.source
    · have hnotmem : ¬ e x ∈ Metric.ball c ψ.rOut := fun h => hxU ((hmem_U_iff x hxe).2 h)
      rw [Metric.mem_ball] at hnotmem
      push Not at hnotmem
      have hgeq1 : g (e x) = 1 := hg_one (e x) (by rwa [dist_eq_norm] at hnotmem)
      rw [hf_source x hxe, hgeq1]
    · exact hf_not_source x hxe
  -- `P, Q ∈ U`.
  have hPU : P ∈ U := (hmem_U_iff P hPs).2 (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_trans (by rwa [Metric.mem_ball, dist_zero_right] at haP) hρψ'')
  have hQU : Q ∈ U := (hmem_U_iff Q hQs).2 (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_trans (by rwa [Metric.mem_ball, dist_zero_right] at haQ) hρψ'')
  -- The weak-solution structure.
  have hf_contMDiffOn : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {Q}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    by_cases hxe : x ∈ e.source
    · have hexQ : e x ≠ e Q := fun h => hx (by rw [← e.left_inv hxe, h, e.left_inv hQs])
      have hcm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g ∘ e) x :=
        contMDiffAt_comp_of_contDiffAt he hxe (hg_contDiffAt (e x) hexQ)
      have heqf : f =ᶠ[𝓝 x] (g ∘ e) := by
        filter_upwards [e.open_source.mem_nhds hxe] with y hy using hf_source y hy
      exact (hcm.congr_of_eventuallyEq heqf).contMDiffWithinAt
    · have hxK : x ∉ K := fun hxK' => hxe (hK_sub_source hxK')
      have hopenK : IsOpen Kᶜ := hK_closed.isOpen_compl
      have heqf : f =ᶠ[𝓝 x] (fun _ : X => (1 : ℂ)) := by
        filter_upwards [hopenK.mem_nhds hxK] with y hy
        exact hf_one_off_K y hy
      exact (contMDiffAt_const.congr_of_eventuallyEq heqf).contMDiffWithinAt
  have hf_ne_zero_off : ∀ x, x ≠ P → x ≠ Q → f x ≠ 0 := by
    intro x hxP hxQ
    by_cases hxe : x ∈ e.source
    · rw [hf_source x hxe]
      have hexP : e x ≠ e P := fun h => hxP (by rw [← e.left_inv hxe, h, e.left_inv hPs])
      have hexQ : e x ≠ e Q := fun h => hxQ (by rw [← e.left_inv hxe, h, e.left_inv hQs])
      by_cases hcase : ‖e x - c‖ ≤ ρ
      · change (if ‖e x - c‖ ≤ ρ then (e x - e P) / (e x - e Q) else
          Complex.exp ((ψ (e x - c) : ℝ) * L (e x - c))) ≠ 0
        rw [if_pos hcase]
        exact div_ne_zero (sub_ne_zero.mpr hexP) (sub_ne_zero.mpr hexQ)
      · change (if ‖e x - c‖ ≤ ρ then (e x - e P) / (e x - e Q) else
          Complex.exp ((ψ (e x - c) : ℝ) * L (e x - c))) ≠ 0
        rw [if_neg hcase]
        exact Complex.exp_ne_zero _
    · rw [hf_not_source x hxe]; exact one_ne_zero
  have hf_weakAt_P : IsWeakSolutionAt f P 1 := by
    refine ⟨e, he, hPs, fun z => 1 / (z - e Q), ?_, ?_, ?_⟩
    · have hnhds : {e Q}ᶜ ∈ 𝓝 (e P) := isOpen_compl_singleton.mem_nhds hePQ
      filter_upwards [hnhds] with z hz
      exact div_ne_zero one_ne_zero (sub_ne_zero.mpr hz)
    · have h1 : ContDiffAt ℂ ∞ (fun z : ℂ => 1 / (z - e Q)) (e P) :=
        contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hePQ)
      exact h1.restrict_scalars ℝ
    · have hballnhds : ∀ᶠ x in 𝓝 P, x ∈ e.source ∧ ‖e x - c‖ ≤ ρ := by
        have h1 : ∀ᶠ x in 𝓝 P, x ∈ e.source := e.open_source.mem_nhds hPs
        have h2 : ∀ᶠ x in 𝓝 P, ‖e x - c‖ < ρ := by
          have hcont : ContinuousAt e P :=
            (contMDiffAt_of_mem_maximalAtlas he hPs).continuousAt
          have := hcont.tendsto.eventually (Metric.isOpen_ball.eventually_mem
            (show e P ∈ Metric.ball c ρ by simpa [Metric.mem_ball, dist_eq_norm] using haP))
          filter_upwards [this] with x hx
          rwa [Metric.mem_ball, dist_eq_norm] at hx
        filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2.le⟩
      filter_upwards [hballnhds] with x hx
      obtain ⟨hxe, hxρ⟩ := hx
      show f x = 1 / (e x - e Q) * (e x - e P) ^ (1 : ℤ)
      rw [hf_source x hxe]
      change (if ‖e x - c‖ ≤ ρ then (e x - e P) / (e x - e Q) else
        Complex.exp ((ψ (e x - c) : ℝ) * L (e x - c))) = 1 / (e x - e Q) * (e x - e P) ^ (1 : ℤ)
      rw [if_pos hxρ, zpow_one]
      ring
  have hf_weakAt_Q : IsWeakSolutionAt f Q (-1) := by
    refine ⟨e, he, hQs, fun z => z - e P, ?_, ?_, ?_⟩
    · have hnhds : {e P}ᶜ ∈ 𝓝 (e Q) := isOpen_compl_singleton.mem_nhds hePQ.symm
      filter_upwards [hnhds] with z hz
      exact sub_ne_zero.mpr hz
    · exact ((contDiffAt_id.sub contDiffAt_const : ContDiffAt ℂ ∞ (fun z : ℂ => z - e P) (e Q))
        |>.restrict_scalars ℝ)
    · have hballnhds : ∀ᶠ x in 𝓝 Q, x ∈ e.source ∧ ‖e x - c‖ ≤ ρ := by
        have h1 : ∀ᶠ x in 𝓝 Q, x ∈ e.source := e.open_source.mem_nhds hQs
        have h2 : ∀ᶠ x in 𝓝 Q, ‖e x - c‖ < ρ := by
          have hcont : ContinuousAt e Q :=
            (contMDiffAt_of_mem_maximalAtlas he hQs).continuousAt
          have := hcont.tendsto.eventually (Metric.isOpen_ball.eventually_mem
            (show e Q ∈ Metric.ball c ρ by simpa [Metric.mem_ball, dist_eq_norm] using haQ))
          filter_upwards [this] with x hx
          rwa [Metric.mem_ball, dist_eq_norm] at hx
        filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2.le⟩
      filter_upwards [hballnhds] with x hx
      obtain ⟨hxe, hxρ⟩ := hx
      show f x = (e x - e P) * (e x - e Q) ^ (-1 : ℤ)
      rw [hf_source x hxe]
      change (if ‖e x - c‖ ≤ ρ then (e x - e P) / (e x - e Q) else
        Complex.exp ((ψ (e x - c) : ℝ) * L (e x - c))) = (e x - e P) * (e x - e Q) ^ (-1 : ℤ)
      rw [if_pos hxρ, zpow_neg_one]
      ring
  exact ⟨f, ⟨hf_contMDiffOn, hf_ne_zero_off, hf_weakAt_P, hf_weakAt_Q⟩,
    hU_open, hclosureU_compact, hPU, hQU, hf_one_off_U⟩

end RS.AbelWeak

end
