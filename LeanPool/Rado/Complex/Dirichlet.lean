/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Complex.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# The Dirichlet problem on a disk

The deepest `ℂ`-level analytic input to Radó's theorem: for continuous boundary
data `f` on a circle, the Poisson/Schwarz integral produces a function that is
harmonic inside the disk, continuous up to the boundary, with boundary values
`f`. Mathlib's pinned version already provides the kernels
(`herglotzRieszKernel`, `poissonKernel` in `Mathlib/Analysis/Complex/Poisson.lean`,
with two-sided bounds) and the representation of an *already harmonic* function
by its Poisson integral (`Mathlib/Analysis/Complex/Harmonic/Poisson.lean`); what
is missing is the solution of the Dirichlet problem for *arbitrary* continuous
boundary data: existence is proved in `Rado/Complex/Poisson.lean`
(`exists_harmonic_extension`). The pooled LeanComplexAnalysis results
`poisson_integral_of_harmonicOn_unitDisc_continuousOn_closedUnitDisc` and
`poisson_integral_of_harmonicOn_disc_continuousOn_closedDisc` likewise assume
an existing harmonic function and prove its representation; they do not
construct a harmonic extension from arbitrary boundary data. This file
packages that complementary existence result and derives the characterizations
used by Perron's method:

* `poissonExtension` — a choice function packaging the solution, with API.
* `harmonicOnNhd_iff_meanEqOn` — harmonic ↔ continuous + mean-value property,
  on open sets (uniqueness direction via the comparison principle).
* `HarmonicOnNhd.comp_analytic` — harmonicity is preserved under holomorphic
  precomposition (via `Re`-of-holomorphic, both directions in Mathlib).
* `SubMeanOn.le_poissonExtension_on` — the comparison characterization of
  subharmonicity (Anghel–Stan Proposition 3, D1 ⇒ D3).

Here "harmonic" is Mathlib's `InnerProductSpace.HarmonicOnNhd`.
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex

namespace Rado

open Classical in
/-- The solution of the Dirichlet problem on `closedBall c R` with boundary
data `f`, extended by junk values off the closed disk and for illegal
parameters. -/
noncomputable def poissonExtension (f : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℝ :=
  if h : 0 < R ∧ ContinuousOn f (sphere c R) then
    fun z ↦ if z ∈ closedBall c R then (exists_harmonic_extension h.1 h.2).choose z else f z
  else f

section PoissonExtensionAPI

variable {c : ℂ} {R : ℝ} {f : ℂ → ℝ}

/-- On the closed disk, `poissonExtension` agrees with the chosen Dirichlet
solution from `exists_harmonic_extension`. -/
private theorem poissonExtension_eq_choose (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    EqOn (poissonExtension f c R) (exists_harmonic_extension hR hf).choose (closedBall c R) := by
  intro z hz
  have hcond : 0 < R ∧ ContinuousOn f (sphere c R) := ⟨hR, hf⟩
  simp only [poissonExtension, dite_eq_left hcond, ite_eq_left hz]

theorem poissonExtension_continuousOn (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    ContinuousOn (poissonExtension f c R) (closedBall c R) :=
  ((exists_harmonic_extension hR hf).choose_spec.1).congr (poissonExtension_eq_choose hR hf)

theorem poissonExtension_harmonicOnNhd (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    HarmonicOnNhd (poissonExtension f c R) (ball c R) := by
  intro x hx
  have hev : poissonExtension f c R =ᶠ[𝓝 x] (exists_harmonic_extension hR hf).choose := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact poissonExtension_eq_choose hR hf (ball_subset_closedBall hy)
  exact (harmonicAt_congr_nhds hev).2 ((exists_harmonic_extension hR hf).choose_spec.2.1 x hx)

theorem poissonExtension_eqOn_sphere (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    EqOn (poissonExtension f c R) f (sphere c R) := by
  intro z hz
  rw [poissonExtension_eq_choose hR hf (sphere_subset_closedBall hz)]
  exact (exists_harmonic_extension hR hf).choose_spec.2.2 hz

theorem poissonExtension_eqOn_compl (hR : 0 < R) (hf : ContinuousOn f (sphere c R)) :
    EqOn (poissonExtension f c R) f (closedBall c R)ᶜ := by
  intro z hz
  have hz' : z ∉ closedBall c R := hz
  have hcond : 0 < R ∧ ContinuousOn f (sphere c R) := ⟨hR, hf⟩
  simp only [poissonExtension, dite_eq_left hcond, ite_eq_right hz']

/-- Harmonic functions satisfy the mean-value property (helper; the openness
hypothesis of `HarmonicOnNhd.meanEqOn` below is not needed). -/
private theorem meanEqOn_of_harmonicOnNhd {u : ℂ → ℝ} {s : Set ℂ}
    (hu : HarmonicOnNhd u s) : MeanEqOn u s := by
  refine ⟨hu.continuousOn, fun a r hr hsub ↦ ?_⟩
  have h : HarmonicOnNhd u (closedBall a |r|) := by
    rw [abs_of_pos hr]
    exact hu.mono hsub
  exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq h

/-- `MeanEqOn` is antitone in the set. -/
private theorem meanEqOn_mono {h : ℂ → ℝ} {s t : Set ℂ} (hh : MeanEqOn h s) (hts : t ⊆ s) :
    MeanEqOn h t :=
  ⟨hh.continuousOn.mono hts, fun a r hr hsub ↦ hh.mean_eq a r hr (hsub.trans hts)⟩

/-- The Poisson extension takes values in any closed interval containing the
boundary data (maximum principle packaging). -/
theorem poissonExtension_mem_Icc (hR : 0 < R) (hf : ContinuousOn f (sphere c R))
    {m M : ℝ} (hfm : ∀ z ∈ sphere c R, f z ∈ Icc m M) :
    ∀ z ∈ closedBall c R, poissonExtension f c R z ∈ Icc m M := by
  have hPc : ContinuousOn (poissonExtension f c R) (closure (ball c R)) := by
    rw [closure_ball c hR.ne']
    exact poissonExtension_continuousOn hR hf
  have hPm : MeanEqOn (poissonExtension f c R) (ball c R) :=
    meanEqOn_of_harmonicOnNhd (poissonExtension_harmonicOnNhd hR hf)
  intro z hz
  have hz' : z ∈ closure (ball c R) := by
    rw [closure_ball c hR.ne']
    exact hz
  rw [mem_Icc]
  constructor
  · -- lower bound via the comparison principle applied to `-poissonExtension`
    have hb : ∀ x ∈ frontier (ball c R), (-poissonExtension f c R) x ≤ -m := by
      intro x hx
      rw [frontier_ball c hR.ne'] at hx
      simp only [Pi.neg_apply]
      rw [poissonExtension_eqOn_sphere hR hf hx]
      have := (mem_Icc.1 (hfm x hx)).1
      linarith
    have h := SubMeanOn.le_of_frontier_le isOpen_ball isBounded_ball
      hPm.neg.subMeanOn hPc.neg hb z hz'
    simp only [Pi.neg_apply] at h
    linarith
  · -- upper bound via the comparison principle
    have hb : ∀ x ∈ frontier (ball c R), poissonExtension f c R x ≤ M := by
      intro x hx
      rw [frontier_ball c hR.ne'] at hx
      rw [poissonExtension_eqOn_sphere hR hf hx]
      exact (mem_Icc.1 (hfm x hx)).2
    exact SubMeanOn.le_of_frontier_le isOpen_ball isBounded_ball
      hPm.subMeanOn hPc hb z hz'

end PoissonExtensionAPI

/-- Harmonic functions satisfy the mean-value property on open sets. -/
theorem HarmonicOnNhd.meanEqOn {u : ℂ → ℝ} {s : Set ℂ}
    (hu : HarmonicOnNhd u s) : MeanEqOn u s :=
  meanEqOn_of_harmonicOnNhd hu

/-- Continuous functions with the mean-value property on an open set are
harmonic (Dirichlet uniqueness). -/
theorem MeanEqOn.harmonicOnNhd {u : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hu : MeanEqOn u s) : HarmonicOnNhd u s := by
  intro x hx
  obtain ⟨r, hr, hcb⟩ := nhds_basis_closedBall.mem_iff.1 (hs.mem_nhds hx)
  have hus : ContinuousOn u (sphere x r) :=
    hu.continuousOn.mono (sphere_subset_closedBall.trans hcb)
  have hPc : ContinuousOn (poissonExtension u x r) (closedBall x r) :=
    poissonExtension_continuousOn hr hus
  have hPh : HarmonicOnNhd (poissonExtension u x r) (ball x r) :=
    poissonExtension_harmonicOnNhd hr hus
  have hPm : MeanEqOn (poissonExtension u x r) (ball x r) := meanEqOn_of_harmonicOnNhd hPh
  have hum : MeanEqOn u (ball x r) := meanEqOn_mono hu (ball_subset_closedBall.trans hcb)
  have hcl : closure (ball x r) = closedBall x r := closure_ball x hr.ne'
  have heq : EqOn u (poissonExtension u x r) (closure (ball x r)) := by
    refine MeanEqOn.eqOn_closure_of_frontier isOpen_ball isBounded_ball hum hPm ?_ ?_ ?_
    · rw [hcl]
      exact hu.continuousOn.mono hcb
    · rw [hcl]
      exact hPc
    · rw [frontier_ball x hr.ne']
      exact fun z hz ↦ (poissonExtension_eqOn_sphere hr hus hz).symm
  have hev : u =ᶠ[𝓝 x] poissonExtension u x r := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    exact heq (subset_closure hy)
  exact (harmonicAt_congr_nhds hev).2 (hPh x (mem_ball_self hr))

/-- Harmonicity is preserved by holomorphic precomposition. -/
theorem HarmonicOnNhd.comp_analytic {u : ℂ → ℝ} {t : Set ℂ} (hu : HarmonicOnNhd u t)
    (ht : IsOpen t) {φ : ℂ → ℂ} {s : Set ℂ} (hφ : AnalyticOnNhd ℂ φ s)
    (hmaps : MapsTo φ s t) : HarmonicOnNhd (u ∘ φ) s := by
  intro x hx
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 ht (φ x) (hmaps hx)
  obtain ⟨H, hH, hHre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (hu.mono hball)
  have hHφ : AnalyticAt ℂ (H ∘ φ) x := (hH (φ x) (mem_ball_self hρ)).comp (hφ x hx)
  have hev : u ∘ φ =ᶠ[𝓝 x] fun z ↦ ((H ∘ φ) z).re := by
    have hcont : ContinuousAt φ x := (hφ x hx).continuousAt
    filter_upwards [hcont.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ))] with y hy
    exact (hHre hy).symm
  exact (harmonicAt_congr_nhds hev).2 hHφ.harmonicAt_re

/-- Comparison characterization of subharmonicity (Anghel–Stan Prop. 3,
D1 ⇒ D3): a sub-mean-value function is dominated on every closed disk by the
Poisson extension of its own boundary values. -/
theorem SubMeanOn.le_poissonExtension_on {g : ℂ → ℝ} {s : Set ℂ}
    (hg : SubMeanOn g s) {c : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ s) :
    ∀ x ∈ closedBall c R, g x ≤ poissonExtension g c R x := by
  have hgs : ContinuousOn g (sphere c R) :=
    hg.continuousOn.mono (sphere_subset_closedBall.trans hsub)
  have hPc : ContinuousOn (poissonExtension g c R) (closedBall c R) :=
    poissonExtension_continuousOn hR hgs
  have hPm : MeanEqOn (poissonExtension g c R) (ball c R) :=
    meanEqOn_of_harmonicOnNhd (poissonExtension_harmonicOnNhd hR hgs)
  have hsm : SubMeanOn (g + -poissonExtension g c R) (ball c R) :=
    (hg.mono (ball_subset_closedBall.trans hsub)).add_meanEq hPm.neg
  have hcl : closure (ball c R) = closedBall c R := closure_ball c hR.ne'
  have hgc : ContinuousOn (g + -poissonExtension g c R) (closure (ball c R)) := by
    rw [hcl]
    exact (hg.continuousOn.mono hsub).add hPc.neg
  have hb : ∀ x ∈ frontier (ball c R), (g + -poissonExtension g c R) x ≤ 0 := by
    intro x hx
    rw [frontier_ball c hR.ne'] at hx
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [poissonExtension_eqOn_sphere hR hgs hx]
    simp
  have h := hsm.le_of_frontier_le isOpen_ball isBounded_ball hgc hb
  intro x hx
  have h' := h x (by rw [hcl]; exact hx)
  simp only [Pi.add_apply, Pi.neg_apply] at h'
  linarith

end Rado
