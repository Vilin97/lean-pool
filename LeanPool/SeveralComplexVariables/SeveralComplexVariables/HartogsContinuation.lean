/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Cauchy

/-!
# Hartogs continuation over an arbitrary connected base

An analytic function on an annular cylinder together with full disc fibers over a nonempty open
part of the base extends to the full cylinder. No local boundedness near the missing part is
assumed. The proof uses a fixed circle integral and the identity principle in the base.
Reference: [Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Theorem 2.6.1.

## Main results

`hartogsCylinder` is an annular cylinder together with full disc fibers over part of the base.
`exists_extension_hartogsCylinder` is Hartogs continuation across that figure, without a local
boundedness hypothesis on the missing part.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- An annular cylinder supplemented by full disc fibers over part of the base. -/
@[expose] def hartogsCylinder (D D₀ : Set E) (ρ R : ℝ) : Set (E × ℂ) :=
  (D ×ˢ (ball 0 R \ closedBall 0 ρ)) ∪ (D₀ ×ˢ ball 0 R)

/-- **Hartogs' continuity theorem.** The smaller base need not be connected. Finite positive
outer radius is used; no positive-dimensional base assumption is required. -/
theorem exists_extension_hartogsCylinder {D D₀ : Set E}
    (hD : IsOpen D) (hc : IsPreconnected D) (hD₀ : IsOpen D₀) (hne : D₀.Nonempty)
    (hsub : D₀ ⊆ D) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {f : E × ℂ → F} (hf : AnalyticOnNhd ℂ f (hartogsCylinder D D₀ ρ R)) :
    ∃ g, AnalyticOnNhd ℂ g (D ×ˢ ball 0 R) ∧ EqOn g f (hartogsCylinder D D₀ ρ R) := by
  classical
  obtain ⟨r, hρr, hrR⟩ := exists_between hρR
  have hr : 0 < r := hρ.trans_lt hρr
  let W : Set ((E × ℂ) × ℂ) := {q | (q.1.1, q.2) ∈ hartogsCylinder D D₀ ρ R ∧ q.2 ≠ q.1.2}
  let H : (E × ℂ) × ℂ → F := fun q => (q.2 - q.1.2)⁻¹ • f (q.1.1, q.2)
  have hH : AnalyticOnNhd ℂ H W := by
    intro q hq
    have hmap : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => (q.1.1, q.2)) q :=
      (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
    exact ((analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)).inv
      (sub_ne_zero.mpr hq.2)).smul
      ((hf _ hq.1).comp_of_eq hmap rfl)
  let J : E × ℂ → F := fun p => (2 * Real.pi * I : ℂ)⁻¹ • ∮ t in C(0, r), H (p, t)
  have hJ : AnalyticOnNhd ℂ J (D ×ˢ ball 0 r) := by
    apply (analyticOnNhd_circleIntegral_kernel (hD.prod isOpen_ball) hH hr.le ?_).const_smul
    intro p hp t ht
    have htn : ‖t‖ = r := by simpa [mem_sphere, dist_zero_right] using ht
    refine ⟨Or.inl ⟨hp.1, ?_, ?_⟩, ?_⟩
    · simpa [mem_ball, dist_zero_right, htn] using hrR
    · simpa [mem_closedBall, dist_zero_right, htn] using not_le.mpr hρr
    · change t ≠ p.2
      intro he
      have hpw : ‖p.2‖ < r := by simpa [mem_ball, dist_zero_right] using hp.2
      rw [he] at htn
      linarith
  have hJ₀ : ∀ z ∈ D₀, ∀ w ∈ ball (0 : ℂ) r, J (z, w) = f (z, w) := by
    intro z hz w hw
    have hs : AnalyticOnNhd ℂ (fun t => f (z, t)) (ball 0 R) := by
      intro t ht
      exact (hf _ (Or.inr ⟨hz, ht⟩)).comp (analyticAt_const.prod analyticAt_id)
    exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (f := fun t => f (z, t)) countable_empty hw
      (hs.continuousOn.mono (closedBall_subset_ball hrR))
      (fun t ht => (hs t (ball_subset_ball hrR.le ht.1)).differentiableAt)
  have hJa : ∀ z ∈ D, ∀ w ∈ ball (0 : ℂ) r \ closedBall 0 ρ, J (z, w) = f (z, w) := by
    intro z hz w hw
    have hj : AnalyticOnNhd ℂ (fun z => J (z, w)) D :=
      fun z hz => (hJ _ ⟨hz, hw.1⟩).comp (analyticAt_id.prod analyticAt_const)
    have hh : AnalyticOnNhd ℂ (fun z => f (z, w)) D :=
      fun z hz => (hf _ (Or.inl ⟨hz, ball_subset_ball hrR.le hw.1, hw.2⟩)).comp
        (analyticAt_id.prod analyticAt_const)
    obtain ⟨a, ha⟩ := hne
    exact hj.eqOn_of_preconnected_of_eventuallyEq hh hc (hsub ha)
      (Filter.mem_of_superset (hD₀.mem_nhds ha) (fun y hy => hJ₀ y hy w hw.1)) hz
  let g : E × ℂ → F := fun p => if ‖p.2‖ < r then J p else f p
  have hgf : EqOn g f (D ×ˢ (ball 0 R \ closedBall 0 ρ)) := by
    intro p hp
    dsimp [g]
    split_ifs with hw
    · exact hJa p.1 hp.1 p.2 ⟨by simpa [mem_ball, dist_zero_right] using hw, hp.2.2⟩
    · rfl
  refine ⟨g, ?_, ?_⟩
  · intro p hp
    by_cases hw : ‖p.2‖ < r
    · have he : g =ᶠ[𝓝 p] J := by
        filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hw] with q hq
        simp [g, hq]
      exact (analyticAt_congr he).mpr (hJ p ⟨hp.1, by simpa [mem_ball, dist_zero_right] using hw⟩)
    · have hp' : p ∈ D ×ˢ (ball 0 R \ closedBall 0 ρ) :=
        ⟨hp.1, hp.2, by simpa [mem_closedBall, dist_zero_right] using (not_le.mpr
          (hρr.trans_le (not_lt.mp hw)))⟩
      have he : g =ᶠ[𝓝 p] f := Filter.mem_of_superset
        ((hD.prod (isOpen_ball.sdiff isClosed_closedBall)).mem_nhds hp') hgf
      exact (analyticAt_congr he).mpr (hf p (Or.inl hp'))
  · intro p hp
    rcases hp with hp | hp
    · exact hgf hp
    · dsimp [g]
      split_ifs with hw
      · exact hJ₀ p.1 hp.1 p.2 (by simpa [mem_ball, dist_zero_right] using hw)
      · rfl

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
