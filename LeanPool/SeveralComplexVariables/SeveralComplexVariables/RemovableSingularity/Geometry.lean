/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Topology.Compactness.Compact
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Basic

/-!
# Circles avoiding an analytic zero set

A nonzero analytic germ admits a complex line on which it is not identically zero. A small
circle on that line avoids its zeros. Compactness then gives a fixed circle that continues to
avoid the zeros under small translations of its centre. A slightly larger closed disc remains in
the original open domain. No preparation or division theorem is used.

## Main results

`exists_nonzero_line_of_analyticAt` produces a complex line on which a nonzero germ is not
identically zero. `exists_translated_circle_avoiding_zeroSet` produces a circle that continues
to avoid the zeros under small translations of its centre.
-/

public section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A nonzero analytic germ has a nonzero germ on some complex line through its centre. -/
theorem exists_nonzero_line_of_analyticAt {g : E → ℂ} {a : E}
    (hg : AnalyticAt ℂ g a) (hne : ¬ g =ᶠ[𝓝 a] 0) :
    ∃ v : E, ¬ (fun w : ℂ => g (a + w • v)) =ᶠ[𝓝 0] 0 := by
  by_cases hga : g a = 0
  · obtain ⟨r, hr, hgon⟩ := hg.exists_ball_analyticOnNhd
    obtain ⟨b, hb, hgb⟩ : ∃ b ∈ ball a r, g b ≠ 0 := by
      by_contra! h
      exact hne (Filter.mem_of_superset (ball_mem_nhds a hr) (fun z hz => h z hz))
    let v := b - a
    have hv : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hgb (h ▸ hga)))
    have hline : AnalyticOnNhd ℂ (fun w : ℂ => g (a + w • v)) (ball 0 (r / ‖v‖)) := by
      intro w hw
      have hm : a + w • v ∈ ball a r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
        exact (lt_div_iff₀ hv).mp (mem_ball_zero_iff.mp hw)
      exact (hgon _ hm).comp_of_eq (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) rfl
    refine ⟨v, fun h => ?_⟩
    have he := hline.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (r / ‖v‖)).isPreconnected (mem_ball_self (div_pos hr hv)) h
    have h1 : (1 : ℂ) ∈ ball 0 (r / ‖v‖) := by
      rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hv, one_mul]
      exact mem_ball_iff_norm.mp hb
    exact hgb (by simpa [v] using he h1)
  · exact ⟨0, fun h => hga (by simpa using h.self_of_nhds)⟩

/-- A fixed translated circle avoids the zero set for all nearby centres, while a larger closed disc
stays in the original domain. This also permits the zero direction when the defining function is
already nonzero at the centre. -/
theorem exists_translated_circle_avoiding_zeroSet {U : Set E} (hU : IsOpen U)
    {g : E → ℂ} (hg : AnalyticOnNhd ℂ g U) {a : E} (ha : a ∈ U)
    (hne : ¬ g =ᶠ[𝓝 a] 0) :
    ∃ (v : E) (r R : ℝ) (V : Set E), 0 < r ∧ r < R ∧ IsOpen V ∧ a ∈ V ∧
      (∀ z ∈ V, ∀ w ∈ closedBall (0 : ℂ) R, z + w • v ∈ U) ∧
      (∀ z ∈ V, ∀ w ∈ sphere (0 : ℂ) r, g (z + w • v) ≠ 0) := by
  obtain ⟨v, hv⟩ := exists_nonzero_line_of_analyticAt (hg a ha) hne
  have hal : AnalyticAt ℂ (fun w : ℂ => g (a + w • v)) 0 :=
    (hg a ha).comp_of_eq (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) (by simp)
  have he : ∀ᶠ w : ℂ in 𝓝 0, w ≠ 0 → g (a + w • v) ≠ 0 :=
    eventually_nhdsWithin_iff.mp (hal.eventually_eq_zero_or_eventually_ne_zero.resolve_left hv)
  have ht : Tendsto (fun w : ℂ => a + w • v) (𝓝 0) (𝓝 a) := by
    have hcont : Continuous (fun w : ℂ => a + w • v) := by fun_prop
    simpa using hcont.tendsto (0 : ℂ)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (inter_mem (ht (hU.mem_nhds ha)) he)
  let r := δ / 4
  let R := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r, R]; linarith
  have hRd : R < δ := by dsimp [R]; linarith
  let A : E × ℂ → E := fun p => p.1 + p.2 • v
  have hA : Continuous A := continuous_fst.add (continuous_snd.smul continuous_const)
  obtain ⟨V₁, W₁, hV₁, _, ha₁, hW₁, hsub₁⟩ := generalized_tube_lemma
    (isCompact_singleton (x := a)) (isCompact_closedBall (0 : ℂ) R)
    (hU.preimage hA) (by
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      rcases hz with rfl
      exact (hd (closedBall_subset_ball hRd hw)).1)
  have hgood : IsOpen {z ∈ U | g z ≠ 0} :=
    hg.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  obtain ⟨V₂, W₂, hV₂, _, ha₂, hW₂, hsub₂⟩ := generalized_tube_lemma
    (isCompact_singleton (x := a)) (isCompact_sphere (0 : ℂ) r)
    (hgood.preimage hA) (by
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      rcases hz with rfl
      have hwδ : w ∈ ball (0 : ℂ) δ :=
        mem_ball.mpr ((mem_sphere.mp hw).trans_lt (hrR.trans hRd))
      refine ⟨(hd hwδ).1, (hd hwδ).2 ?_⟩
      intro h
      have heq := mem_sphere.mp hw
      simp [h] at heq
      linarith)
  refine ⟨v, r, R, V₁ ∩ V₂, hr, hrR, hV₁.inter hV₂,
    ⟨ha₁ (mem_singleton a), ha₂ (mem_singleton a)⟩, ?_, ?_⟩
  · intro z hz w hw
    exact hsub₁ (a := (z, w)) ⟨hz.1, hW₁ hw⟩
  · intro z hz w hw
    exact (hsub₂ (a := (z, w)) ⟨hz.2, hW₂ hw⟩).2

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
