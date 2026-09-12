/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
import Mathlib.Algebra.Order.Ring.Star

/-!
# Breakdown Criterion
-/

@[expose] public section

noncomputable section

namespace EulerBreakdownCriterion

open Filter Set EulerSmoothLimit
open scoped Topology

theorem no_escape_near_compact_trajectory
    {E : Type*} [NormedAddCommGroup E]
    (reference : ℝ → E) (samples : ℕ → E) (times errors : ℕ → ℝ) (S : ℝ)
    (hc : ContinuousOn reference (Icc 0 S))
    (ht : ∀ n, times n ∈ Icc 0 S)
    (he : Tendsto errors atTop (nhds 0))
    (hd : ∀ᶠ n in atTop, ‖samples n - reference (times n)‖ ≤ errors n) :
    ¬ Tendsto (fun n => ‖samples n‖) atTop atTop := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  intro hg
  have hε : ∀ᶠ n in atTop, errors n < 1 := he.eventually (gt_mem_nhds (by norm_num))
  have hlarge : ∀ᶠ n in atTop, C + 2 ≤ ‖samples n‖ :=
    hg.eventually (eventually_ge_atTop (C + 2))
  obtain ⟨n, hnε, hnlarge, hnd⟩ := (hε.and (hlarge.and hd)).exists
  have hnorm : ‖samples n‖ ≤ ‖samples n - reference (times n)‖ + ‖reference (times n)‖ := by
    calc
      _ = ‖(samples n - reference (times n)) + reference (times n)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have href := hC (times n) (ht n)
  have herr := hnd
  linarith

/-- The final gradient contradiction, expressed with actual Fréchet derivatives at the origin. -/
theorem no_gradient_escape_under_C1_comparison
    (u : ℝ → Space → Space) (U : ℕ → ℝ → Space → Space)
    (times errors : ℕ → ℝ) (S : ℝ)
    (hc : ContinuousOn (fun t => fderiv ℝ (u t) 0) (Icc 0 S))
    (ht : ∀ n, times n ∈ Icc 0 S)
    (he : Tendsto errors atTop (nhds 0))
    (hd : ∀ n, ‖fderiv ℝ (U n (times n)) 0 - fderiv ℝ (u (times n)) 0‖ ≤ errors n) :
    ¬ Tendsto (fun n => ‖fderiv ℝ (U n (times n)) 0‖) atTop atTop :=
  no_escape_near_compact_trajectory (fun t => fderiv ℝ (u t) 0)
    (fun n => fderiv ℝ (U n (times n)) 0) times errors S hc ht he (Eventually.of_forall hd)

end EulerBreakdownCriterion
