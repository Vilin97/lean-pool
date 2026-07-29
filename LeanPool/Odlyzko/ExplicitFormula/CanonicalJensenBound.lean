/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CanonicalAnalyticFactorization

/-!
# Canonical Jensen Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Metric Set

namespace NumberField.Odlyzko

open Classical in
theorem AnalyticOnNhd.eq_zero_of_mem_divisor_support
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hz : z ∈ (MeromorphicOn.divisor f U).support) :
    f z = 0 := by
  have hzU : z ∈ U := by
    by_contra hzU
    simp_all
  by_contra hfz
  apply Function.mem_support.mp hz
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzU,
    (hf z hzU).meromorphicOrderAt_eq,
    (hf z hzU).analyticOrderAt_eq_zero.mpr hfz]
  simp

open Classical in
theorem AnalyticOnNhd.sum_divisor_ball_le
    {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0)
    (hboundary : ∀ z ∈ sphere c r, f z ≠ 0)
    (f_bound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ((∑ᶠ z, MeromorphicOn.divisor f (ball c r) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / Real.log (R / r) := by
  have heq :=
    divisor_ball_eq_divisor_closedBall_of_boundary_ne
      (hf.mono (closedBall_subset_closedBall hrR.le)) hboundary
  have hfinsum :
      (∑ᶠ z, MeromorphicOn.divisor f (ball c r) z : ℤ) =
        ∑ᶠ z, MeromorphicOn.divisor f (closedBall c r) z := by simp_all
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by grind
  have f_bound' : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by grind
  rw [hfinsum]
  have hJ :=
    hf'.sum_divisor_le
      (show 0 < |r| by grind)
      (show |r| < |R| by
        grind)
      hM hc f_bound'
  grind

end NumberField.Odlyzko
