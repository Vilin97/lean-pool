/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.AnalyticLogOnBall
public import LeanPool.Odlyzko.ExplicitFormula.BorelCaratheodoryDerivative

/-!
# Zero Free Log Derivative Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace NumberField.Odlyzko

theorem norm_logDeriv_le_of_zeroFree_on_ball
    {g : ℂ → ℂ} {c z : ℂ} {R r M A : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hM : 0 < M) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R))
    (hgn : ∀ w ∈ Metric.ball c R, g w ≠ 0)
    (hbound : ∀ w ∈ Metric.ball c R, ‖g w‖ ≤ M)
    (hcenter : Real.log M - Real.log ‖g c‖ ≤ A)
    (hz : z ∈ Metric.closedBall c r) :
    ‖logDeriv g z‖ ≤ 4 * A * (R + r) / (R - r) ^ 2 := by
  obtain ⟨L, hLc, hLderiv, hLexp⟩ :=
    AnalyticOnNhd.exists_analyticLog_on_ball hR hg hgn
  let F : ℂ → ℂ := fun w ↦ L (c + w) - L c
  have hFdiff : DifferentiableOn ℂ F (Metric.ball 0 R) := by
    intro w hw
    have hcw : c + w ∈ Metric.ball c R := by simp_all
    exact ((hLderiv (c + w) hcw).comp w
      ((hasDerivAt_const w c).add (hasDerivAt_id w))).sub_const _
      |>.differentiableAt.differentiableWithinAt
  have hreal (w : ℂ) (hw : w ∈ Metric.ball c R) :
      (L w).re = Real.log ‖g w‖ := by
    rw [← hLexp w hw, Complex.norm_exp, Real.log_exp]
  have hFre : ∀ w ∈ Metric.ball 0 R, (F w).re ≤ A := by
    intro w hw
    have hcw : c + w ∈ Metric.ball c R := by simp_all
    have hcball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
    have hgwpos : 0 < ‖g (c + w)‖ := norm_pos_iff.mpr (hgn (c + w) hcw)
    have hlog :
        Real.log ‖g (c + w)‖ ≤ Real.log M :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hgwpos) (Set.mem_Ioi.mpr hM) (hbound (c + w) hcw)
    dsimp [F]
    grind
  have hF0 : F 0 = 0 := by simp [F]
  let w := z - c
  have hw : w ∈ Metric.closedBall 0 r := by
    simpa [w, Metric.mem_closedBall, dist_eq, norm_sub_rev] using hz
  have hmain :=
    norm_deriv_le_of_re_le_on_ball hR hr hrR hA hFdiff hFre hF0 hw
  have hzball : z ∈ Metric.ball c R :=
    Metric.closedBall_subset_ball hrR hz
  have hFderiv :
      deriv F w = logDeriv g z := by
    have hcz : c + w = z := by grind
    have hLz := hLderiv z hzball
    rw [← hcz] at hLz
    have h :=
      (hLz.comp w
        ((hasDerivAt_const w c).add (hasDerivAt_id w))).sub_const (L c)
    have h' : deriv F w = logDeriv g (c + w) := by
      simpa [F] using h.deriv
    simp_all
  simp_all

end NumberField.Odlyzko
