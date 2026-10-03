/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.LinearWindowBounds
public import Mathlib.Analysis.ODE.Gronwall

/-! A local quadratic remainder estimate for a flow and its variational
equation. All bounds are confined to one compact forward time window and one
bounded state tube. -/

@[expose] public section

open Set
open scoped NNReal Topology

namespace AVenhance.Infra.Flow

noncomputable section

theorem VariationalRemainderOnWindow.gronwallBound_zero_scale (K c a d : ℝ) :
    gronwallBound 0 K (c * a) d = c * gronwallBound 0 K a d := by
  by_cases hK : K = 0
  · simp [gronwallBound, hK]
    ring
  · simp [gronwallBound, hK]
    ring

/-- A quadratic Taylor error in the vector field produces a quadratic error
between a nonlinear trajectory and its variational approximation. The
trajectory, derivative, Taylor, and Lipschitz hypotheses are only required on
the indicated compact window and bounded state tube. -/
theorem flowOn_variational_quadratic_remainder_on_window
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E → E) {Y : ℝ → E → ℝ → E}
    (hY : IsFlowOn F Y) (x : E) {V : ℝ → E → ℝ → E}
    (A : ℝ → E →L[ℝ] E)
    (hV : IsFlowOn (fun r v => A r v) V)
    {s t M T L C₀ R : ℝ} (hst : s ≤ t)
    (hM₀ : 0 ≤ M) (hT₀ : 0 ≤ T) (hL₀ : 0 ≤ L)
    (hA : ∀ r, r ∈ Icc s t → ‖A r‖ ≤ M)
    (hAeq : ∀ r, A r = fderiv ℝ (F r) (Y r x s))
    (htraj : ∀ r, r ∈ Icc s t → ∀ w, ‖w - x‖ ≤ 1 →
      ‖Y r w s‖ ≤ C₀)
    (hTube : C₀ + Real.exp (M * (t - s)) ≤ R)
    (hLip : ∀ r, r ∈ Ico s t →
      LipschitzOnWith ⟨L, hL₀⟩ (F r) (Metric.closedBall (0 : E) R))
    (hTaylor : ∀ r, r ∈ Ico s t → ∀ v : E,
      ‖Y r x s‖ ≤ R → ‖v‖ ≤ R →
      ‖F r v - F r (Y r x s) - A r (v - Y r x s)‖ ≤
        T * ‖v - Y r x s‖ * ‖v - Y r x s‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : E, ‖h‖ ≤ 1 →
      ‖Y t (x + h) s - Y t x s - V t h s‖ ≤ C * ‖h‖ * ‖h‖ := by
  let Eexp : ℝ := Real.exp (M * (t - s))
  let B : ℝ := T * Eexp * Eexp
  let Q : ℝ := gronwallBound 0 L 1 (t - s)
  let K : ℝ≥0 := ⟨L, hL₀⟩
  have hEexp : 0 ≤ Eexp := (Real.exp_pos _).le
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hT₀ hEexp) hEexp
  have hQ : 0 ≤ Q := by
    have hmono := gronwallBound_mono (show 0 ≤ (0 : ℝ) by norm_num)
      (show 0 ≤ (1 : ℝ) by norm_num) hL₀
    have hq := hmono (show 0 ≤ t - s by linarith [hst])
    simpa [Q, gronwallBound_x0] using hq
  refine ⟨Q * B, mul_nonneg hQ hB, ?_⟩
  intro h hh
  let f : ℝ → E := fun r => Y r (x + h) s
  let g : ℝ → E := fun r => Y r x s + V r h s
  let ε : ℝ := B * ‖h‖ * ‖h‖
  have hVbound (r : ℝ) (hr : r ∈ Ico s t) :
      ‖V r h s‖ ≤ Eexp * ‖h‖ := by
    have hboundLinear := linearFlow_norm_bound_on_window hV
      (show s ∈ Icc s t from ⟨le_rfl, hst⟩)
      (fun q hq => hA q hq) h r ⟨hr.1, hr.2.le⟩
    have hexp : Real.exp (M * |r - s|) ≤ Eexp := by
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
      exact mul_le_mul_of_nonneg_left (by linarith [hr.2]) hM₀
    calc
      ‖V r h s‖ ≤ Real.exp (M * |r - s|) * ‖h‖ := hboundLinear
      _ ≤ Eexp * ‖h‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg h)
  have hfderiv (r : ℝ) : HasDerivAt f (F r (f r)) r := by
    simpa [f] using hY.2 (x + h) s r
  have hgderiv (r : ℝ) : HasDerivAt g
      (F r (Y r x s) + A r (V r h s)) r := by
    have hsum := (hY.2 x s r).add (hV.2 h s r)
    convert hsum using 1
  have hfcont : ContinuousOn f (Icc s t) :=
    HasDerivAt.continuousOn (fun r _ => hfderiv r)
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun r _ => hgderiv r)
  have hfwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt f (F r (f r)) (Ici r) r :=
    fun r _ => (hfderiv r).hasDerivWithinAt
  have hgwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt g (F r (Y r x s) + A r (V r h s)) (Ici r) r :=
    fun r _ => (hgderiv r).hasDerivWithinAt
  have hfmem : ∀ r ∈ Ico s t, f r ∈ Metric.closedBall (0 : E) R := by
    intro r hr
    rw [Metric.mem_closedBall, dist_zero_right]
    have hbound := htraj r ⟨hr.1, hr.2.le⟩ (x + h) (by
      rw [add_sub_cancel_left]
      exact hh)
    exact hbound.trans (by linarith [hEexp, hTube])
  have hgmem : ∀ r ∈ Ico s t, g r ∈ Metric.closedBall (0 : E) R := by
    intro r hr
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu := htraj r ⟨hr.1, hr.2.le⟩ x (by simp)
    have htime := hVbound r hr
    calc
      ‖g r‖ ≤ ‖Y r x s‖ + ‖V r h s‖ := norm_add_le _ _
      _ ≤ C₀ + Eexp * ‖h‖ := add_le_add hu htime
      _ ≤ C₀ + Eexp := by
        have hmul : Eexp * ‖h‖ ≤ Eexp := by
          calc
            Eexp * ‖h‖ ≤ Eexp * 1 := mul_le_mul_of_nonneg_left hh hEexp
            _ = Eexp := by ring
        simpa [add_comm] using add_le_add_left hmul C₀
      _ ≤ R := hTube
  have hfapprox : ∀ r ∈ Ico s t,
      dist (F r (f r)) (F r (f r)) ≤ (0 : ℝ) := by
    intro r hr
    simp
  have hgapprox : ∀ r ∈ Ico s t,
      dist (F r (Y r x s) + A r (V r h s)) (F r (g r)) ≤ ε := by
    intro r hr
    have huR : ‖Y r x s‖ ≤ R := by
      have hu := htraj r ⟨hr.1, hr.2.le⟩ x (by simp)
      exact hu.trans (by linarith [hEexp, hTube])
    have hvR : ‖g r‖ ≤ R := by
      have hv := hgmem r hr
      simpa [Metric.mem_closedBall, dist_zero_right] using hv
    have hTaylor' := hTaylor r hr (g r) huR hvR
    have hAvar : A r (V r h s) =
        fderiv ℝ (F r) (Y r x s) (V r h s) := by
      rw [hAeq r]
    have hrem :
        dist (F r (Y r x s) + A r (V r h s)) (F r (g r)) =
          ‖F r (g r) - F r (Y r x s) -
            A r (g r - Y r x s)‖ := by
      rw [dist_eq_norm]
      rw [show g r - Y r x s = V r h s by simp [g]]
      rw [hAvar]
      have hneg : F r (Y r x s) +
          fderiv ℝ (F r) (Y r x s) (V r h s) - F r (g r) =
          -(F r (g r) - F r (Y r x s) -
            fderiv ℝ (F r) (Y r x s) (V r h s)) := by abel
      rw [hneg, norm_neg]
    rw [hrem]
    have hdisp : ‖g r - Y r x s‖ ≤ Eexp * ‖h‖ := by
      rw [show g r - Y r x s = V r h s by simp [g]]
      exact hVbound r hr
    have hdisp0 : 0 ≤ Eexp * ‖h‖ := mul_nonneg hEexp (norm_nonneg h)
    calc
      _ ≤ T * ‖g r - Y r x s‖ * ‖g r - Y r x s‖ := hTaylor'
      _ ≤ T * (Eexp * ‖h‖) * ‖g r - Y r x s‖ := by gcongr
      _ ≤ T * (Eexp * ‖h‖) * (Eexp * ‖h‖) := by gcongr
      _ = ε := by
        simp [ε, B, Eexp]
        ring
  have hstart : dist (f s) (g s) ≤ 0 := by
    simp [f, g, hY.1, hV.1]
  have hcomp := dist_le_of_approx_trajectories_ODE_of_mem
    (a := s) (b := t) (K := K) (v := F)
    (s := fun _ => Metric.closedBall (0 : E) R)
    hLip hfcont hfwithin hfapprox hfmem hgcont hgwithin hgapprox hgmem hstart
  have hdist := hcomp t ⟨hst, le_rfl⟩
  rw [dist_eq_norm] at hdist
  have hK : (K : ℝ) = L := rfl
  rw [hK, zero_add] at hdist
  have hfg : f t - g t = Y t (x + h) s - Y t x s - V t h s := by
    dsimp [f, g]
    abel
  rw [hfg] at hdist
  have hscale := VariationalRemainderOnWindow.gronwallBound_zero_scale L ε 1 (t - s)
  calc
    ‖Y t (x + h) s - Y t x s - V t h s‖ ≤ gronwallBound 0 L ε (t - s) := hdist
    _ = ε * Q := by simpa [Q] using hscale
    _ = (Q * B) * ‖h‖ * ‖h‖ := by
      simp [ε, B]
      ring

end

end AVenhance.Infra.Flow
