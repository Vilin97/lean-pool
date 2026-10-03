/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveOperators

/-! Differentiation of an actual field acting on continuous trajectories. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter Asymptotics
open scoped Topology
namespace AVenhance.Infra.Section4

/-- A uniform quadratic remainder gives the actual Frechet derivative.
This helper applies to the Banach space of continuous trajectories as well
as to the finite-dimensional source field. -/
theorem amnr_hasFDerivAt_of_quadratic_remainder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (L : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hrem : ∀ h, ‖f (x + h) - f x - L h‖ ≤ C * ‖h‖ * ‖h‖) :
    HasFDerivAt f L x := by
  have hlittle : (fun h : E => ‖f (x + h) - f x - L h‖) =o[𝓝 0] fun h => ‖h‖ := by
    rw [isLittleO_iff]
    intro c hc
    have hb : Metric.ball (0 : E) (c / (C + 1)) ∈ 𝓝 (0 : E) :=
      Metric.ball_mem_nhds _ (div_pos hc (by linarith))
    filter_upwards [hb] with h hh
    have hh' : ‖h‖ < c / (C + 1) := by simpa only [Metric.mem_ball, dist_zero_right] using hh
    have hscaled : (C + 1) * ‖h‖ ≤ c := by
      have := (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hh'
      simpa only [mul_comm] using this.le
    have hbound : ‖f (x + h) - f x - L h‖ ≤ c * ‖h‖ := by
      calc
        _ ≤ C * ‖h‖ * ‖h‖ := hrem h
        _ ≤ (C + 1) * ‖h‖ * ‖h‖ := by gcongr; linarith
        _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hscaled (norm_nonneg _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound
  exact (hasFDerivAt_iff_isLittleO_nhds_zero).mpr (isLittleO_norm_norm.mp hlittle)

/-- Applying the primitive field derivative along a continuous curve gives
an actual continuous operator curve. -/
def amnrCurveDerivative {K E F : Type*} [TopologicalSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : K → E → E →L[ℝ] F) (hD : Continuous (fun z : K × E => D z.1 z.2))
    (u : C(K, E)) : C(K, E →L[ℝ] F) :=
  ⟨fun t => D t (u t), hD.comp (continuous_id.prodMk u.continuous)⟩

/-- A uniform primitive Taylor estimate differentiates the actual
composition operator on the whole continuous-trajectory space. -/
theorem amnrCurveCompose_hasFDerivAt {K E F : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : K → E → F) (hf : Continuous (fun z : K × E => f z.1 z.2))
    (D : K → E → E →L[ℝ] F) (hD : Continuous (fun z : K × E => D z.1 z.2))
    {C : ℝ} (hC : 0 ≤ C)
    (hTaylor : ∀ t x h, ‖f t (x + h) - f t x - D t x h‖ ≤ C * ‖h‖ * ‖h‖)
    (u : C(K, E)) :
    HasFDerivAt (amnrCurveCompose f hf) (amnrCurveOperator (amnrCurveDerivative D hD u)) u := by
  apply amnr_hasFDerivAt_of_quadratic_remainder _ hC
  intro h
  apply (ContinuousMap.norm_le _ (show 0 ≤ C * ‖h‖ * ‖h‖ by positivity)).mpr
  intro t
  change ‖f t (u t + h t) - f t (u t) - D t (u t) (h t)‖ ≤ _
  exact (hTaylor t (u t) (h t)).trans (by gcongr <;> exact h.norm_coe_le_norm t)

end AVenhance.Infra.Section4
