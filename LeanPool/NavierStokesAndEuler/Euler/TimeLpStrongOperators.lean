/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L2Space

/-! Genuine strong operator approximation on Bochner L² time spaces. -/

@[expose] public section


noncomputable section

namespace EulerTimeLp

open MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniformly bounded strong operator approximation converges on every actual Bochner L² time field.
-/
theorem strong_operator_timeLp_tendsto (T : ℝ) (A : ℕ → E →L[ℝ] E) (M : ℝ)
    (hA : ∀ n x, ‖A n x‖ ≤ M * ‖x‖)
    (hlim : ∀ x, Filter.Tendsto (fun n => A n x) Filter.atTop (𝓝 x))
    (u : TimeLp T E) :
    Filter.Tendsto (fun n => (A n).compLpL 2 (timeMeasure T) u) Filter.atTop (𝓝 u) := by
  let F := fun n t => ‖A n (u t)-u t‖^2
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (timeMeasure T) := by
    intro n
    exact (((A n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).sub
      (Lp.aestronglyMeasurable u)).norm.pow 2
  have hi : Integrable (fun t => ‖u t‖^2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hb : ∀ n t, ‖F n t‖ ≤ (M+1)^2*‖u t‖^2 := by
    intro n t
    have hn := (norm_sub_le (A n (u t)) (u t)).trans (add_le_add (hA n (u t)) le_rfl)
    change ‖‖A n (u t)-u t‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (A n (u t)-u t), norm_nonneg (u t)]
  have hl : ∀ t, Filter.Tendsto (fun n => F n t) Filter.atTop (𝓝 (0 : ℝ)) := by
    intro t
    have h := ((hlim (u t)).sub_const (u t)).norm.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hint := tendsto_integral_of_dominated_convergence (fun t => (M+1)^2*‖u t‖^2)
    hmeas (hi.const_mul ((M+1)^2)) (fun n => Filter.Eventually.of_forall (hb n))
    (Filter.Eventually.of_forall hl)
  have he (n : ℕ) : ‖(A n).compLpL 2 (timeMeasure T) u-u‖^2 = ∫ t, F n t ∂timeMeasure T := by
    rw [norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((A n).compLpL 2 (timeMeasure T) u) u,
      (A n).coeFn_compLpL u] with t hs ha
    rw [hs, Pi.sub_apply, ha]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh : Filter.Tendsto (fun n => ‖(A n).compLpL 2 (timeMeasure T) u-u‖^2) Filter.atTop (𝓝 (0 :
      ℝ)) := by
    simpa only [he, integral_zero] using hint
  have h := hh.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h

end EulerTimeLp
