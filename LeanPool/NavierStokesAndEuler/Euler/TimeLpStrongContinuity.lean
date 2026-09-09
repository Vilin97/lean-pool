/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Strong continuity of isometric spatial actions on time L²

This uses dominated convergence with the actual square-integrable time field.
It does not assume operator-norm continuity of spatial translations.
-/

noncomputable section

namespace EulerTimeLpBoundedMap

open MeasureTheory Set Filter EulerTimeLp
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A pointwise formula for the square distance between two genuine lifted fields. -/
theorem timeLift_norm_sub_sq (T : ℝ) (A B : E →L[ℝ] E) (u : TimeLp T E) :
    ‖timeLift T A u-timeLift T B u‖^2 =
      ∫ t, ‖A (u t)-B (u t)‖^2 ∂timeMeasure T := by
  refine (norm_sq_eq_integral T (timeLift T A u-timeLift T B u)).trans ?_
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (timeLift T A u) (timeLift T B u),
    timeLift_ae T A u, timeLift_ae T B u] with t hs ha hb
  simp only [Pi.sub_apply, ha, hb] at hs
  exact congrArg (fun v : E => ‖v‖^2) hs

/-- A strongly continuous family of spatial isometries remains strongly
continuous on the genuine Bochner time space. -/
theorem timeLift_strongly_continuous {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (T : ℝ) (A : X → E →L[ℝ] E)
    (hA : ∀ x v, ‖A x v‖ = ‖v‖)
    (hc : ∀ v, Continuous (fun x => A x v)) (u : TimeLp T E) :
    Continuous (fun x => timeLift T (A x) u) := by
  apply continuous_iff_continuousAt.2
  intro x₀
  let g : X → ℝ → ℝ := fun x t => ‖A x (u t)-A x₀ (u t)‖^2
  have hm (x : X) : AEStronglyMeasurable (g x) (timeMeasure T) := by
    exact (((A x).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).sub
      ((A x₀).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))).norm.pow 2
  have hb (x : X) (t : ℝ) : ‖g x t‖ ≤ 4*‖u t‖^2 := by
    have hn : ‖A x (u t)-A x₀ (u t)‖ ≤ 2*‖u t‖ := by
      calc
        _ ≤ ‖A x (u t)‖+‖A x₀ (u t)‖ := norm_sub_le _ _
        _ = 2*‖u t‖ := by rw [hA, hA]; ring
    calc
      ‖g x t‖ = ‖A x (u t)-A x₀ (u t)‖^2 := Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ (2*‖u t‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = 4*‖u t‖^2 := by ring
  have hi : Integrable (fun t => 4*‖u t‖^2) (timeMeasure T) :=
    ((Lp.memLp u).integrable_norm_pow (by norm_num)).const_mul 4
  have hl (t : ℝ) : Tendsto (fun x => g x t) (𝓝 x₀) (𝓝 (0 : ℝ)) := by
    have h := (((hc (u t)).tendsto x₀).sub_const (A x₀ (u t))).norm.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hint : Tendsto (fun x => ∫ t, g x t ∂timeMeasure T) (𝓝 x₀) (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (fun t => 4*‖u t‖^2)
        (Eventually.of_forall hm) (Eventually.of_forall (fun x => Eventually.of_forall (hb x))) hi
        (Eventually.of_forall hl))
  have hs : Tendsto (fun x => ‖timeLift T (A x) u-timeLift T (A x₀) u‖^2)
      (𝓝 x₀) (𝓝 (0 : ℝ)) := by
    exact hint.congr' (Eventually.of_forall (fun x => (timeLift_norm_sub_sq T (A x) (A x₀) u).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

end EulerTimeLpBoundedMap
