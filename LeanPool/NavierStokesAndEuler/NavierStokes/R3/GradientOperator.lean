/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup

@[expose] public section

/-!
# The differential operator norm and the coordinate gradient energy

The three coordinate derivatives control the operator norm of the full
derivative. These pointwise estimates do not require differentiability: Lean's
totalized `fderiv` is a continuous linear map for every function.
-/


noncomputable section

open scoped BigOperators ContDiff

namespace NavierStokesR3.GradientOperator

open ProblemStatement Comparison

theorem gradientSq_nonneg (w : Space → Space) (x : Space) :
    0 ≤ gradientSq w x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem partial_norm_le_sqrt_gradientSq (w : Space → Space) (x : Space)
    (i : Fin 3) :
    ‖partialD i w x‖ ≤ Real.sqrt (gradientSq w x) := by
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖partialD j w x‖)
    (Finset.mem_univ i)

/-- The derivative applied to a vector, expanded in the standard coordinate
basis. -/
theorem fderiv_apply_eq_sum (w : Space → Space) (x v : Space) :
    fderiv ℝ w x v = ∑ i : Fin 3, v i • partialD i w x := by
  conv_lhs => rw [← NavierStokes.PeriodicUniqueness.sum_coordinates v]
  simp only [map_sum, map_smul]
  rfl

theorem norm_fderiv_le_three_mul_sqrt_gradientSq (w : Space → Space) (x : Space) :
    ‖fderiv ℝ w x‖ ≤ 3 * Real.sqrt (gradientSq w x) := by
  apply (fderiv ℝ w x).opNorm_le_bound (by positivity)
  intro v
  rw [fderiv_apply_eq_sum]
  calc
    ‖∑ i : Fin 3, v i • partialD i w x‖
        ≤ ∑ i : Fin 3, ‖v i • partialD i w x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖v‖ * Real.sqrt (gradientSq w x) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v i)
        (partial_norm_le_sqrt_gradientSq w x i) (norm_nonneg _) (norm_nonneg _)
    _ = (3 * Real.sqrt (gradientSq w x)) * ‖v‖ := by
      simp
      ring

theorem continuous_gradientSq {w : Space → Space} (hw : ContDiff ℝ 1 w) :
    Continuous (gradientSq w) := by
  unfold gradientSq
  exact continuous_finsetSum _ fun i _ =>
    (NavierStokes.PeriodicIntegration.continuous_partial hw i).norm.pow 2

end NavierStokesR3.GradientOperator
