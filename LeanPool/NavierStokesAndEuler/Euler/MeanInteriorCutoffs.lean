/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicCutoffEnergy

@[expose] public section

/-! Actual nested smooth cutoffs, with finite derivative bounds independent of the field. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus EulerMeanSolenoidal
open scoped ContDiff

private theorem derivative_bound_exists (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) : ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C :=
  (hc.iteratedFDeriv n).exists_bound_of_continuous (hs.continuous_iteratedFDeriv (by simp))

def derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) : ℝ :=
  max 1 (Classical.choose (derivative_bound_exists f hc hs n))

theorem one_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) : 1 ≤ derivativeBound f hc hs n := le_max_left _ _

theorem norm_iteratedFDeriv_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ derivativeBound f hc hs n :=
  (Classical.choose_spec (derivative_bound_exists f hc hs n) x).trans (le_max_right _ _)

theorem norm_gradient_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (x : Space) : ‖gradient f x‖ ≤ derivativeBound f hc hs 1 := by
  have hn : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := (toDual ℝ Space).symm.norm_map _
  rw [hn, ← norm_iteratedFDeriv_one]
  exact norm_iteratedFDeriv_le_derivativeBound f hc hs 1 x

theorem abs_secondPartial_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (i : Fin 3) (x : Space) :
    |partialDerivative (partialDerivative f i) i x| ≤ derivativeBound f hc hs 2 := by
  rw [partialDerivative_twice f hs i x, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ 2 f x).le_opNorm (fun _ : Fin 2 => EuclideanSpace.single i 1)
  have hb : ‖iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => EuclideanSpace.single i 1)‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
    simpa only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] using h
  exact hb.trans (norm_iteratedFDeriv_le_derivativeBound f hc hs 2 x)

def innerBump : ContDiffBump (0 : Space) := ⟨1/2, 5/8, by norm_num, by norm_num⟩
def middleBump : ContDiffBump (0 : Space) := ⟨3/4, 13/16, by norm_num, by norm_num⟩
def outerBump : ContDiffBump (0 : Space) := ⟨7/8, 15/16, by norm_num, by norm_num⟩

def innerCutoff : Space → ℝ := innerBump
def middleCutoff : Space → ℝ := middleBump
def outerCutoff : Space → ℝ := outerBump

theorem inner_smooth : ContDiff ℝ ∞ innerCutoff := innerBump.contDiff
theorem middle_smooth : ContDiff ℝ ∞ middleCutoff := middleBump.contDiff
theorem outer_smooth : ContDiff ℝ ∞ outerCutoff := outerBump.contDiff
theorem inner_compact : HasCompactSupport innerCutoff := innerBump.hasCompactSupport
theorem middle_compact : HasCompactSupport middleCutoff := middleBump.hasCompactSupport
theorem outer_compact : HasCompactSupport outerCutoff := outerBump.hasCompactSupport

theorem inner_support : tsupport innerCutoff = Metric.closedBall 0 (5/8 : ℝ) :=
  innerBump.tsupport_eq
theorem middle_support : tsupport middleCutoff = Metric.closedBall 0 (13/16 : ℝ) :=
  middleBump.tsupport_eq
theorem outer_support : tsupport outerCutoff = Metric.closedBall 0 (15/16 : ℝ) :=
  outerBump.tsupport_eq

theorem abs_inner_le_one (x : Space) : |innerCutoff x| ≤ 1 := by
  change |innerBump x| ≤ 1
  rw [abs_of_nonneg innerBump.nonneg]
  exact innerBump.le_one
theorem abs_middle_le_one (x : Space) : |middleCutoff x| ≤ 1 := by
  change |middleBump x| ≤ 1
  rw [abs_of_nonneg middleBump.nonneg]
  exact middleBump.le_one
theorem abs_outer_le_one (x : Space) : |outerCutoff x| ≤ 1 := by
  change |outerBump x| ≤ 1
  rw [abs_of_nonneg outerBump.nonneg]
  exact outerBump.le_one

theorem inner_one_on_halfBall {x : Space} (hx : x ∈ Metric.closedBall 0 (1/2 : ℝ)) :
    innerCutoff x = 1 := innerBump.one_of_mem_closedBall hx

theorem middle_one_on_inner_support {x : Space} (hx : x ∈ tsupport innerCutoff) :
    middleCutoff x = 1 := by
  rw [inner_support] at hx
  exact middleBump.one_of_mem_closedBall
    (Metric.closedBall_subset_closedBall (by norm_num [middleBump]) hx)

theorem outer_one_on_middle_support {x : Space} (hx : x ∈ tsupport middleCutoff) :
    outerCutoff x = 1 := by
  rw [middle_support] at hx
  exact outerBump.one_of_mem_closedBall
    (Metric.closedBall_subset_closedBall (by norm_num [outerBump]) hx)

theorem outer_one_on_inner_support {x : Space} (hx : x ∈ tsupport innerCutoff) :
    outerCutoff x = 1 := by
  rw [inner_support] at hx
  exact outerBump.one_of_mem_closedBall
    (Metric.closedBall_subset_closedBall (by norm_num [outerBump]) hx)

theorem outer_support_unitBall : tsupport outerCutoff ⊆ Metric.ball 0 (1 : ℝ) := by
  rw [outer_support]
  exact Metric.closedBall_subset_ball (by norm_num)

theorem middle_support_unitBall : tsupport middleCutoff ⊆ Metric.ball 0 (1 : ℝ) := by
  rw [middle_support]
  exact Metric.closedBall_subset_ball (by norm_num)

end EulerMeanHarmonic
