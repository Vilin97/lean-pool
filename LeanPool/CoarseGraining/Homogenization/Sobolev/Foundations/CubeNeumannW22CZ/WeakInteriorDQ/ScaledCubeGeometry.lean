/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule

/-! # Scaled Cube Geometry -/

namespace Homogenization

open scoped Topology

noncomputable section

/-- A closed concentric cube of smaller relative radius lies in the open
concentric cube of any strictly larger relative radius. -/
theorem scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt {d : ℕ}
    (Q : TriadicCube d) {ρ σ : ℝ} (hρσ : ρ < σ) :
    scaledClosedCubeSet Q ρ ⊆ scaledOpenCubeSet Q σ := by
  intro x hx i
  calc
    |x i - cubeCenter Q i| ≤ ρ * cubeRadius Q := hx i
    _ < σ * cubeRadius Q :=
      mul_lt_mul_of_pos_right hρσ (cubeRadius_pos Q)

/-- Positive scaled open cubes are metric balls for the sup metric on `Vec d`. -/
theorem ball_cubeCenter_mul_cubeRadius_eq_scaledOpenCubeSet {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ : 0 < ρ) :
    Metric.ball (cubeCenter Q) (ρ * cubeRadius Q) =
      scaledOpenCubeSet Q ρ := by
  have hrad : 0 < ρ * cubeRadius Q := mul_pos hρ (cubeRadius_pos Q)
  rw [ball_pi (cubeCenter Q) hrad]
  ext x
  constructor
  · intro hx i
    have hi := hx i (by simp)
    rw [Metric.mem_ball, Real.dist_eq] at hi
    simpa [scaledOpenCubeSet, abs_sub_comm] using hi
  · intro hx i _hi
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [scaledOpenCubeSet, abs_sub_comm] using hx i

/-- Positive scaled open cubes are admissible open bounded convex domains. -/
theorem isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpenBoundedConvexDomain (scaledOpenCubeSet Q ρ) := by
  have hball :
      IsOpenBoundedConvexDomain
        (Metric.ball (cubeCenter Q) (ρ * cubeRadius Q)) :=
    isOpenBoundedConvexDomain_ball (cubeCenter Q)
      (mul_pos hρ (cubeRadius_pos Q))
  simpa [ball_cubeCenter_mul_cubeRadius_eq_scaledOpenCubeSet Q hρ] using hball

end

end Homogenization
