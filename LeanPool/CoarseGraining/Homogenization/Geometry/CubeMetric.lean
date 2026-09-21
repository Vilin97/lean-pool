/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Multiscale.CubeAverage
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Cube Metric -/

namespace Homogenization

open scoped Topology

noncomputable def cubeCenter {d : ℕ} (Q : TriadicCube d) : Vec d :=
  fun i => (Q.index i : ℝ) * cubeScaleFactor Q

noncomputable def cubeRadius {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (1 / 2 : ℝ) * cubeScaleFactor Q

private theorem cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

theorem cubeRadius_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeRadius Q := by
  unfold cubeRadius
  exact mul_pos (by norm_num) (cubeScaleFactor_pos Q)

theorem cubeRadius_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ cubeRadius Q := le_of_lt (cubeRadius_pos Q)

theorem cubeScaleFactor_eq_two_mul_cubeRadius {d : ℕ} (Q : TriadicCube d) :
    cubeScaleFactor Q = 2 * cubeRadius Q := by
  unfold cubeRadius
  ring

theorem cubeScaleFactor_eq_one_of_scale_eq_zero {d : ℕ} {Q : TriadicCube d}
    (hQ : Q.scale = 0) :
    cubeScaleFactor Q = 1 := by
  simp [cubeScaleFactor, hQ]

theorem cubeRadius_eq_half_of_scale_eq_zero {d : ℕ} {Q : TriadicCube d}
    (hQ : Q.scale = 0) :
    cubeRadius Q = (1 / 2 : ℝ) := by
  unfold cubeRadius
  rw [cubeScaleFactor_eq_one_of_scale_eq_zero hQ]
  norm_num

private theorem cubeCenter_sub_cubeRadius {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    cubeCenter Q i - cubeRadius Q =
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
  simp [cubeCenter, cubeRadius]
  ring_nf

private theorem cubeCenter_add_cubeRadius {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    cubeCenter Q i + cubeRadius Q =
      (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
  simp [cubeCenter, cubeRadius]
  ring_nf

theorem closedBall_cubeCenter_eq_pi_Icc {d : ℕ} (Q : TriadicCube d) :
    Metric.closedBall (cubeCenter Q) (cubeRadius Q) =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Icc
            (cubeCenter Q i - cubeRadius Q)
            (cubeCenter Q i + cubeRadius Q)) := by
  rw [closedBall_pi (cubeCenter Q) (cubeRadius_nonneg Q)]
  ext x
  constructor
  · intro hx
    simpa [Set.mem_pi, Set.mem_univ, true_implies, cubeCenter, cubeRadius,
      Real.closedBall_eq_Icc, cubeCenter_sub_cubeRadius,
      cubeCenter_add_cubeRadius] using hx
  · intro hx
    simpa [Set.mem_pi, Set.mem_univ, true_implies, cubeCenter, cubeRadius,
      Real.closedBall_eq_Icc, cubeCenter_sub_cubeRadius,
      cubeCenter_add_cubeRadius] using hx

theorem ball_cubeCenter_eq_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    Metric.ball (cubeCenter Q) (cubeRadius Q) = openCubeSet Q := by
  have hball_pi :
      Metric.ball (cubeCenter Q) (cubeRadius Q) =
        Set.pi Set.univ
          (fun i : Fin d => Set.Ioo (cubeCenter Q i - cubeRadius Q) (cubeCenter Q i + cubeRadius Q)) := by
    rw [ball_pi (cubeCenter Q) (cubeRadius_pos Q)]
    ext x
    simp [Real.ball_eq_Ioo]
  rw [hball_pi, openCubeSet_eq_pi_Ioo]
  simp [cubeCenter_sub_cubeRadius, cubeCenter_add_cubeRadius]

theorem cubeSet_subset_closedBall {d : ℕ} (Q : TriadicCube d) :
    cubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
  intro x hx
  rw [closedBall_cubeCenter_eq_pi_Icc]
  rw [cubeSet_eq_pi_Ico] at hx
  intro i hi
  have hxi := hx i hi
  refine ⟨?_, le_of_lt ?_⟩
  · dsimp [cubeCenter, cubeRadius]
    nlinarith [hxi.1]
  · dsimp [cubeCenter, cubeRadius]
    nlinarith [hxi.2]

theorem cubeSet_ae_eq_closedBall {d : ℕ} (Q : TriadicCube d) :
    cubeSet Q =ᵐ[MeasureTheory.volume] Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
  rw [cubeSet_eq_pi_Ico, closedBall_cubeCenter_eq_pi_Icc]
  simpa [cubeCenter_sub_cubeRadius, cubeCenter_add_cubeRadius] using!
    (MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc
      (μ := fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := fun i : Fin d => (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
      (g := fun i : Fin d => (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)))

theorem cubeAverage_eq_setAverage_cubeSet {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q f = ⨍ x in cubeSet Q, f x ∂MeasureTheory.volume := by
  have hreal : MeasureTheory.volume.real (cubeSet Q) = cubeVolume Q := by
    rw [MeasureTheory.measureReal_def]
    exact volume_cubeSet_toReal (Q := Q)
  calc
    cubeAverage Q f = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume := rfl
    _ = (MeasureTheory.volume.real (cubeSet Q))⁻¹ *
          ∫ x in cubeSet Q, f x ∂MeasureTheory.volume := by rw [hreal]
    _ = ⨍ x in cubeSet Q, f x ∂MeasureTheory.volume := by
      rw [MeasureTheory.setAverage_eq]
      simp

theorem cubeAverage_eq_setAverage_closedBall {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q f =
      ⨍ x in Metric.closedBall (cubeCenter Q) (cubeRadius Q), f x ∂MeasureTheory.volume := by
  rw [cubeAverage_eq_setAverage_cubeSet]
  exact MeasureTheory.setAverage_congr (cubeSet_ae_eq_closedBall Q)

end Homogenization
