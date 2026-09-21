/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.StoppingRadius

/-! # Stopping Cube Geometry -/

namespace Homogenization

open scoped Topology

noncomputable section

namespace CubeCalderonZygmund

open Filter MeasureTheory Set

/-!
# Axis cubes at a good-`lambda` stopping scale

The Vitali argument is formulated with sup-metric balls in `Vec d`.  This
module identifies those balls with the axis cubes used by the harmonic
replacement and harmonic-gain APIs.  The comparison parent has radius
`5 * 3^n * r`; its concentric depth-`n` descendant is exactly the comparison
ball of radius `5 * r`.
-/

/-- The lower corner of the axis cube representing the sup-metric ball of
radius `S * r` around `x`. -/
def stoppingAxisCubeCorner {d : ℕ} (x : Vec d) (S r : ℝ) : Vec d :=
  fun i => x i - S * r

/-- The side length of the axis cube representing the sup-metric ball of
radius `S * r` around `x`. -/
def stoppingAxisCubeSide (S r : ℝ) : ℝ :=
  2 * S * r

/-- A positive-radius sup-metric ball is exactly its open axis-cube
realization. -/
theorem axisCube_stoppingAxisCubeCorner_eq_ball {d : ℕ} (x : Vec d)
    {S r : ℝ} (hS : 0 < S) (hr : 0 < r) :
    axisCube (stoppingAxisCubeCorner x S r) (stoppingAxisCubeSide S r) =
      Metric.ball x (S * r) := by
  have hSr : 0 < S * r := mul_pos hS hr
  rw [ball_pi x hSr]
  ext y
  simp only [axisCube, stoppingAxisCubeCorner, stoppingAxisCubeSide,
    Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo, Real.ball_eq_Ioo]
  constructor <;> intro hy <;> intro i
  · constructor <;> linarith [hy i]
  · constructor <;> linarith [hy i]

/-- The open stopping cube and its closed sup-metric ball agree almost
everywhere for Lebesgue measure. -/
theorem axisCube_stoppingAxisCubeCorner_ae_eq_closedBall {d : ℕ} [NeZero d]
    (x : Vec d) {S r : ℝ} (hS : 0 < S) (hr : 0 < r) :
    axisCube (stoppingAxisCubeCorner x S r) (stoppingAxisCubeSide S r) =ᵐ[volume]
      Metric.closedBall x (S * r) := by
  rw [axisCube_stoppingAxisCubeCorner_eq_ball x hS hr]
  have hsphere : ∀ᵐ y ∂volume, y ∉ Metric.sphere x (S * r) := by
    rw [ae_iff]
    simpa using! (volume_sphere_eq_zero (d := d) x (S * r))
  filter_upwards [hsphere] with y hy
  apply propext
  constructor
  · intro hyball
    exact Metric.ball_subset_closedBall hyball
  · intro hyclosed
    by_contra hynot
    have hdist_le : dist y x ≤ S * r := Metric.mem_closedBall.mp hyclosed
    have hdist_ge : S * r ≤ dist y x := by
      exact le_of_not_gt fun hlt => hynot (Metric.mem_ball.mpr hlt)
    exact hy (Metric.mem_sphere.mpr (le_antisymm hdist_le hdist_ge))

/-- The comparison parent multiplier: after `n` concentric contractions, a
radius `5 * 3^n * r` becomes `5 * r`. -/
def stoppingComparisonParentMultiplier (n : ℕ) : ℝ :=
  5 * (3 : ℝ) ^ n

/-- The parent cube used for a depth-`n` harmonic comparison at stopping
radius `r`. -/
def stoppingComparisonParentCorner {d : ℕ} (x : Vec d) (r : ℝ) (n : ℕ) : Vec d :=
  stoppingAxisCubeCorner x (stoppingComparisonParentMultiplier n) r

/-- The side length of the comparison parent cube. -/
def stoppingComparisonParentSide (r : ℝ) (n : ℕ) : ℝ :=
  stoppingAxisCubeSide (stoppingComparisonParentMultiplier n) r

private theorem stoppingComparisonParentMultiplier_pos (n : ℕ) :
    0 < stoppingComparisonParentMultiplier n := by
  simp only [stoppingComparisonParentMultiplier]
  positivity

private theorem stoppingComparisonParentSide_eq {r : ℝ} (n : ℕ) :
    stoppingComparisonParentSide r n = 10 * (3 : ℝ) ^ n * r := by
  simp only [stoppingComparisonParentSide, stoppingAxisCubeSide,
    stoppingComparisonParentMultiplier]
  ring

/-- The comparison parent is the open sup-metric ball with radius
`5 * 3^n * r`. -/
theorem stoppingComparisonParent_axisCube_eq_ball {d : ℕ} (x : Vec d)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    axisCube (stoppingComparisonParentCorner x r n)
        (stoppingComparisonParentSide r n) =
      Metric.ball x (stoppingComparisonParentMultiplier n * r) :=
  axisCube_stoppingAxisCubeCorner_eq_ball x
    (stoppingComparisonParentMultiplier_pos n) hr

/-- The comparison parent and its closed sup-metric ball agree almost
everywhere. -/
theorem stoppingComparisonParent_axisCube_ae_eq_closedBall {d : ℕ} [NeZero d]
    (x : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    axisCube (stoppingComparisonParentCorner x r n)
        (stoppingComparisonParentSide r n) =ᵐ[volume]
      Metric.closedBall x (stoppingComparisonParentMultiplier n * r) :=
  axisCube_stoppingAxisCubeCorner_ae_eq_closedBall x
    (stoppingComparisonParentMultiplier_pos n) hr

private theorem axisCubeConcentricDepthSide_stoppingComparisonParent
    (r : ℝ) (n : ℕ) :
    axisCubeConcentricDepthSide (stoppingComparisonParentSide r n) n =
      stoppingAxisCubeSide 5 r := by
  rw [stoppingComparisonParentSide_eq]
  simp only [axisCubeConcentricDepthSide, stoppingAxisCubeSide, zpow_neg,
    zpow_natCast]
  field_simp [pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)]
  ring

private theorem axisCubeConcentricDepthCorner_stoppingComparisonParent
    {d : ℕ} (x : Vec d) (r : ℝ) (n : ℕ) :
    axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r n)
        (stoppingComparisonParentSide r n) n =
      stoppingAxisCubeCorner x 5 r := by
  ext i
  rw [stoppingComparisonParentSide_eq]
  simp only [axisCubeConcentricDepthCorner, stoppingComparisonParentCorner,
    stoppingAxisCubeCorner, axisCubeCenter, axisCubeConcentricDepthSide,
    stoppingComparisonParentMultiplier, zpow_neg,
    zpow_natCast, div_eq_mul_inv]
  field_simp [pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- The depth-`n` concentric descendant of the comparison parent is exactly
the stopping-scale comparison ball of radius `5 * r`. -/
theorem stoppingComparison_concentricDepth_axisCube_eq_ball {d : ℕ}
    (x : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    axisCube
        (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r n)
          (stoppingComparisonParentSide r n) n)
        (axisCubeConcentricDepthSide (stoppingComparisonParentSide r n) n) =
      Metric.ball x (5 * r) := by
  rw [axisCubeConcentricDepthCorner_stoppingComparisonParent x r n,
    axisCubeConcentricDepthSide_stoppingComparisonParent r n]
  exact axisCube_stoppingAxisCubeCorner_eq_ball x (by norm_num) hr

/-- The depth-`n` comparison descendant and the closed stopping-scale ball
agree almost everywhere. -/
theorem stoppingComparison_concentricDepth_axisCube_ae_eq_closedBall
    {d : ℕ} [NeZero d] (x : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    axisCube
        (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r n)
          (stoppingComparisonParentSide r n) n)
        (axisCubeConcentricDepthSide (stoppingComparisonParentSide r n) n) =ᵐ[volume]
      Metric.closedBall x (5 * r) := by
  rw [stoppingComparison_concentricDepth_axisCube_eq_ball x hr n]
  have hsphere : ∀ᵐ y ∂volume, y ∉ Metric.sphere x (5 * r) := by
    rw [ae_iff]
    simpa using! (volume_sphere_eq_zero (d := d) x (5 * r))
  filter_upwards [hsphere] with y hy
  apply propext
  constructor
  · intro hyball
    exact Metric.ball_subset_closedBall hyball
  · intro hyclosed
    by_contra hynot
    have hdist_le : dist y x ≤ 5 * r := Metric.mem_closedBall.mp hyclosed
    have hdist_ge : 5 * r ≤ dist y x := by
      exact le_of_not_gt fun hlt => hynot (Metric.mem_ball.mpr hlt)
    exact hy (Metric.mem_sphere.mpr (le_antisymm hdist_le hdist_ge))

/-- The largest comparison radius required by the depth-`n` parent. -/
def stoppingComparisonRadius (r : ℝ) (n : ℕ) : ℝ :=
  10 * (3 : ℝ) ^ n * r

theorem stoppingComparisonRadius_eq_two_mul_parentRadius (r : ℝ) (n : ℕ) :
    stoppingComparisonRadius r n =
      2 * (stoppingComparisonParentMultiplier n * r) := by
  simp only [stoppingComparisonRadius, stoppingComparisonParentMultiplier]
  ring

/-- A positive stopping radius is no larger than its comparison radius. -/
theorem le_stoppingComparisonRadius {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    r ≤ stoppingComparisonRadius r n := by
  have hpow : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hfactor : 1 ≤ 10 * (3 : ℝ) ^ n := by nlinarith
  calc
    r = 1 * r := by ring
    _ ≤ (10 * (3 : ℝ) ^ n) * r := mul_le_mul_of_nonneg_right hfactor hr
    _ = stoppingComparisonRadius r n := rfl

/-- The stopping-scale cutoff ensures that the full comparison parent remains
within the radius on which the last-exit bound is available. -/
theorem stoppingComparisonRadius_le_of_le {r R : ℝ} (n : ℕ)
    (h : r ≤ R / (10 * (3 : ℝ) ^ n)) :
    stoppingComparisonRadius r n ≤ R := by
  have hdenom : 0 < 10 * (3 : ℝ) ^ n := by positivity
  rw [le_div_iff₀ hdenom] at h
  calc
    stoppingComparisonRadius r n = r * (10 * (3 : ℝ) ^ n) := by
      simp only [stoppingComparisonRadius]
      ring
    _ ≤ R := h

/-- A stopping radius bounded by `R / (10 * 3^n)` can be used both at its own
scale and at the comparison-parent scale before the last-exit radius `R`. -/
theorem stoppingComparisonRadius_bounds_of_le {r R : ℝ} (hr : 0 ≤ r) (n : ℕ)
    (h : r ≤ R / (10 * (3 : ℝ) ^ n)) :
    r ≤ stoppingComparisonRadius r n ∧ stoppingComparisonRadius r n ≤ R :=
  ⟨le_stoppingComparisonRadius hr n, stoppingComparisonRadius_le_of_le n h⟩

/-- Under the conservative `10 * 3^n` cutoff, the actual comparison-parent
radius `5 * 3^n * r` lies in the last-exit interval from `r` to `R`. -/
theorem stoppingComparisonParentRadius_mem_Icc_of_le {r R : ℝ}
    (hr : 0 ≤ r) (n : ℕ) (h : r ≤ R / (10 * (3 : ℝ) ^ n)) :
    stoppingComparisonParentMultiplier n * r ∈ Icc r R := by
  have hpow : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hlower : r ≤ stoppingComparisonParentMultiplier n * r := by
    rw [stoppingComparisonParentMultiplier]
    nlinarith
  have hparent_nonneg : 0 ≤ stoppingComparisonParentMultiplier n * r := by
    exact mul_nonneg (stoppingComparisonParentMultiplier_pos n).le hr
  have hparent_le_comparison :
      stoppingComparisonParentMultiplier n * r ≤ stoppingComparisonRadius r n := by
    rw [stoppingComparisonRadius_eq_two_mul_parentRadius]
    nlinarith
  exact ⟨hlower,
    hparent_le_comparison.trans (stoppingComparisonRadius_le_of_le n h)⟩

end CubeCalderonZygmund

end

end Homogenization
