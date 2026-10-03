/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.StoppingCubeGeometry

/-! # One Ball Scale Factor -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-!
# Exact scale factors for the one-ball good-`lambda` estimate

This module isolates the elementary extended-real identities which convert
the local harmonic and correction tails into a stopping-ball volume times the
square of the level.  Keeping them separate from the PDE comparison avoids
any hidden finite-measure or cancellation assumptions in the one-ball proof.
-/

/-- At the harmonic-tail threshold, the negative threshold power cancels all
but two powers of the positive level.  Finiteness of `A` is precisely what
allows the `ENNReal` product to pass through the real exponent. -/
theorem oneBall_harmonic_threshold_rpow_factor
    {qR M level : ℝ} {A : ℝ≥0∞}
    (hM : 0 < M) (hlevel : 0 < level) (hA : A ≠ ∞) :
    ENNReal.ofReal ((M * level / 2) ^ (2 - qR)) *
        (A * ENNReal.ofReal level) ^ qR =
      ENNReal.ofReal ((M / 2) ^ (2 - qR)) * A ^ qR *
        ENNReal.ofReal (level ^ (2 : ℝ)) := by
  have hMtwo : 0 < M / 2 := by positivity
  have hlevel_zero : ENNReal.ofReal level ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hlevel)
  have hlevel_top : ENNReal.ofReal level ≠ ∞ := ENNReal.ofReal_ne_top
  rw [show M * level / 2 = (M / 2) * level by ring,
    Real.mul_rpow hMtwo.le hlevel.le]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hMtwo.le _)]
  rw [ENNReal.mul_rpow_of_ne_top hA ENNReal.ofReal_ne_top]
  rw [← ENNReal.ofReal_rpow_of_pos hMtwo,
    ← ENNReal.ofReal_rpow_of_pos hlevel]
  calc
    _ = ENNReal.ofReal (M / 2) ^ (2 - qR) * A ^ qR *
        (ENNReal.ofReal level ^ (2 - qR) * ENNReal.ofReal level ^ qR) := by
      ring
    _ = ENNReal.ofReal (M / 2) ^ (2 - qR) * A ^ qR *
        ENNReal.ofReal level ^ ((2 - qR) + qR) := by
      rw [ENNReal.rpow_add _ _ hlevel_zero hlevel_top]
    _ = _ := by
      rw [← ENNReal.ofReal_rpow_of_pos hlevel]
      congr 3
      linarith

/-- The side-`10r` cube has exactly `5^d` times the volume of the
sup-metric stopping ball of radius `r`. -/
theorem oneBall_child_side_volume
    {d : ℕ} [NeZero d] (x : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal ((10 * r) ^ d) =
      (5 : ℝ≥0∞) ^ d * volume (Metric.closedBall x r) := by
  rw [Real.volume_pi_closedBall x hr]
  rw [show 10 * r = 5 * (2 * r) by ring, mul_pow]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (5 : ℝ) ^ d)]
  rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (5 : ℝ))]
  simp only [Fintype.card_fin]
  norm_num

/-- The side of the depth-`n` comparison parent contributes the exact
relative factor `(5 * 3^n)^d` against the stopping ball of radius `r`. -/
theorem oneBall_parent_side_volume
    {d : ℕ} [NeZero d] (x : Vec d) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    ENNReal.ofReal ((10 * (3 : ℝ) ^ n * r) ^ d) =
      (5 * (3 : ℝ≥0∞) ^ n) ^ d * volume (Metric.closedBall x r) := by
  rw [Real.volume_pi_closedBall x hr]
  rw [show 10 * (3 : ℝ) ^ n * r = (5 * (3 : ℝ) ^ n) * (2 * r) by ring,
    mul_pow]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (5 * (3 : ℝ) ^ n) ^ d)]
  rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 5 * (3 : ℝ) ^ n)]
  simp only [Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (5 : ℝ))]
  rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (3 : ℝ))]
  norm_num

/-- The harmonic local-tail scale factor, already expressed relative to the
stopping ball.  Here `A` is the complete harmonic coefficient (for example,
`2 * G.constant * d`), so no factor is silently discarded. -/
theorem oneBall_harmonic_tail_scale_factor
    {d : ℕ} [NeZero d] {qR M level r : ℝ} {A : ℝ≥0∞}
    (x : Vec d) (hr : 0 ≤ r) (hM : 0 < M) (hlevel : 0 < level)
    (hA : A ≠ ∞) :
    2 * ENNReal.ofReal ((M * level / 2) ^ (2 - qR)) *
        (ENNReal.ofReal ((10 * r) ^ d) *
          (A * ENNReal.ofReal level) ^ qR) =
      2 * (5 : ℝ≥0∞) ^ d * A ^ qR *
        ENNReal.ofReal ((M / 2) ^ (2 - qR)) *
        ENNReal.ofReal (level ^ (2 : ℝ)) *
        volume (Metric.closedBall x r) := by
  rw [oneBall_child_side_volume x hr]
  calc
    _ = 2 * (5 : ℝ≥0∞) ^ d * volume (Metric.closedBall x r) *
        (ENNReal.ofReal ((M * level / 2) ^ (2 - qR)) *
          (A * ENNReal.ofReal level) ^ qR) := by ring
    _ = _ := by
      rw [oneBall_harmonic_threshold_rpow_factor hM hlevel hA]
      ring

/-- The correction local-tail scale factor, already expressed relative to the
stopping ball. -/
theorem oneBall_correction_tail_scale_factor
    {d : ℕ} [NeZero d] {eps level r : ℝ} (x : Vec d) (hr : 0 ≤ r)
    (heps : 0 ≤ eps) (hlevel : 0 ≤ level) (n : ℕ) :
    6 * ENNReal.ofReal ((10 * (3 : ℝ) ^ n * r) ^ d) *
        (ENNReal.ofReal (eps * level) ^ (2 : ℕ)) =
      6 * (5 * (3 : ℝ≥0∞) ^ n) ^ d * ENNReal.ofReal (eps ^ (2 : ℕ)) *
        ENNReal.ofReal (level ^ (2 : ℕ)) * volume (Metric.closedBall x r) := by
  rw [oneBall_parent_side_volume x hr n]
  rw [ENNReal.ofReal_mul heps, mul_pow]
  rw [ENNReal.ofReal_pow heps, ENNReal.ofReal_pow hlevel]
  ring

end CubeCalderonZygmund

end

end Homogenization
