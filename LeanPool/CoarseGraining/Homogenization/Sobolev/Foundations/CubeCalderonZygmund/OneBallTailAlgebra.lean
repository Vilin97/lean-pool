/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalScaledDatumEnergy
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeNormalizedLp

/-! # One Ball Tail Algebra -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-!
# One-ball good-lambda algebra

These are the purely extended-real algebraic steps in the one-stopping-ball
comparison.  They contain no PDE, stopping, or comparison hypotheses: the
analytic proof supplies the two local `L²` bounds, and this file records the
constant bookkeeping that turns their sum into the conventional factor two.
-/

/-- If the correction energy is at most `e` times the original local energy
and `e ≤ 1`, then the harmonic-remainder energy costs at most a factor two.
The statement is deliberately pure `ENNReal` algebra, so it can be used after
the local normalized-energy and Minkowski estimates without importing any
comparison conclusion. -/
theorem oneBall_harmonicGain_scale_le_two
    {A L e : ℝ≥0∞} (he : e ≤ 1) :
    A * (L + e * L) ≤ (2 * A) * L := by
  have hsum : 1 + e ≤ (2 : ℝ≥0∞) := by
    calc
      1 + e ≤ 1 + 1 := add_le_add_right he 1
      _ = 2 := by norm_num
  calc
    A * (L + e * L) = A * ((1 + e) * L) := by ring
    _ ≤ A * (2 * L) := by gcongr
    _ = (2 * A) * L := by ring

/-- Factor the two local weighted-tail contributions through a single uniform
coefficient.  This is the exact overestimate used by the one-ball tail
assembly: `K * m + K' * e` is bounded by `(K + K') * (m + e)`, and the two
tail masses are then factored together. -/
theorem oneBall_tail_coefficient_factor
    (K K' m e Tf Tg : ℝ≥0∞) :
    (K * m + K' * e) * (2 * Tf + 2 * Tg) ≤
      (2 * K + 2 * K') * (m + e) * (Tf + Tg) := by
  have hbase : K * m + K' * e ≤ (K + K') * (m + e) := by
    calc
      K * m + K' * e ≤ (K * m + K' * e) + (K * e + K' * m) :=
        le_add_of_nonneg_right (by positivity)
      _ = (K + K') * (m + e) := by ring
  calc
    (K * m + K' * e) * (2 * Tf + 2 * Tg) =
        (K * m + K' * e) * (2 * (Tf + Tg)) := by ring
    _ ≤ ((K + K') * (m + e)) * (2 * (Tf + Tg)) := by
      exact mul_le_mul_left hbase _
    _ = (2 * K + 2 * K') * (m + e) * (Tf + Tg) := by ring

/-- The powered normalized `L^p` bound on a positive axis cube yields the
raw local integral bound on that open cube.  The factor is exactly `L^d`,
obtained by cancelling the positive normalized-volume density.  This is the
open-cube form used when the final comparison tail is restricted to the
triadic child. -/
theorem axisCube_lintegral_ofReal_norm_rpow_le_volume_mul
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (p : FiniteLpExponent)
    (V : Vec d → E) {B : ℝ≥0∞}
    (hV : eLpNorm V p.exponent (axisCubeNormalizedMeasure z L) ≤ B) :
    (∫⁻ y in axisCube z L,
      ENNReal.ofReal (‖V y‖ ^ p.exponent.toReal) ∂volume) ≤
      ENNReal.ofReal (L ^ d) * B ^ p.exponent.toReal := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((L ^ d)⁻¹)
  let I : ℝ≥0∞ := ∫⁻ y in axisCube z L,
    ENNReal.ofReal (‖V y‖ ^ p.exponent.toReal) ∂volume
  have hpow :
      (eLpNorm V p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal ≤
        B ^ p.exponent.toReal :=
    ENNReal.rpow_le_rpow hV ENNReal.toReal_nonneg
  have hidentity :
      (eLpNorm V p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
        c * I := by
    simpa only [c, I] using
      (axisCube_eLpNorm_rpow_exponent_eq_normalized_setLIntegral z hL p V)
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hL _)))
  have hcTop : c ≠ ∞ := by
    dsimp only [c]
    exact ENNReal.ofReal_ne_top
  have hraw : c * I ≤ B ^ p.exponent.toReal := by
    rw [← hidentity]
    exact hpow
  calc
    I = c⁻¹ * (c * I) := by
      rw [ENNReal.inv_mul_cancel_left hc0 hcTop]
    _ ≤ c⁻¹ * B ^ p.exponent.toReal := by gcongr
    _ = ENNReal.ofReal (L ^ d) * B ^ p.exponent.toReal := by
      rw [show c⁻¹ = ENNReal.ofReal (L ^ d) by
        dsimp only [c]
        rw [ENNReal.ofReal_inv_of_pos (pow_pos hL _)]
        exact inv_inv _]

/-- The `p=2` specialization of
`axisCube_lintegral_ofReal_norm_rpow_le_volume_mul`. -/
theorem axisCube_lintegral_ofReal_norm_sq_le_volume_mul
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (V : Vec d → E) {B : ℝ≥0∞}
    (hV : eLpNorm V 2 (axisCubeNormalizedMeasure z L) ≤ B) :
    (∫⁻ y in axisCube z L,
      ENNReal.ofReal (‖V y‖ ^ (2 : ℕ)) ∂volume) ≤
      ENNReal.ofReal (L ^ d) * B ^ (2 : ℝ) := by
  simpa only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat,
    Real.rpow_two] using
    (axisCube_lintegral_ofReal_norm_rpow_le_volume_mul z hL
      FiniteLpExponent.two V hV)

/-- The powered normalized `L^p` bound on a positive axis cube yields the
raw local integral bound over its a.e.-equal closed ball.  The factor is
exactly the cube volume `L^d`: it is obtained by cancelling the positive
normalized-volume density, not by a comparison estimate. -/
theorem closedBall_lintegral_ofReal_norm_rpow_le_axisCube_volume_mul
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (p : FiniteLpExponent)
    (V : Vec d → E) {B : ℝ≥0∞}
    (hV : MeasureTheory.eLpNorm V p.exponent (axisCubeNormalizedMeasure z L) ≤ B) :
    (∫⁻ y in Metric.closedBall (axisCubeCenter (d := d) z L) (L / 2),
      ENNReal.ofReal (‖V y‖ ^ p.exponent.toReal) ∂(volume : MeasureTheory.Measure (Vec d))) ≤
      ENNReal.ofReal (L ^ d) * B ^ p.exponent.toReal := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((L ^ d)⁻¹)
  let I : ℝ≥0∞ := ∫⁻ y in Metric.closedBall (axisCubeCenter (d := d) z L) (L / 2),
    ENNReal.ofReal (‖V y‖ ^ p.exponent.toReal) ∂(volume : MeasureTheory.Measure (Vec d))
  have hpow :
      (MeasureTheory.eLpNorm V p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal ≤
        B ^ p.exponent.toReal :=
    ENNReal.rpow_le_rpow hV ENNReal.toReal_nonneg
  have hidentity :
      (MeasureTheory.eLpNorm V p.exponent (axisCubeNormalizedMeasure z L)) ^ p.exponent.toReal =
        c * I := by
    simpa only [c, I] using
      (axisCube_eLpNorm_rpow_exponent_eq_normalized_closedBallLIntegral z hL p V)
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hL _)))
  have hcTop : c ≠ ∞ := by
    dsimp only [c]
    exact ENNReal.ofReal_ne_top
  have hraw : c * I ≤ B ^ p.exponent.toReal := by
    rw [← hidentity]
    exact hpow
  calc
    I = c⁻¹ * (c * I) := by
      rw [ENNReal.inv_mul_cancel_left hc0 hcTop]
    _ ≤ c⁻¹ * B ^ p.exponent.toReal := by gcongr
    _ = ENNReal.ofReal (L ^ d) * B ^ p.exponent.toReal := by
      rw [show c⁻¹ = ENNReal.ofReal (L ^ d) by
        dsimp only [c]
        rw [ENNReal.ofReal_inv_of_pos (pow_pos hL _)]
        exact inv_inv _]

/-- The `p=2` specialization of
`closedBall_lintegral_ofReal_norm_rpow_le_axisCube_volume_mul`. -/
theorem closedBall_lintegral_ofReal_norm_sq_le_axisCube_volume_mul
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) {L : ℝ} (hL : 0 < L) (V : Vec d → E) {B : ℝ≥0∞}
    (hV : MeasureTheory.eLpNorm V 2 (axisCubeNormalizedMeasure z L) ≤ B) :
    (∫⁻ y in Metric.closedBall (axisCubeCenter (d := d) z L) (L / 2),
      ENNReal.ofReal (‖V y‖ ^ (2 : ℕ)) ∂(volume : MeasureTheory.Measure (Vec d))) ≤
      ENNReal.ofReal (L ^ d) * B ^ (2 : ℝ) := by
  simpa only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat,
    Real.rpow_two] using
    (closedBall_lintegral_ofReal_norm_rpow_le_axisCube_volume_mul z hL
      FiniteLpExponent.two V hV)

end CubeCalderonZygmund

end

end Homogenization
