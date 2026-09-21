/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeNormalizedLp

/-! # Closed Ball Normalized L2 -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open Filter MeasureTheory Set

/-!
# Exact closed-ball / normalized-cube `L²` bridge

The stopping construction records a real normalized squared energy on closed
sup-metric balls.  The local harmonic comparison uses the `ENNReal` `eLpNorm`
on the a.e.-equal open axis cube.  This file identifies the two normalizations
without a geometric comparison constant.
-/

/-- The squared normalized cube `L²` seminorm is exactly the `ofReal` of the
closed-ball squared energy at the corresponding stopping scale. -/
theorem stoppingAxisCube_eLpNorm_two_sq_eq_ofReal_closedBallL2Energy
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (x : Vec d) {S r : ℝ} (hS : 0 < S) (hr : 0 < r) (F : Vec d → E)
    (hF : MemLp F 2 (volume.restrict (Metric.closedBall x (S * r)))) :
    (eLpNorm F 2
      (axisCubeNormalizedMeasure (stoppingAxisCubeCorner x S r)
        (stoppingAxisCubeSide S r))) ^ (2 : ℝ) =
      ENNReal.ofReal (closedBallL2Energy F x (S * r)) := by
  have hSr : 0 < S * r := mul_pos hS hr
  have hside : 0 < stoppingAxisCubeSide S r := by
    simp only [stoppingAxisCubeSide]
    positivity
  have hcenter :
      axisCubeCenter (stoppingAxisCubeCorner x S r) (stoppingAxisCubeSide S r) = x := by
    ext i
    simp only [axisCubeCenter, stoppingAxisCubeCorner, stoppingAxisCubeSide]
    ring
  have hhalf : stoppingAxisCubeSide S r / 2 = S * r := by
    simp only [stoppingAxisCubeSide]
    ring
  have hpow := axisCube_eLpNorm_two_sq_eq_normalized_closedBallLIntegral
    (z := stoppingAxisCubeCorner x S r) hside F
  rw [hcenter, hhalf] at hpow
  have hint : IntegrableOn (fun y : Vec d => ‖F y‖ ^ (2 : ℕ))
      (Metric.closedBall x (S * r)) volume := by
    exact hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have henergy :
      ENNReal.ofReal (closedBallL2Energy F x (S * r)) =
        ENNReal.ofReal ((stoppingAxisCubeSide S r) ^ d)⁻¹ *
          ∫⁻ y in Metric.closedBall x (S * r), ENNReal.ofReal (‖F y‖ ^ (2 : ℕ))
            ∂volume := by
    rw [closedBallL2Energy, closedBallAverage_eq_setAverage x hSr.le]
    rw [MeasureTheory.ofReal_setAverage hint (ae_of_all _ fun y => sq_nonneg (‖F y‖))]
    rw [Real.volume_pi_closedBall x hSr.le, ENNReal.div_eq_inv_mul]
    congr 1
    simp only [stoppingAxisCubeSide]
    rw [show (2 * S * r) ^ d = (2 * (S * r)) ^ d by ring]
    rw [← ENNReal.ofReal_inv_of_pos]
    · simp only [Fintype.card_fin]
    · positivity
  exact hpow.trans henergy.symm

/-- The normalized cube `L²` seminorm is exactly the square root of the
closed-ball squared energy at the corresponding stopping scale. -/
theorem stoppingAxisCube_eLpNorm_two_eq_ofReal_sqrt_closedBallL2Energy
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (x : Vec d) {S r : ℝ} (hS : 0 < S) (hr : 0 < r) (F : Vec d → E)
    (hF : MemLp F 2 (volume.restrict (Metric.closedBall x (S * r)))) :
    eLpNorm F 2
      (axisCubeNormalizedMeasure (stoppingAxisCubeCorner x S r)
        (stoppingAxisCubeSide S r)) =
      ENNReal.ofReal (Real.sqrt (closedBallL2Energy F x (S * r))) := by
  have henergy_nonneg : 0 ≤ closedBallL2Energy F x (S * r) := by
    rw [closedBallL2Energy, closedBallAverage_eq_setAverage x (mul_pos hS hr).le]
    exact MeasureTheory.integral_nonneg fun y => sq_nonneg (‖F y‖)
  have hsq := stoppingAxisCube_eLpNorm_two_sq_eq_ofReal_closedBallL2Energy
    x hS hr F hF
  apply le_antisymm
  · rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2), hsq]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, Real.sq_sqrt henergy_nonneg]
  · rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2), hsq]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, Real.sq_sqrt henergy_nonneg]

/-- The global `L²` assumption supplies the local integrability needed by the
exact stopping-cube energy bridge. -/
theorem stoppingAxisCube_eLpNorm_two_eq_ofReal_sqrt_closedBallL2Energy_of_memLp
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (x : Vec d) {S r : ℝ} (hS : 0 < S) (hr : 0 < r) (F : Vec d → E)
    (hF : MemLp F 2 volume) :
    eLpNorm F 2
      (axisCubeNormalizedMeasure (stoppingAxisCubeCorner x S r)
        (stoppingAxisCubeSide S r)) =
      ENNReal.ofReal (Real.sqrt (closedBallL2Energy F x (S * r))) :=
  stoppingAxisCube_eLpNorm_two_eq_ofReal_sqrt_closedBallL2Energy x hS hr F
    (hF.restrict _)

/-- The exact `L²` bridge at the harmonic comparison parent. -/
theorem stoppingComparisonParent_eLpNorm_two_eq_ofReal_sqrt_closedBallL2Energy
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (x : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) (F : Vec d → E)
    (hF : MemLp F 2
      (volume.restrict (Metric.closedBall x (stoppingComparisonParentMultiplier n * r)))) :
    eLpNorm F 2
      (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r n)
        (stoppingComparisonParentSide r n)) =
      ENNReal.ofReal
        (Real.sqrt (closedBallL2Energy F x (stoppingComparisonParentMultiplier n * r))) := by
  exact stoppingAxisCube_eLpNorm_two_eq_ofReal_sqrt_closedBallL2Energy x
    (by
      simp only [stoppingComparisonParentMultiplier]
      positivity)
    hr F hF

end CubeCalderonZygmund

end

end Homogenization
