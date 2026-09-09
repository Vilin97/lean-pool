/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyGrowthCoefficient

@[expose] public section

/-! Fixed continuous majorants for metric growth; no time continuity of arbitrary bound witnesses
  is required. -/

noncomputable section

namespace EulerGevreyGrowthCoefficient

open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolevSpace
  EulerCylinderViscousEnergy EulerWeightedCylinderEnergy EulerGevreyMetricEstimate

/-- A fixed bound for the metric derivative and viscosity contribution. -/
def growthBudgetBase (c D L : ℝ) : ℝ := (D+4*L^2/c^2)/(2*c^2)

/-- A fixed bound for the velocity-dependent metric transport slope. -/
def growthBudgetSlope (c L : ℝ) : ℝ := 2*L/(2*c^2)

variable (period : ℝ) [Fact (0 < period)]

/-- Uniform actual coefficient bounds control the constant growth term. -/
theorem growthBase_budget (K : SmoothCoefficient period) (K' : LiftL2 period →L[ℝ] LiftL2 period)
    (c D L : ℝ) (hD : ‖K'‖ ≤ D) (hL : (K.firstBound : ℝ) ≤ L) :
    growthBase period K K' c ≤ growthBudgetBase c D L := by
  have hsq : (K.firstBound : ℝ)^2 ≤ L^2 := by nlinarith [K.firstBound.coe_nonneg]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 4))
    (sq_nonneg c)
  unfold growthBase growthBudgetBase heatEnergyConstant
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) (sq_nonneg c))
  calc
    _ = ‖K'‖+4*(K.firstBound : ℝ)^2/c^2 := by ring
    _ ≤ _ := add_le_add hD hh

omit [Fact (0 < period)] in
/-- The actual transport metric slope has a uniform bound for the permitted lifted directions. -/
theorem growthSlope_budget (K : SmoothCoefficient period) (κ : ℝ) (m : Vector3)
    (c L : ℝ) (hκ : |κ| ≤ 1) (hm : ‖m‖ ≤ 1) (hL : (K.firstBound : ℝ) ≤ L) :
    growthSlope period K κ m c ≤ growthBudgetSlope c L := by
  have hL0 : 0 ≤ L := K.firstBound.coe_nonneg.trans hL
  have h := mul_le_mul hL (add_le_add hκ hm) (add_nonneg (abs_nonneg κ) (norm_nonneg m)) hL0
  unfold growthSlope growthBudgetSlope
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) (sq_nonneg c))
  nlinarith only [h]

/-- Uniform actual coefficient budgets majorize the complete viscous growth coefficient. -/
theorem viscousGrowth_budget (K : SmoothCoefficient period) (K' : LiftL2 period →L[ℝ] LiftL2 period)
    (κ : ℝ) (m : Vector3) (c ν D L : ℝ) (B : NNReal)
    (hν : ν ≤ 1) (hκ : |κ| ≤ 1) (hm : ‖m‖ ≤ 1)
    (hD : ‖K'‖ ≤ D) (hL : (K.firstBound : ℝ) ≤ L) :
    viscousGrowthCoefficient period K K' κ m c ν B ≤ growthBudgetBase c D L+growthBudgetSlope c L*B
      :=
  (viscousGrowth_uniform period K K' κ m c ν B hν).trans
    (add_le_add (growthBase_budget period K K' c D L hD hL)
      (mul_le_mul_of_nonneg_right (growthSlope_budget period K κ m c L hκ hm hL) B.coe_nonneg))

/-- The metric PDE growth is bounded by a fixed affine function of the actual metric energy. -/
theorem viscousGrowth_fixed_metric (K : SmoothCoefficient period) (K' : LiftL2 period →L[ℝ] LiftL2
  period)
    (κ : ℝ) (m : Vector3) (c ν D L B X : ℝ) (hc : 0 < c)
    (hν : ν ≤ 1) (hκ : |κ| ≤ 1) (hm : ‖m‖ ≤ 1)
    (hD : ‖K'‖ ≤ D) (hL : (K.firstBound : ℝ) ≤ L) (hB : 0 ≤ B) (hX : 0 ≤ X) :
    viscousGrowthCoefficient period K K' κ m c ν (metricVelocityBound period c B X) ≤
      growthBudgetBase c D L+growthBudgetSlope c L*sobolevEmbeddingConstant period 6*B+
        (growthBudgetSlope c L*sobolevEmbeddingConstant period 6*metricAmplification c)*X := by
  have h := viscousGrowth_budget period K K' κ m c ν D L (metricVelocityBound period c B X) hν hκ
    hm hD hL
  rw [metricVelocityBound_coe period c B X hc hB hX] at h
  exact h.trans_eq (by ring)

end EulerGevreyGrowthCoefficient
