/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate

@[expose] public section

/-! Actual metric-energy growth coefficients bounded uniformly for artificial viscosities at most
  one. -/

noncomputable section

namespace EulerGevreyGrowthCoefficient

open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolevSpace
  EulerCylinderViscousEnergy EulerWeightedCylinderEnergy EulerGevreyMetricEstimate
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The viscosity-uniform constant part of the actual metric growth coefficient. -/
def growthBase (K : SmoothCoefficient period) (K' : LiftL2 period →L[ℝ] LiftL2 period) (c : ℝ) : ℝ
  :=
  (‖K'‖+2*heatEnergyConstant period K c)/(2*c^2)

/-- The exact slope of the actual metric growth coefficient with respect to the velocity bound. -/
def growthSlope (K : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) : ℝ :=
  (K.firstBound : ℝ)*(|κ|+‖m‖)/(2*c^2)

theorem growthBase_nonneg (K : SmoothCoefficient period) (K' : LiftL2 period →L[ℝ] LiftL2 period)
  (c : ℝ) :
    0 ≤ growthBase period K K' c := by
  unfold growthBase heatEnergyConstant
  positivity

omit [Fact (0 < period)] in
theorem growthSlope_nonneg (K : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) :
    0 ≤ growthSlope period K κ m c := by
  unfold growthSlope
  positivity

/-- Artificial viscosity contributes no unbounded constant to the actual energy estimate as it tends to zero. -/
theorem viscousGrowth_uniform (K : SmoothCoefficient period) (K' : LiftL2 period →L[ℝ] LiftL2
  period)
    (κ : ℝ) (m : Vector3) (c ν : ℝ) (B : NNReal) (hν : ν ≤ 1) :
    viscousGrowthCoefficient period K K' κ m c ν B ≤ growthBase period K K' c+growthSlope period K
      κ m c*B := by
  have hheat : 0 ≤ heatEnergyConstant period K c := by unfold heatEnergyConstant; positivity
  have hv := mul_le_mul_of_nonneg_right hν hheat
  have hn : ‖K'‖+2*transportEnergyConstant period K κ m B+2*ν*heatEnergyConstant period K c ≤
      ‖K'‖+2*transportEnergyConstant period K κ m B+2*heatEnergyConstant period K c := by nlinarith
        only [hv]
  have h := div_le_div_of_nonneg_right hn (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg c))
  exact h.trans_eq (by unfold growthBase growthSlope transportEnergyConstant; ring)

/-- The chosen genuine pointwise velocity bound depends continuously on the actual metric energy. -/
theorem metricVelocityBound_continuous (c B : ℝ) : Continuous (metricVelocityBound period c B) := by
  exact continuous_real_toNNReal.comp
    (continuous_const.mul (continuous_const.add (continuous_const.mul continuous_id)))

/-- Its NNReal coercion is exactly the intended positive metric-energy majorant. -/
theorem metricVelocityBound_coe (c B X : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hX : 0 ≤ X) :
    (metricVelocityBound period c B X : ℝ) = sobolevEmbeddingConstant period
      6*(B+metricAmplification c*X) := by
  exact Real.coe_toNNReal _ (mul_nonneg (sobolevEmbeddingConstant_nonneg period 6)
    (add_nonneg hB (mul_nonneg (le_trans zero_le_one (metricAmplification_one_le hc)) hX)))

/-- The actual energy growth coefficient is affine in the metric error energy, uniformly for 0<ν≤1. -/
theorem viscousGrowth_metric (K : SmoothCoefficient period) (K' : LiftL2 period →L[ℝ] LiftL2 period)
    (κ : ℝ) (m : Vector3) (c ν B X : ℝ) (hc : 0 < c) (hν : ν ≤ 1) (hB : 0 ≤ B) (hX : 0 ≤ X) :
    viscousGrowthCoefficient period K K' κ m c ν (metricVelocityBound period c B X) ≤
      growthBase period K K' c+growthSlope period K κ m c*sobolevEmbeddingConstant period 6*B+
        (growthSlope period K κ m c*sobolevEmbeddingConstant period 6*metricAmplification c)*X := by
  have h := viscousGrowth_uniform period K K' κ m c ν (metricVelocityBound period c B X) hν
  rw [metricVelocityBound_coe period c B X hc hB hX] at h
  exact h.trans_eq (by ring)

/-- One positive constant absorbs every derived scalar growth coefficient while preserving the signed radius term. -/
theorem absorb_scalar_coefficients (g0 g1 f0 f1 f2 d r X Y B R C : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hf0 : 0 ≤ f0) (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hd : 0 ≤ d)
    (hr : 0 ≤ r) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hC : 1+g0+g1+f0+f1+f2+d ≤ C) (b : ℝ) :
    (g0+g1*X)*X+b*Y+(f0*r+f1*X+f2*X^2+d*R*(B+X)*Y) ≤
      C*(X+X^2+r)+(b+C*R*(B+X))*Y := by
  have hc0 : f0 ≤ C := by linarith
  have hc1 : g0+f1 ≤ C := by linarith
  have hc2 : g1+f2 ≤ C := by linarith
  have hcd : d ≤ C := by linarith
  have h0 := mul_le_mul_of_nonneg_right hc0 hr
  have h1 := mul_le_mul_of_nonneg_right hc1 hX
  have h2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg X)
  have h3 := mul_le_mul_of_nonneg_right hcd (mul_nonneg (mul_nonneg hR (add_nonneg hB hX)) hY)
  nlinarith only [h0,h1,h2,h3]

end EulerGevreyGrowthCoefficient
