/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmallCorrectionBounds

@[expose] public section

/-! A genuine all-order correction budget for small smooth data with the
identity metric. Every field and coefficient estimate is derived from the
given datum's actual word bound; the amplitude is chosen explicitly. -/

noncomputable section

namespace EulerSmallCorrection

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerPacketCylinderField
  EulerPacketProfileRecursion EulerAllOrderCorrectionData EulerCorrectionEnergyData
  EulerCorrectionEnergyMajorants EulerConstantCorrection EulerSobolevGevreyOperators
  EulerQuadraticSource EulerSobolevDriftNorm EulerFunctionalVelocity EulerSobolevTransport
  EulerGevreyGrowthCoefficient EulerGevreyMetricEstimate EulerNonlinearEnergyConstants

variable {P : ℝ} [Fact (0 < P)] {raw : VectorField}
  (G : Field P 1 raw) {C R : ℝ} (hG : G.WordBound 6 R C 0)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (S : Scale P C R (residualCost P C R))

def spatialBudget (q : ℕ) (hq : 6 ≤ q) :
    SpatialBudget P (by omega : 6 ≤ (q+1)+1)
      ((input G S.value).atOrder P ((q+1)+1)) (q-4) (S.radius P) where
  Rc := 0
  M := pressureBound
  B := 1
  B0 := 1
  B1 := 1
  A0 := 0
  A2 := 0
  residual := S.value^2*residualCost P C R
  Rc_nonneg := le_rfl
  M_one_le := pressureBound_one_le
  B_nonneg := zero_le_one
  B0_nonneg := zero_le_one
  B1_nonneg := zero_le_one
  A0_nonneg := le_rfl
  A2_nonneg := le_rfl
  residual_pos := mul_pos (sq_pos_of_pos S.positive) (residualCost_pos P C R hR)
  radius_pos := S.radius_positive P hC hR
  inverse_five _ := (identity_pressure P ((q+1)+1) (by omega)).1
  inverse_six _ := (identity_pressure P ((q+1)+1) (by omega)).2
  radius_small _ := by simp only [mul_zero,zero_le_one]
  metric_derivatives _ l hl _ := by
    change EulerH6Pressure.coefficientBlock P
      (jet P (ContinuousLinearMap.id ℝ Space) ((q+1)+1)) 6 l ≤ 0^l*(l.factorial : ℝ)^2
    rw [jet_positive_coefficientBlock P _ _ _ l (by omega)]
    positivity
  metric_base _ r _ := identity_base P ((q+1)+1) r
  background t := by
    have h := (scaled_word G hG S.value S.positive.le).toFieldTower_weightedNorm_le_two
      hR (mul_nonneg S.positive.le hC) (((q+1)+1)+1) (q-4) (by omega)
      (S.radius P t) (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t
    exact h.trans (by simpa only [mul_assoc] using S.background)
  background_derivative t := by
    have h := (scaled_word G hG S.value S.positive.le).toFieldTower_weightedDerivativeNorm_le_twelve
      hR (mul_nonneg S.positive.le hC) ((q+1)+1) (q-4) (by omega)
      (S.radius P t) (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t
    exact h.trans (by simpa only [mul_assoc] using S.derivative)
  linear _ := (jet_zero_weightedCoefficient P _ _ _ _).le
  quadratic _ := by
    change (∑ _i : Fin 3, weightedCoefficient P (jet P (0 : Space →L[ℝ] Space) ((q+1)+1))
      6 (q-4) _) ≤ 0
    simp only [jet_zero_weightedCoefficient,Finset.sum_const_zero,le_refl]
  residual_bound t := residual_weighted G hG hC hR S.value S.positive.le
    ((q+1)+1) (q-4) (by omega) (S.radius P t)
    (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t

def driftBudget (q : ℕ) (hq : 6 ≤ q) :
    EulerDriftCorrectionBudget.Budget P (by omega : 6 ≤ (q+1)+1)
      ((input G S.value).atOrder P ((q+1)+1)) (q-4) (S.radius P) where
  full := spatialBudget G hG hC hR S q hq
  drift := 8*S.value*C
  drift_nonneg := by have hv := S.positive; positivity
  drift_bound t := by
    have hh := weightedDriftNorm_velocityMap_le P 6 (q-4) (S.radius P t)
      (S.radius_positive P hC hR t) (velocityComponents 1 (0 : Space))
      (velocityComponents_norm 1 (0 : Space) (by norm_num) (by simp))
      ((G.smul S.value).toFieldTower.realization (((q+1)+1)+1) t)
    have hb := (scaled_word G hG S.value S.positive.le).toFieldTower_weightedNorm_le_two
      hR (mul_nonneg S.positive.le hC) (((q+1)+1)+1) (q-4) (by omega)
      (S.radius P t) (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t
    exact hh.trans ((mul_le_mul_of_nonneg_left hb (by norm_num)).trans_eq (by ring))

theorem driftBudget_growth (q : ℕ) (hq : 6 ≤ q) :
    combinedConstant P (driftBudget G hG hC hR S q hq).full
      ((input G S.value).metricBudget P (by norm_num)
        (metricBudget P (by norm_num) (G.smul S.value).toFieldTower (residual G
          S.value).toFieldTower)
        (q+1)) = growth P := by
  change energyConstant P
    (growthBudgetBase 1 0 0+growthBudgetSlope 1 0*sobolevEmbeddingConstant P 6*1)
    (growthBudgetSlope 1 0*sobolevEmbeddingConstant P 6*metricAmplification 1)
    (1/1) 1 pressureBound 1 1 0 0 1 = growth P
  norm_num [growthBudgetBase,growthBudgetSlope,growth]

def budget (hdiv : ∀ t, G.path t ∈ divergenceFreeSpace P 1 (0 : Space)) :
    EulerAllOrderDriftCorrection.Budget P (by norm_num : (0 : ℝ) < 1) (input G S.value) where
  metric := metricBudget P (by norm_num) (G.smul S.value).toFieldTower (residual G
    S.value).toFieldTower
  radius := S.radius P
  growthCoefficient := growth P
  delta := S.value
  initialRadius := initialRadius R
  spatial := driftBudget G hG hC hR S
  growth_bound q hq := (driftBudget_growth G hG hC hR S q hq).le
  delta_pos := S.positive
  delta_le_one := S.one
  radius_pos := initialRadius_pos R hR
  decay _ _ := by
    change 2*growth P*(8*S.value*C+S.value)*1 ≤ initialRadius R/2
    simpa only [mul_one] using S.shrink
  scale _ _ := by
    change initialRadius R*0 ≤ 1
    simp only [mul_zero,zero_le_one]
  small _ _ := by
    change 2*(S.value^2*residualCost P C R)*Real.exp (3*growth P*1) ≤ S.value/2
    simpa only [mul_one] using S.residual
  radius_eq _ _ _ := rfl
  divergence t := (divergenceFreeSpace P 1 (0 : Space)).smul_mem S.value (hdiv t)

/-- No scalar guard is required of the input: the amplitude is explicitly
chosen from its finite actual Gevrey constants. -/
def smallBudget (hdiv : ∀ t, G.path t ∈ divergenceFreeSpace P 1 (0 : Space)) :=
  budget G hG hC hR (scale P C R (residualCost P C R) hC hR (residualCost_pos P C R hR)) hdiv

end EulerSmallCorrection
