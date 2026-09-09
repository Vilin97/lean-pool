/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerCorrection
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressureBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolevBudget

/-! Explicit bounds for the constructed small-data solution. All constants
are functions of the datum's supplied Gevrey bounds and the fixed period;
none depends on which datum realizes those bounds. -/

@[expose] public section


noncomputable section

namespace EulerStaticEuler

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpTranslation
  EulerAllOrderDriftCorrection EulerAllOrderCorrectionData EulerSobolevGevreyOperators
  EulerGevreyCorrectionSourceBounds EulerGevreyMetricEstimate EulerConstantCorrection

/-- A fixed positive radius retained by the actual correction. -/
def retainedRadius (R : ℝ) : ℝ := EulerSmallCorrection.initialRadius (mixedRadius R)/4

/-- Base error factor, given by `metricAmplification 1/2`. -/
def baseErrorFactor : ℝ := metricAmplification 1/2

theorem retainedRadius_pos (R : ℝ) (hR : 0 ≤ R) : 0 < retainedRadius R :=
  div_pos (EulerSmallCorrection.initialRadius_pos _ (mixedRadius_nonneg R hR)) (by norm_num)

theorem retainedRadius_small (R : ℝ) (hR : 0 ≤ R) :
    retainedRadius R*mixedRadius R ≤ 1/2 := by
  have h := EulerSmallCorrection.initialRadius_mul _ (mixedRadius_nonneg R hR)
  have hn := mul_nonneg (EulerSmallCorrection.initialRadius_pos _ (mixedRadius_nonneg R hR)).le
    (mixedRadius_nonneg R hR)
  dsimp [retainedRadius]
  nlinarith

theorem baseErrorFactor_nonneg : 0 ≤ baseErrorFactor :=
  div_nonneg (zero_le_one.trans (metricAmplification_one_le (by
      norm_num : (0 : ℝ) < 1))) (by norm_num)

variable (P : ℝ) [Fact (0 < P)]

/-- Static source cost, given by `sourceBound P 1 1 0 0 1 baseErrorFactor
((8/EulerSmallCorrection.initialRadius (mixedRadius R))*baseErrorFactor)`. -/
def staticSourceCost (R : ℝ) : ℝ :=
  sourceBound P 1 1 0 0 1 baseErrorFactor
    ((8/EulerSmallCorrection.initialRadius (mixedRadius R))*baseErrorFactor)

/-- Static time cost, given by `(1+2*pressureBound*(448*1+1))*staticSourceCost P R`. -/
def staticTimeCost (R : ℝ) : ℝ := (1+2*pressureBound*(448*1+1))*staticSourceCost P R

/-- Static pressure cost, given by `2*pressureBound*staticSourceCost P R`. -/
def staticPressureCost (R : ℝ) : ℝ := 2*pressureBound*staticSourceCost P R

theorem staticSourceCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ staticSourceCost P R :=
  sourceBound_nonneg P zero_le_one zero_le_one le_rfl le_rfl zero_le_one baseErrorFactor_nonneg
    (mul_nonneg (div_nonneg (by norm_num)
      (EulerSmallCorrection.initialRadius_pos _ (mixedRadius_nonneg R hR)).le)
          baseErrorFactor_nonneg)

theorem staticTimeCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ staticTimeCost P R := by
  have hS := staticSourceCost_nonneg P R hR
  have hP := zero_le_one.trans pressureBound_one_le
  unfold staticTimeCost
  positivity

theorem staticPressureCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ staticPressureCost P R := by
  have hS := staticSourceCost_nonneg P R hR
  have hP := zero_le_one.trans pressureBound_one_le
  unfold staticPressureCost
  positivity

variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)

theorem budget_retainedRadius :
    (correctionBudget P u C R hC hR hu hdiv).reducedRadius P=retainedRadius R := rfl

theorem budget_staticTimeCost (q : ℕ) (hq : 6 ≤ q) :
    (correctionBudget P u C R hC hR hu hdiv).timeDerivativeCost P q hq=staticTimeCost P R := rfl

theorem budget_staticPressureCost (q : ℕ) (hq : 6 ≤ q) :
    (correctionBudget P u C R hC hR hu hdiv).pressureCost P q hq=staticPressureCost P R := rfl

theorem correction_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      (((correctionBudget P u C R hC hR hu hdiv).fieldTower P).realization (n+6) t) ≤
      amplitude P C R hC hR*baseErrorFactor := by
  have h := (correctionBudget P u C R hC hR hu hdiv).fieldTower_reducedNorm P (n+6) n le_rfl t
  change _ ≤ metricAmplification 1*(amplitude P C R hC hR/2) at h
  exact h.trans_eq (by unfold baseErrorFactor; ring)

theorem exact_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      ((exactPacket P u C R hC hR hu hdiv).velocity.realization (n+6) t) ≤
      amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor) := by
  have hw := EulerSmallCorrection.scaled_word (EulerStaticCylinder.field P 1 u)
    (EulerStaticCylinder.field_wordBound P 1 u 6 C R hC hR hu)
    (amplitude P C R hC hR) (amplitude_pos P C R hC hR).le
  have hb := hw.toFieldTower_weightedNorm_le_two (mixedRadius_nonneg R hR)
    (mul_nonneg (amplitude_pos P C R hC hR).le (mixedAmplitude_nonneg P C R hC hR))
    (n+6) n le_rfl (retainedRadius R) (retainedRadius_pos R hR) (retainedRadius_small R hR) t
  change weightedNorm P 6 n (retainedRadius R)
    (((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)).toFieldTower.realization
        (n+6) t +
      ((correctionBudget P u C R hC hR hu hdiv).fieldTower P).realization (n+6) t) ≤ _
  apply (weightedNorm_add_le P 6 n le_rfl (retainedRadius R) (retainedRadius_pos R hR) _ _).trans
  exact (add_le_add hb (correction_weighted P u C R hC hR hu hdiv n t)).trans_eq (by
      unfold mixedAmplitude; ring)

theorem time_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      (((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower P).realization (n+6) t) ≤
      amplitude P C R hC hR*staticTimeCost P R := by
  have h := (correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower_reducedNorm_delta
    P (n+6) (by omega) n (by omega) (n+6) le_rfl t
  rw [budget_retainedRadius,budget_staticTimeCost] at h
  exact h.trans_eq (mul_comm _ _)

theorem pressure_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      (((correctionBudget P u C R hC hR hu hdiv).pressureTower P).realization (n+6) t) ≤
      amplitude P C R hC hR*staticPressureCost P R := by
  have h := (correctionBudget P u C R hC hR hu hdiv).pressureTower_reducedNorm_delta
    P (n+6) (by omega) n (by omega) (n+6) le_rfl t
  rw [budget_retainedRadius,budget_staticPressureCost] at h
  exact h.trans_eq (mul_comm _ _)

end EulerStaticEuler
