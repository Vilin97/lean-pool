/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftRadiusBounds
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblySourceTower
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSourceBounds
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressure
import LeanPool.NavierStokesAndEuler.Euler.GevreyRadiusReduction
import Mathlib.Algebra.Order.Star.Real

/-! Smaller-radius quantitative bounds for the constructed common pressure
and the actual first time derivative of the correction. -/

@[expose] public section


noncomputable section

namespace EulerGevreyCorrectionSourceBounds

open EulerH6Nonlinear

variable (period : ℝ) [Fact (0 < period)]

/-- Scaling a small error and its first derivatives leaves a linear
smallness factor in the actual quadratic source bound. -/
theorem sourceBound_scaling {B0 B1 A0 A2 residual E DE δ : ℝ}
    (hA2 : 0 ≤ A2) (hE : 0 ≤ E) (hDE : 0 ≤ DE)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : residual ≤ δ) :
    sourceBound period B0 B1 A0 A2 residual (δ*E) (δ*DE) ≤
      sourceBound period B0 B1 A0 A2 1 E DE*δ := by
  have hP := productConstant_nonneg period 3
  have hquad : 0 ≤ productConstant period 3*E*DE + A2*productConstant period 3*E^2 := by positivity
  have hsq : δ^2 ≤ δ := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq hquad
  unfold sourceBound
  nlinarith only [hr, hm]

end EulerGevreyCorrectionSourceBounds

namespace EulerAllOrderDriftCorrection

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerGevreyMetricEstimate EulerSobolevGevreyOperators
  EulerGevreyRadiusReduction EulerGevreyCorrectionSourceBounds

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The explicit raw-source bound before using the target-error smallness. -/
def Budget.sourceSize (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) : ℝ :=
  let S := (B.spatial q hq).full
  sourceBound period S.B0 S.B1 S.A0 S.A2 S.residual
    (B.correctionSize period) ((8/B.initialRadius)*B.correctionSize period)

/-- The factor in the correction bound after removing the common delta. -/
def Budget.baseCorrectionSize (B : Budget period hT A) : ℝ := metricAmplification B.metric.c/2

/-- An explicit source constant involving only the prescribed norm budgets
and the reciprocal initial radius; it is independent of delta. -/
def Budget.sourceCost (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) : ℝ :=
  let S := (B.spatial q hq).full
  sourceBound period S.B0 S.B1 S.A0 S.A2 1
    (B.baseCorrectionSize period) ((8/B.initialRadius)*B.baseCorrectionSize period)

/-- Pressure cost, given by `2*(B.spatial q hq).full.M*B.sourceCost period q hq`. -/
def Budget.pressureCost (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) : ℝ :=
  2*(B.spatial q hq).full.M*B.sourceCost period q hq

/-- Time derivative cost, given by `(1+2*(B.spatial q hq).full.M*(448*(B.spatial q
hq).full.B+1))*B.sourceCost period q hq`. -/
def Budget.timeDerivativeCost (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) : ℝ :=
  (1+2*(B.spatial q hq).full.M*(448*(B.spatial q hq).full.B+1))*B.sourceCost period q hq

theorem Budget.baseCorrectionSize_nonneg (B : Budget period hT A) :
    0 ≤ B.baseCorrectionSize period := by
  exact div_nonneg (zero_le_one.trans (metricAmplification_one_le B.metric.c_pos)) (by norm_num)

theorem Budget.sourceSize_le_delta (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) :
    B.sourceSize period q hq ≤ B.sourceCost period q hq*B.delta := by
  have hr : (B.spatial q hq).full.residual ≤ B.delta :=
    (B.residual_le_delta period q hq).trans (by have := B.delta_pos; linarith)
  have hE := B.baseCorrectionSize_nonneg period
  have hDE : 0 ≤ (8/B.initialRadius)*B.baseCorrectionSize period :=
    mul_nonneg (div_nonneg (by norm_num) B.radius_pos.le) hE
  have h := sourceBound_scaling period (B0 := (B.spatial q hq).full.B0)
    (B1 := (B.spatial q hq).full.B1) (A0 := (B.spatial q hq).full.A0)
    (B.spatial q hq).full.A2_nonneg hE hDE
    B.delta_pos.le B.delta_le_one hr
  convert h using 1
  · dsimp [Budget.sourceSize, Budget.correctionSize, Budget.baseCorrectionSize]
    congr 1 <;> ring
  · rfl

theorem Budget.sourceCost_nonneg (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) :
    0 ≤ B.sourceCost period q hq := by
  exact sourceBound_nonneg period (B.spatial q hq).full.B0_nonneg (B.spatial q hq).full.B1_nonneg
    (B.spatial q hq).full.A0_nonneg (B.spatial q hq).full.A2_nonneg (by norm_num)
    (B.baseCorrectionSize_nonneg period)
    (mul_nonneg (div_nonneg (by norm_num) B.radius_pos.le) (B.baseCorrectionSize_nonneg period))

private theorem tower_weightedNorm_eq (F : FieldTower period T) (s u N : ℕ)
    (hs : N + 6 ≤ s) (hu : N + 6 ≤ u) (r : ℝ) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N r (F.realization s t) =
      weightedNorm period 6 N r (F.realization u t) := by
  apply weightedNorm_unique period 6 N r _ _ _ hs hu
  rw [F.value_eq, F.value_eq]

/-- The common raw source is bounded at the fixed smaller radius, using
only the actual correction and derivative bounds already proved. -/
theorem Budget.rawSourceTower_reducedNorm (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hNq : N + 4 ≤ q)
    (s : ℕ) (hs : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period) ((B.rawSourceTower period).realization s t) ≤
      B.sourceSize period q hq := by
  have hrR : B.reducedRadius period ≤ B.radius t := by
    have h := B.reducedRadius_le_half period t
    have hp := (B.spatial q hq).full.radius_pos t
    linarith
  have h := rawSource_smallerRadius_bound period (B.spatial q hq).full N (by omega) (by omega)
    t (B.reducedRadius period) (B.reducedRadius_pos period) hrR
    (B.correctionSize period) ((8/B.initialRadius)*B.correctionSize period)
    ((B.fieldTower period).realization (q+3) t)
    (B.fieldTower_reducedNorm period (q+3) N (by omega) t)
    (B.fieldTower_reducedDerivativeNorm period (q+2) N (by omega) t)
  change weightedNorm period 6 N (B.reducedRadius period)
    ((A.atOrder period (q+2)).rawSource period (by omega) t
      ((B.fieldTower period).realization (q+3) t)) ≤ B.sourceSize period q hq at h
  rw [B.rawSource_eq_realization period (q+2) (by omega)] at h
  rw [tower_weightedNorm_eq period (B.rawSourceTower period) s (q+2) N hs (by omega)]
  exact h

/-- The pressure is the actual common signed pressure obtained from the
coercive elliptic inverse, with an explicit smaller-radius bound. -/
theorem Budget.pressureTower_reducedNorm (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hNq : N + 4 ≤ q)
    (s : ℕ) (hs : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period) ((B.pressureTower period).realization s t) ≤
      2*(B.spatial q hq).full.M*B.sourceSize period q hq := by
  have hrR : B.reducedRadius period ≤ B.radius t := by
    have h := B.reducedRadius_le_half period t
    have hp := (B.spatial q hq).full.radius_pos t
    linarith
  have h := pressure_smallerRadius_bound period (B.spatial q hq).full N (by omega) (by omega)
    t (B.reducedRadius period) (B.reducedRadius_pos period) hrR
    (B.correctionSize period) ((8/B.initialRadius)*B.correctionSize period)
    ((B.fieldTower period).realization (q+3) t)
    (B.fieldTower_reducedNorm period (q+3) N (by omega) t)
    (B.fieldTower_reducedDerivativeNorm period (q+2) N (by omega) t)
  change weightedNorm period 6 N (B.reducedRadius period)
    ((A.atOrder period (q+2)).pressure period (by omega) t
      ((B.fieldTower period).realization (q+3) t)) ≤
        2*(B.spatial q hq).full.M*B.sourceSize period q hq at h
  rw [← B.solution_eq_realization period (q+2) (by omega), B.pressure_eq_realization] at h
  rw [tower_weightedNorm_eq period (B.pressureTower period) s (q+2) N hs (by omega)]
  exact h

/-- The actual continuous time-derivative field has the bound obtained
from its literal raw-source and signed-pressure equation. -/
theorem Budget.timeDerivativeTower_reducedNorm (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hNq : N + 4 ≤ q)
    (s : ℕ) (hs : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period) ((B.timeDerivativeTower period).realization s
        t) ≤
      (1+2*(B.spatial q hq).full.M*(448*(B.spatial q hq).full.B+1))*B.sourceSize period q hq := by
  have hrR : B.reducedRadius period ≤ B.radius t := by
    have h := B.reducedRadius_le_half period t
    have hp := (B.spatial q hq).full.radius_pos t
    linarith
  have h := timeSource_smallerRadius_bound period (B.spatial q hq).full N (by omega) (by omega)
    t (B.reducedRadius period) (B.reducedRadius_pos period) hrR
    (B.correctionSize period) ((8/B.initialRadius)*B.correctionSize period)
    ((B.fieldTower period).realization (q+3) t)
    (B.fieldTower_reducedNorm period (q+3) N (by omega) t)
    (B.fieldTower_reducedDerivativeNorm period (q+2) N (by omega) t)
  change weightedNorm period 6 N (B.reducedRadius period)
    (((A.atOrder period (q+2)).coefficients period (by omega)).apply t
      ((B.fieldTower period).realization (q+3) t)) ≤
        (1+2*(B.spatial q hq).full.M*(448*(B.spatial q hq).full.B+1))*B.sourceSize period q hq at h
  rw [B.source_eq_timeDerivativeTower period (q+2) (by omega)] at h
  rw [tower_weightedNorm_eq period (B.timeDerivativeTower period) s (q+2) N hs (by omega)]
  exact h

/-- The actual pressure-gradient norm is linear in the target error. -/
theorem Budget.pressureTower_reducedNorm_delta (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hNq : N + 4 ≤ q)
    (s : ℕ) (hs : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period) ((B.pressureTower period).realization s t) ≤
      B.pressureCost period q hq*B.delta := by
  have hM := zero_le_one.trans (B.spatial q hq).full.M_one_le
  exact (B.pressureTower_reducedNorm period q hq N hNq s hs t).trans
    ((mul_le_mul_of_nonneg_left (B.sourceSize_le_delta period q hq) (by positivity)).trans_eq
      (by unfold Budget.pressureCost; ring))

/-- The actual first time derivative has the same linear target-error
factor, at the same fixed radius and every finite external cutoff. -/
theorem Budget.timeDerivativeTower_reducedNorm_delta (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hNq : N + 4 ≤ q)
    (s : ℕ) (hs : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period) ((B.timeDerivativeTower period).realization s
        t) ≤
      B.timeDerivativeCost period q hq*B.delta := by
  have hM := zero_le_one.trans (B.spatial q hq).full.M_one_le
  have hB := (B.spatial q hq).full.B_nonneg
  exact (B.timeDerivativeTower_reducedNorm period q hq N hNq s hs t).trans
    ((mul_le_mul_of_nonneg_left (B.sourceSize_le_delta period q hq) (by positivity)).trans_eq
      (by unfold Budget.timeDerivativeCost; ring))

end EulerAllOrderDriftCorrection
