/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftCorrection
import LeanPool.NavierStokesAndEuler.Euler.GevreyRadiusReduction

/-! Actual weighted correction and derivative bounds at a fixed positive radius. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderDriftCorrection

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerAllOrderCorrectionData EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerGevreyMetricEstimate EulerGevreyRadiusReduction EulerSobolevGevreyOperators

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The fixed radius retained for the correction, its pressure, and its time derivative. -/
def Budget.reducedRadius (B : Budget period hT A) : ℝ := B.initialRadius/4

/-- The actual target-error envelope converted from metric energy to the fixed H⁶ word norm. -/
def Budget.correctionSize (B : Budget period hT A) : ℝ :=
  metricAmplification B.metric.c*(B.delta/2)

theorem Budget.growth_pos (B : Budget period hT A) : 0 < B.growthCoefficient :=
  (combinedConstant_pos period (B.spatial 6 le_rfl).full
    (A.metricBudget period hT.le B.metric 7)).trans_le (B.growth_bound 6 le_rfl)

theorem Budget.radius_bounds (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    B.initialRadius/2 ≤ B.radius t ∧ B.radius t ≤ B.initialRadius := by
  have hG := (B.growth_pos period).le
  have hd := (B.spatial 6 le_rfl).drift_nonneg
  have hδ := B.delta_pos.le
  have hs : 0 ≤ 2*B.growthCoefficient*((B.spatial 6 le_rfl).drift+B.delta) := by positivity
  have ht := mul_le_mul_of_nonneg_left t.property.2 hs
  have hzero := mul_nonneg hs t.property.1
  rw [B.radius_eq 6 le_rfl t]
  constructor <;> linarith [B.decay 6 le_rfl]

theorem Budget.reducedRadius_pos (B : Budget period hT A) : 0 < B.reducedRadius period := by
  exact div_pos B.radius_pos (by norm_num)

theorem Budget.reducedRadius_le_half (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    B.reducedRadius period ≤ B.radius t/2 := by
  have h := (B.radius_bounds period t).1
  dsimp [Budget.reducedRadius]
  linarith

theorem Budget.correctionSize_nonneg (B : Budget period hT A) : 0 ≤ B.correctionSize period := by
  have hμ := metricAmplification_one_le B.metric.c_pos
  have hδ := B.delta_pos.le
  dsimp [Budget.correctionSize]
  positivity

/-- The actual common correction retains the quantitative residual energy
of any finite realization containing the requested words. -/
theorem Budget.fieldTower_weightedNorm_residual (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hN : N ≤ q - 4) (hNq : N + 6 ≤ q + 1)
    (s : ℕ) (hs : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.radius t) ((B.fieldTower period).realization s t) ≤
      metricAmplification B.metric.c *
        (2*(B.spatial q hq).full.residual*Real.exp (3*B.growthCoefficient*t.val)) := by
  have hv : value period ((B.fieldTower period).realization s t) =
      value period (B.solution period q hq t) := by
    rw [(B.fieldTower period).value_eq]
    exact (B.solution_value_common period q hq t).symm
  rw [weightedNorm_unique period 6 N (B.radius t) _ _ hv hs hNq]
  have h := weightedNorm_le_energy period N hNq (B.radius t)
    ((B.spatial q hq).full.radius_pos t) (B.metric.operatorPath period t)
    (B.solution period q hq t) B.metric.c B.metric.c_pos (B.metric.operator_coercive period t)
  exact h.trans (mul_le_mul_of_nonneg_left (B.solution_energy period q hq N hN hNq t).1
    (zero_le_one.trans (metricAmplification_one_le B.metric.c_pos)))

/-- At every finite cutoff, the norm bounds the one constructed common field. -/
theorem Budget.fieldTower_weightedNorm_delta (B : Budget period hT A)
    (s N : ℕ) (hN : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.radius t) ((B.fieldTower period).realization s t) ≤
      B.correctionSize period := by
  have hv : value period ((B.fieldTower period).realization s t) =
      value period (B.solution period (N+6) (by omega) t) := by
    rw [(B.fieldTower period).value_eq]
    exact (B.solution_value_common period (N+6) (by omega) t).symm
  rw [weightedNorm_unique period 6 N (B.radius t) _ _ hv hN (by omega)]
  have h := weightedNorm_le_energy period N (by omega : N+6 ≤ (N+6)+1) (B.radius t)
    ((B.spatial (N+6) (by omega)).full.radius_pos t) (B.metric.operatorPath period t)
    (B.solution period (N+6) (by omega) t) B.metric.c B.metric.c_pos
    (B.metric.operator_coercive period t)
  exact h.trans (mul_le_mul_of_nonneg_left
    (B.solution_energy period (N+6) (by omega) N (by omega) (by omega) t).2
    (zero_le_one.trans (metricAmplification_one_le B.metric.c_pos)))

/-- The correction estimate holds at the same fixed quarter of the initial
radius for the whole time interval. -/
theorem Budget.fieldTower_reducedNorm (B : Budget period hT A)
    (s N : ℕ) (hN : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period)
      ((B.fieldTower period).realization s t) ≤ B.correctionSize period := by
  have hr : B.reducedRadius period ≤ B.radius t := by
    have hh := B.reducedRadius_le_half period t
    have hp := (B.spatial 6 le_rfl).full.radius_pos t
    linarith
  exact (weightedNorm_mono_radius period 6 N (B.reducedRadius_pos period).le hr _).trans
    (B.fieldTower_weightedNorm_delta period s N hN t)

/-- One extra derivative costs only the fixed reciprocal initial radius.
The estimate is simultaneous in all four genuine coordinate derivatives. -/
theorem Budget.fieldTower_reducedDerivativeNorm (B : Budget period hT A)
    (s N : ℕ) (hN : N + 6 ≤ s) (t : Icc (0 : ℝ) T) :
    (∑ i : Fin 4, weightedNorm period 6 N (B.reducedRadius period)
      (derivativeOperator period s i ((B.fieldTower period).realization (s+1) t))) ≤
      (8/B.initialRadius)*B.correctionSize period := by
  have hR := (B.spatial 6 le_rfl).full.radius_pos t
  have hfrac : 4/B.radius t ≤ 8/B.initialRadius := by
    apply (div_le_div_iff₀ hR B.radius_pos).mpr
    linarith [(B.radius_bounds period t).1]
  calc
    _ ≤ ∑ i : Fin 4, weightedNorm period 6 N (B.radius t/2)
        (derivativeOperator period s i ((B.fieldTower period).realization (s+1) t)) := by
      exact sum_le_sum fun i _ => weightedNorm_mono_radius period 6 N
        (B.reducedRadius_pos period).le (B.reducedRadius_le_half period t) _
    _ ≤ (4/B.radius t)*weightedNorm period 6 (N+1) (B.radius t)
        ((B.fieldTower period).realization (s+1) t) :=
      weightedNorm_derivative_half period 6 N hN (B.radius t) hR _
    _ ≤ (4/B.radius t)*B.correctionSize period :=
      mul_le_mul_of_nonneg_left (B.fieldTower_weightedNorm_delta period (s+1) (N+1) (by omega) t)
        (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hfrac (B.correctionSize_nonneg period)

/-- The scalar residual budget itself is small; this follows from the
actual bootstrap input and does not assume a pressure estimate. -/
theorem Budget.residual_le_delta (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) :
    (B.spatial q hq).full.residual ≤ B.delta/4 := by
  have he : 1 ≤ Real.exp (3*B.growthCoefficient*T) :=
    Real.one_le_exp_iff.mpr (by have hG := (B.growth_pos period).le; positivity)
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 2*(B.spatial q hq).full.residual by
        have := (B.spatial q hq).full.residual_pos; positivity)
  have hs := B.small q hq
  linarith

end EulerAllOrderDriftCorrection
