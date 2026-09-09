/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressureBounds

@[expose] public section

/-! The smaller-radius estimates also retain the actual residual envelope. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerGevreyMetricEstimate EulerSobolevGevreyOperators
  EulerGevreyRadiusReduction EulerGevreyCorrectionSourceBounds

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The quantitative envelope delivered by the actual finite solver. -/
def Budget.residualEnvelope (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q)
    (t : Icc (0 : ℝ) T) : ℝ :=
  2*(B.spatial q hq).full.residual*Real.exp (3*B.growthCoefficient*t.val)

theorem Budget.residualEnvelope_nonneg (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    0 ≤ B.residualEnvelope period q hq t := by
  have h := (B.spatial q hq).full.residual_pos
  unfold Budget.residualEnvelope
  positivity

theorem Budget.residualEnvelope_le_target (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    B.residualEnvelope period q hq t ≤ B.delta/2 := by
  have hg : 0 ≤ 3*B.growthCoefficient := by have := B.growth_pos period; positivity
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 hg)
  exact (mul_le_mul_of_nonneg_left he
    (show 0 ≤ 2*(B.spatial q hq).full.residual by have := (B.spatial q hq).full.residual_pos;
      positivity)).trans
      (B.small q hq)

/-- Both the correction and its genuine first spatial derivatives retain
the quantitative residual bound at the fixed smaller radius. -/
theorem Budget.fieldTower_reducedNorms_residual (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hNq : N+6 ≤ q)
    (s : ℕ) (hs : N+6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period) ((B.fieldTower period).realization s t) ≤
        metricAmplification B.metric.c*B.residualEnvelope period q hq t ∧
    (∑ i : Fin 4, weightedNorm period 6 N (B.reducedRadius period)
        (derivativeOperator period s i ((B.fieldTower period).realization (s+1) t))) ≤
        (8/B.initialRadius)*(metricAmplification B.metric.c*B.residualEnvelope period q hq t) := by
  have hR := (B.spatial q hq).full.radius_pos t
  have hrR : B.reducedRadius period ≤ B.radius t := by
    have h := B.reducedRadius_le_half period t
    linarith
  have hfrac : 4/B.radius t ≤ 8/B.initialRadius := by
    apply (div_le_div_iff₀ hR B.radius_pos).mpr
    linarith [(B.radius_bounds period t).1]
  have hE : 0 ≤ metricAmplification B.metric.c*B.residualEnvelope period q hq t :=
    mul_nonneg (zero_le_one.trans (metricAmplification_one_le B.metric.c_pos))
      (B.residualEnvelope_nonneg period q hq t)
  constructor
  · exact (weightedNorm_mono_radius period 6 N (B.reducedRadius_pos period).le hrR _).trans
      (B.fieldTower_weightedNorm_residual period q hq N (by omega) (by omega) s hs t)
  · calc
      _ ≤ ∑ i : Fin 4, weightedNorm period 6 N (B.radius t/2)
          (derivativeOperator period s i ((B.fieldTower period).realization (s+1) t)) :=
        sum_le_sum fun i _ => weightedNorm_mono_radius period 6 N
          (B.reducedRadius_pos period).le (B.reducedRadius_le_half period t) _
      _ ≤ (4/B.radius t)*weightedNorm period 6 (N+1) (B.radius t)
          ((B.fieldTower period).realization (s+1) t) :=
        weightedNorm_derivative_half period 6 N hs (B.radius t) hR _
      _ ≤ (4/B.radius t)*(metricAmplification B.metric.c*B.residualEnvelope period q hq t) :=
        mul_le_mul_of_nonneg_left
          (B.fieldTower_weightedNorm_residual period q hq (N+1) (by omega) (by omega) (s+1) (by
            omega) t)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac hE

/-- The fixed polynomial cost when the solver's residual envelope is retained. -/
def Budget.residualSourceCost (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) : ℝ :=
  let S := (B.spatial q hq).full
  sourceBound period S.B0 S.B1 S.A0 S.A2 1
    (metricAmplification B.metric.c) ((8/B.initialRadius)*metricAmplification B.metric.c)

private theorem sourceBound_residual (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    let S := (B.spatial q hq).full
    sourceBound period S.B0 S.B1 S.A0 S.A2 S.residual
        (metricAmplification B.metric.c*B.residualEnvelope period q hq t)
        ((8/B.initialRadius)*(metricAmplification B.metric.c*B.residualEnvelope period q hq t)) ≤
      B.residualSourceCost period q hq*B.residualEnvelope period q hq t := by
  have hμ : 0 ≤ metricAmplification B.metric.c := zero_le_one.trans (metricAmplification_one_le
    B.metric.c_pos)
  have hDE := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) B.radius_pos.le) hμ
  have he := B.residualEnvelope_nonneg period q hq t
  have he1 : B.residualEnvelope period q hq t ≤ 1 :=
    (B.residualEnvelope_le_target period q hq t).trans (by have := B.delta_le_one; linarith)
  have hG := (B.growth_pos period).le
  have ht0 := t.property.1
  have hexp : 1 ≤ Real.exp (3*B.growthCoefficient*t.val) := Real.one_le_exp_iff.mpr (by positivity)
  have hr0 := (B.spatial q hq).full.residual_pos.le
  have hr : (B.spatial q hq).full.residual ≤ B.residualEnvelope period q hq t := by
    have hm := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2*(B.spatial q hq).full.residual by
      positivity)
    dsimp [Budget.residualEnvelope]
    linarith
  have h := sourceBound_scaling period (B0 := (B.spatial q hq).full.B0)
    (B1 := (B.spatial q hq).full.B1) (A0 := (B.spatial q hq).full.A0)
    (B.spatial q hq).full.A2_nonneg hμ hDE he he1 hr
  convert h using 1
  · congr 1 <;> ring
  · rfl

/-- The constructed pressure and actual time derivative satisfy the
sharper residual-envelope estimates, without assuming either bound. -/
theorem Budget.pressure_time_reducedNorms_residual (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (N : ℕ) (hNq : N+6 ≤ q)
    (s : ℕ) (hs : N+6 ≤ s) (t : Icc (0 : ℝ) T) :
    weightedNorm period 6 N (B.reducedRadius period) ((B.pressureTower period).realization s t) ≤
        (2*(B.spatial q hq).full.M*B.residualSourceCost period q hq)*B.residualEnvelope period q hq
          t ∧
    weightedNorm period 6 N (B.reducedRadius period) ((B.timeDerivativeTower period).realization s
      t) ≤
        ((1+2*(B.spatial q hq).full.M*(448*(B.spatial q hq).full.B+1))*
          B.residualSourceCost period q hq)*B.residualEnvelope period q hq t := by
  have hrR : B.reducedRadius period ≤ B.radius t := by
    have h := B.reducedRadius_le_half period t
    have hp := (B.spatial q hq).full.radius_pos t
    linarith
  have he := (B.fieldTower_reducedNorms_residual period q hq N hNq (q+3) (by omega) t).1
  have hde := (B.fieldTower_reducedNorms_residual period q hq N hNq (q+2) (by omega) t).2
  have hcost := sourceBound_residual period B q hq t
  have hM := zero_le_one.trans (B.spatial q hq).full.M_one_le
  have hB := (B.spatial q hq).full.B_nonneg
  have hp := pressure_smallerRadius_bound period (B.spatial q hq).full N (by omega) (by omega)
    t (B.reducedRadius period) (B.reducedRadius_pos period) hrR _ _ _ he hde
  have ht := timeSource_smallerRadius_bound period (B.spatial q hq).full N (by omega) (by omega)
    t (B.reducedRadius period) (B.reducedRadius_pos period) hrR _ _ _ he hde
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hcost (by positivity : 0 ≤ 2*(B.spatial q
    hq).full.M))
  have ht' := ht.trans (mul_le_mul_of_nonneg_left hcost
    (by positivity : 0 ≤ 1+2*(B.spatial q hq).full.M*(448*(B.spatial q hq).full.B+1)))
  change weightedNorm period 6 N (B.reducedRadius period)
    ((A.atOrder period (q+2)).pressure period (by omega) t
      ((B.fieldTower period).realization (q+3) t)) ≤ _ at hp'
  rw [← B.solution_eq_realization period (q+2) (by omega), B.pressure_eq_realization] at hp'
  change weightedNorm period 6 N (B.reducedRadius period)
    (((A.atOrder period (q+2)).coefficients period (by omega)).apply t
      ((B.fieldTower period).realization (q+3) t)) ≤ _ at ht'
  rw [B.source_eq_timeDerivativeTower period (q+2) (by omega)] at ht'
  constructor
  · rw [weightedNorm_unique period 6 N (B.reducedRadius period) _
      ((B.pressureTower period).realization (q+2) t)
      (by rw [(B.pressureTower period).value_eq, (B.pressureTower period).value_eq]) hs (by omega)]
    exact hp'.trans_eq (by ring)
  · rw [weightedNorm_unique period 6 N (B.reducedRadius period) _
      ((B.timeDerivativeTower period).realization (q+2) t)
      (by rw [(B.timeDerivativeTower period).value_eq, (B.timeDerivativeTower period).value_eq]) hs
        (by omega)]
    exact ht'.trans_eq (by ring)

end EulerAllOrderDriftCorrection
