/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ViscosityCauchy
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData

@[expose] public section

/-! The already-proved Gevrey budgets supply every actual vanishing-viscosity stability budget. -/

noncomputable section

namespace EulerGevreyStabilityBudget

open MeasureTheory Set EulerLiftedGradientSpace EulerLiftedPressure EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerJetProductBounds EulerH6Pressure
  EulerSobolevGevreyOperators EulerPacketWeights EulerSobolevCoefficientPressure
  EulerCorrectionOperators EulerCorrectionLowerData EulerCorrectionEnergyData
    EulerCorrectionStabilityBudget
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- The actual uniform coefficient bound is contained in its fixed H6 coefficient block. -/
theorem coefficient_bound_le_block {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A) :
    (A.bound : ℝ) ≤ coefficientBlock period K 6 0 := by
  have hsum : 0 ≤ ∑ r ∈ Finset.range 7, boundLevel period K r :=
    Finset.sum_nonneg (fun r _ => boundLevel_nonneg K)
  have hsingle : boundLevel period K 0 ≤ ∑ r ∈ Finset.range 7, boundLevel period K r :=
    Finset.single_le_sum (f := fun r => boundLevel period K r) (fun r _ => boundLevel_nonneg K) (by
      norm_num : 0 ∈ Finset.range 7)
  have hzero : boundLevel period K 0 = (A.bound : ℝ) := by cases K <;> simp only [boundLevel]
  rw [hzero] at hsingle
  unfold coefficientBlock
  norm_num only [Nat.reduceAdd,zero_add,pow_succ,pow_zero,one_mul]
  nlinarith only [hsum,hsingle]

omit [Fact (0 < period)] in
/-- The actual uniform coefficient bound is contained in every positive-radius truncated Gevrey coefficient sum. -/
theorem coefficient_bound_le_weighted {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (A.bound : ℝ) ≤ weightedCoefficient period K 6 N ρ := by
  have hsingle : weight ρ 0*coefficientBlock period K 6 0 ≤ weightedCoefficient period K 6 N ρ :=
    Finset.single_le_sum (f := fun n => weight ρ n*coefficientBlock period K 6 n)
      (fun n _ => mul_nonneg (weight_pos hρ n).le (coefficientBlock_nonneg K))
      (by simp : 0 ∈ Finset.range (N+1))
  norm_num only [weight,pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,div_one,one_mul] at hsingle
  exact (coefficient_bound_le_block period K).trans hsingle

/-- The concrete global Gevrey and metric budgets directly construct the viscosity comparison budget on the genuine lower equation. -/
def stabilityBudgetLower {q : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, EulerSpatialSobolevInverse.CoefficientJet period standardDirection q
      (D.metric.coefficient t))
    (KL : ∀ t, EulerSpatialSobolevInverse.CoefficientJet period standardDirection q
      (D.linear.coefficient t))
    (KQ : ∀ i t, EulerSpatialSobolevInverse.CoefficientJet period standardDirection q ((D.quadratic
      i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (N : ℕ) (R : C(Icc (0 : ℝ) T,ℝ)) (hq : 6 ≤ q+1)
    (B : SpatialBudget period hq D N R) (K : MetricBudget period T hT D) :
    StabilityBudget period hT (lowerData period D KG KL KQ hG hL hQ) where
  metric := K.metric
  continuous := K.continuous
  derivative := K.derivative
  hasDeriv := K.hasDeriv
  c := K.c
  c_pos := K.c_pos
  symmetric := K.symmetric
  coercive := K.coercive
  inverse := K.inverse
  bound := K.bound
  first := K.first
  time := K.time
  linear := B.A0
  quadratic := B.A2
  bound_le t := (coefficientOperator_norm_le (K.metric t).coefficient (K.metric t).measurable
    (K.metric t).bound (K.metric t).norm_bound).trans (K.bound_le t)
  first_le := K.first_le
  time_le := K.time_le
  linear_le t := (coefficient_bound_le_weighted period (D.linear.jet t) N (R t) (B.radius_pos
    t)).trans (B.linear t)
  quadratic_le t := (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    coefficient_bound_le_weighted period ((D.quadratic i).jet t) N (R t) (B.radius_pos t))).trans
      (B.quadratic t)

end EulerGevreyStabilityBudget
