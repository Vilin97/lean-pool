/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.GevreyStabilityBudget

/-! One concrete stability budget compares every finite realization of the same prescribed data. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionBudget

open MeasureTheory Set EulerLiftedGradientSpace EulerLiftedPressure EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerAllOrderCorrectionData
  EulerCorrectionStabilityBudget EulerGevreyStabilityBudget

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine base-order data bounds construct the comparison budget at every Sobolev order of the
coherent coefficient family. -/
def stabilityBudget {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A) (q : ℕ) :
    StabilityBudget period hT.le (A.atOrder period q) where
  metric := B.metric.metric
  continuous := B.metric.continuous
  derivative := B.metric.derivative
  hasDeriv := B.metric.hasDeriv
  c := B.metric.c
  c_pos := B.metric.c_pos
  symmetric := B.metric.symmetric
  coercive := B.metric.coercive
  inverse := B.metric.inverse
  bound := B.metric.bound
  first := B.metric.first
  time := B.metric.time
  linear := (B.spatial 6 le_rfl).A0
  quadratic := (B.spatial 6 le_rfl).A2
  bound_le t := (coefficientOperator_norm_le (B.metric.metric t).coefficient
    (B.metric.metric t).measurable (B.metric.metric t).bound (B.metric.metric t).norm_bound).trans
      (B.metric.bound_le t)
  first_le := B.metric.first_le
  time_le := B.metric.time_le
  linear_le t := (coefficient_bound_le_weighted period (A.linear.jet 8 t) 2 (B.radius t)
    ((B.spatial 6 le_rfl).radius_pos t)).trans ((B.spatial 6 le_rfl).linear t)
  quadratic_le t := (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    coefficient_bound_le_weighted period ((A.quadratic i).jet 8 t) 2 (B.radius t)
      ((B.spatial 6 le_rfl).radius_pos t))).trans ((B.spatial 6 le_rfl).quadratic t)

end EulerAllOrderCorrectionBudget
