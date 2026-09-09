/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DriftEnergyMajorants
import LeanPool.NavierStokesAndEuler.Euler.DriftMetricForcing

/-! The actual time-dependent correction forcing obeys the sharp drift majorant. -/

@[expose] public section


noncomputable section

namespace EulerDriftCorrectionEnergyBound

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerCorrectionOperators
  EulerCorrectionEnergyTime EulerEnergyMetricPaths EulerGevreyMetricEstimate
  EulerH6Pressure EulerSobolevGevreyOperators EulerSobolevTransportCommutator
  EulerSobolevTransport EulerH6Nonlinear EulerGevreyMetricComparison EulerTimeLp
  EulerVolterraConvolution EulerSobolevWordValueIdentity EulerRegularizedTopBlocks
  EulerGevreyOrderZero EulerTimeCorrectionSource EulerWeightedCylinderEnergy
  EulerCorrectionEnergyData EulerDriftCorrectionBudget EulerDriftEnergyMajorants
  EulerFunctionalVelocity EulerSobolevDriftNorm
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual correction array is controlled by the continuous drift majorant,
independently of its auxiliary higher-Sobolev representative. -/
theorem correctionArray_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (V : SobolevSpace period ((q + 1) + 1)) (τ : Icc (0 : ℝ) T)
    (hV : truncateOperator period (q + 1) V = e τ) :
    weightedForcingSum (R τ) (fun I : ExternalWord N => I.1.val)
      (correctionArray period hq D (baseMetricJet period hq D) N hN e V τ) ≤
        forcingMajorant period S hN K e τ := by
  have h := EulerDriftMetricForcing.correctionForcing_metric period hq
    (D.metric.jet τ) (baseMetricJet period hq D τ)
    D.κ D.direction D.coercivity D.coercivity_pos (D.metric_pos τ)
    N hN (R τ) S.full.Rc S.full.M S.full.B (S.full.radius_pos τ)
    S.full.Rc_nonneg S.full.M_one_le S.full.B_nonneg
    (S.full.inverse_five τ) (S.full.inverse_six τ) (S.full.radius_small τ)
    (S.full.metric_derivatives τ) (S.full.metric_base τ) (S.full.base_bound period τ)
    (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (D.linear.coefficient τ) (D.linear.jet τ)
    (fun i => (D.quadratic i).coefficient τ) (fun i => (D.quadratic i).jet τ)
    (D.approximation τ) V (D.residual τ)
    S.full.B0 S.drift S.full.B1 S.full.A0 S.full.A2 S.full.residual S.full.A2_nonneg
    (S.full.background τ) (S.drift_bound τ) (S.full.background_derivative τ)
    (S.full.linear τ) (S.full.quadratic τ) (S.full.residual_bound τ)
    (K.operatorPath period τ) K.c K.c_pos (K.operator_coercive period τ)
  have hv : value period V = value period (e τ) := congrArg (value period) hV
  rw [energyNorm_of_value_eq period N (by omega) hN (R τ) (K.operatorPath period τ) V (e τ) hv,
    energyLoss_of_value_eq period N (by omega) hN (R τ) (K.operatorPath period τ) V (e τ) hv] at h
  simpa only [correctionArray, lowerOrderPath, orderZeroPath, ContinuousMap.coe_mk,
    CoefficientPath.operatorPath, EulerGevreyPressureTransport.transportPressure, hV,
    forcingMajorant, energyPath_apply, lossPath_apply] using h

/-- The full Bochner forcing inherits the drift bound from the actual spatial fields. -/
theorem weightedCorrectionForcing_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e))
      Filter.atTop (𝓝 U)) :
    (weightedCorrectionForcing period hq T hT D hG N hN R e U : ℝ → ℝ) ≤ᵐ[timeMeasure T]
      extendPath T hT (forcingMajorant period S hN K e) := by
  filter_upwards [weightedCorrectionForcing_ae period hq T hT D hG
    (baseMetricJet period hq D) N hN R e U hU,
    reindexMaximalTime_restriction period T hT e U hU] with t hforce hv
  exact hforce.le.trans (correctionArray_bound period S hN K e
    (reindexMaximalTime period q T U t) (projIcc 0 T hT t) hv)

end EulerDriftCorrectionEnergyBound
