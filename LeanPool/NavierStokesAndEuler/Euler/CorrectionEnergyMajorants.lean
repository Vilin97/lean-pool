/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyData
public import LeanPool.NavierStokesAndEuler.Euler.NonlinearEnergyConstants
import LeanPool.NavierStokesAndEuler.Euler.GevreyRestriction

/-! Continuous scalar majorants derived from actual coefficient budgets and actual nonlinear time
fields. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionEnergyMajorants

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyTime
      EulerCorrectionEnergyBound
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerGevreyGrowthCoefficient
      EulerGevreyRestriction
  EulerNonlinearEnergyConstants  EulerTimeLp EulerVolterraConvolution
  EulerRegularizedTopBlocks EulerWeightedCylinderEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual metric energy is nonnegative along every positive-radius solution path. -/
theorem energy_nonneg {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    0 ≤ energyPath period N hN T R (K.operatorPath period) e t := by
  rw [energyPath_apply]
  exact energyNorm_nonneg period N hN (R t) (S.radius_pos t) _ _

/-- Actual metric radius loss is nonnegative along the same solution path. -/
theorem loss_nonneg {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    0 ≤ lossPath period N hN T R (K.operatorPath period) e t := by
  rw [lossPath_apply]
  exact energyLoss_nonneg period N hN (R t) (S.radius_pos t) _ _

/-- The actual total velocity has the genuine metric-energy pointwise bound. -/
theorem velocity_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure period, ‖value period (velocityPath period D e t) x‖ ≤
      metricVelocityBound period K.c S.B0 (energyPath period N hN T R (K.operatorPath period) e t)
          := by
  have hz : EulerSobolevGevreyOperators.weightedNorm period 6 N (R t)
      (truncateOperator period (q+1) (D.approximation t)) ≤ S.B0 := by
    rw [weightedNorm_truncate period 6 N hN]
    exact S.background t
  rw [energyPath_apply]
  exact velocity_ae_metric period N hN (R t) (S.radius_pos t) (K.operatorPath period t)
    (truncateOperator period (q+1) (D.approximation t)) (e t) K.c S.B0 K.c_pos (K.operator_coercive
        period t) hz

/-- Adding the actual divergence-free approximation and error preserves the lifted constraint. -/
theorem velocity_divergenceFree {q : ℕ} {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (he : ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) (t : Icc (0 : ℝ) T)
        :
    value period (velocityPath period D e t) ∈ divergenceFreeSpace period D.κ D.direction :=
  (divergenceFreeSpace period D.κ D.direction).add_mem (hz t) (he t)

/-- The fixed affine continuous majorant of actual metric growth. -/
def growthPath {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => K.growth0 period S.B0 + K.growth1 period * energyPath period N hN T R (K.operatorPath
      period) e t,
    continuous_const.add (continuous_const.mul (energyPath period N hN T R (K.operatorPath period)
        e).continuous)⟩

/-- The signed radius derivative divided by the actual positive radius. -/
def radiusLossPath {T : ℝ} (R Rdot : C(Icc (0 : ℝ) T, ℝ)) (hR : ∀ t, 0 < R t) : C(Icc (0 : ℝ) T, ℝ)
    :=
  ⟨fun t => Rdot t/R t, Rdot.continuous.div R.continuous (fun t => (hR t).ne')⟩

/-- The literal continuous nonlinear forcing majorant. -/
def forcingMajorant {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) :=
  forcingBoundPath period N hN T R S.radius_pos (K.operatorPath period) e
    S.B S.M S.B0 S.B1 S.A0 S.A2 S.residual K.c S.Rc

/-- The actual metric-growth coefficient is bounded by the continuous affine majorant. -/
theorem growthPath_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (ν : ℝ) (hν : ν ≤ 1) (t : Icc (0 : ℝ) T) :
    viscousGrowthCoefficient period (K.metric t) (K.derivative t) D.κ D.direction K.c ν
      (metricVelocityBound period K.c S.B0 (energyPath period N hN T R (K.operatorPath period) e
          t)) ≤
      growthPath period S hN K e t :=
  viscousGrowth_fixed_metric period (K.metric t) (K.derivative t) D.κ D.direction K.c ν K.time
      K.first S.B0
    (energyPath period N hN T R (K.operatorPath period) e t) K.c_pos hν D.scale_bound
        D.direction_bound
    (K.time_le t) (K.first_le t) S.B0_nonneg (energy_nonneg period S hN K e t)

/-- The actual full-order nonlinear forcing has the continuous majorant derived from its genuine
coefficient budgets. -/
theorem forcingMajorant_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U)) :
    (weightedCorrectionForcing period hq T hT D hG N hN R e U : ℝ → ℝ) ≤ᵐ[timeMeasure T]
      extendPath T hT (forcingMajorant period S hN K e) :=
  weightedCorrectionForcing_bound period hq T hT D hG (baseMetricJet period hq D) N hN R
      S.radius_pos
    S.Rc S.M S.B S.Rc_nonneg S.M_one_le S.B_nonneg S.inverse_five S.inverse_six S.radius_small
    S.metric_derivatives S.metric_base (S.base_bound period) e U hU S.B0 S.B1 S.A0 S.A2 S.residual
        S.A2_nonneg
    S.background S.background_derivative S.linear S.quadratic S.residual_bound (K.operatorPath
        period) K.c K.c_pos
    (K.operator_coercive period)

/-- The explicit cutoff-independent constant in the scalar shrinking-radius estimate. -/
def combinedConstant {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) {hT : 0 ≤ T} (K : MetricBudget period T hT D) : ℝ :=
  energyConstant period (K.growth0 period S.B0) (K.growth1 period) (K.multiplier period)
    S.B S.M S.B0 S.B1 S.A0 S.A2 K.c

/-- The actual combined constant is strictly positive. -/
theorem combinedConstant_pos {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) {hT : 0 ≤ T} (K : MetricBudget period T hT D) :
    0 < combinedConstant period S K := by
  obtain ⟨hg0,hg1,hk⟩ := K.constants_nonneg period S.B0 S.B0_nonneg
  exact energyConstant_pos period _ _ _ _ _ _ _ _ _ _ hg0 hg1 hk S.B_nonneg
    (zero_le_one.trans S.M_one_le) S.B0_nonneg S.B1_nonneg S.A0_nonneg S.A2_nonneg K.c_pos

end EulerCorrectionEnergyMajorants
