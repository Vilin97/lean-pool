/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyGrowthBudget
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMetricPaths
import LeanPool.NavierStokesAndEuler.Euler.H6PressureConstants

/-! Concrete coefficient and background budgets for the actual nonlinear correction energy theorem.
-/

@[expose] public section


noncomputable section

namespace EulerCorrectionEnergyData

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators
   EulerGevreyMetricEstimate EulerGevreyGrowthCoefficient
  EulerH6Pressure EulerSobolevGevreyOperators EulerRegularizedMetricPaths
  EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual derivative and residual norm budgets at the chosen cutoff; no energy or nonlinear forcing
estimate is assumed. -/
structure SpatialBudget {q : ℕ} {T : ℝ} (hq : 6 ≤ q + 1)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)) (N : ℕ) (R : C(Icc (0 : ℝ) T, ℝ)) where
  /-- Coefficient derivative radius. -/
  Rc : ℝ
  /-- Proven fixed-base pressure inverse bound. -/
  M : ℝ
  /-- Base coefficient derivative bound. -/
  B : ℝ
  /-- Background velocity norm bound. -/
  B0 : ℝ
  /-- Background derivative norm bound. -/
  B1 : ℝ
  /-- Linear coefficient norm bound. -/
  A0 : ℝ
  /-- Quadratic coefficient norm bound. -/
  A2 : ℝ
  /-- Approximate-equation residual norm bound. -/
  residual : ℝ
  /-- The coefficient radius is nonnegative. -/
  Rc_nonneg : 0 ≤ Rc
  /-- The pressure bound is at least one. -/
  M_one_le : 1 ≤ M
  /-- The base coefficient budget is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- The background budget is nonnegative. -/
  B0_nonneg : 0 ≤ B0
  /-- The background derivative budget is nonnegative. -/
  B1_nonneg : 0 ≤ B1
  /-- The linear budget is nonnegative. -/
  A0_nonneg : 0 ≤ A0
  /-- The quadratic budget is nonnegative. -/
  A2_nonneg : 0 ≤ A2
  /-- The residual budget is strictly positive. -/
  residual_pos : 0 < residual
  /-- The actual radius stays positive. -/
  radius_pos : ∀ t, 0 < R t
  /-- The actual H⁵ projected inverse has the fixed bound. -/
  inverse_five : ∀ t, (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet t) 5 (by
      omega)).pressureConstant D.coercivity ≤ M
  /-- The actual H⁶ projected inverse has the fixed bound. -/
  inverse_six : ∀ t, (EulerH6Pressure.CoefficientJet.restrict (D.metric.jet t) 6
      hq).pressureConstant D.coercivity ≤ M
  /-- The coefficient series is in the proved inverse absorption regime. -/
  radius_small : ∀ t, 4*M*(R t*Rc) ≤ 1
  /-- Actual higher coefficient derivatives satisfy the factorial estimate. -/
  metric_derivatives : ∀ t l, 1 ≤ l → l ≤ N → coefficientBlock period (D.metric.jet t) 6 l ≤
      Rc^l*(l.factorial : ℝ)^2
  /-- Actual base coefficient derivatives satisfy the fixed budget. -/
  metric_base : ∀ t r, r ≤ 6 → EulerJetProductBounds.boundLevel period (D.metric.jet t) r ≤ B
  /-- The actual approximate velocity has the background norm budget. -/
  background : ∀ t, weightedNorm period 6 N (R t) (D.approximation t) ≤ B0
  /-- The actual approximate velocity derivatives have the background derivative budget. -/
  background_derivative : ∀ t, (∑ i : Fin 4, weightedNorm period 6 N (R t) (derivativeOperator
      period (q+1) i (D.approximation t))) ≤ B1
  /-- Actual linear multiplier derivatives have the linear budget. -/
  linear : ∀ t, weightedCoefficient period (D.linear.jet t) 6 N (R t) ≤ A0
  /-- Actual quadratic multiplier derivatives have the quadratic budget. -/
  quadratic : ∀ t, (∑ i : Fin 3, weightedCoefficient period ((D.quadratic i).jet t) 6 N (R t)) ≤ A2
  /-- The literal approximate-equation residual has the residual budget. -/
  residual_bound : ∀ t, weightedNorm period 6 N (R t) (D.residual t) ≤ residual

/-- An actual inverse metric and its uniform first spatial and time derivative budgets. -/
structure MetricBudget {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)) where
  /-- Actual spatial inverse metric at each time. -/
  metric : Icc (0 : ℝ) T → SmoothCoefficient period
  /-- Its actual L² multiplier path is continuous. -/
  continuous : Continuous (fun t => (metric t).operator)
  /-- Actual time derivative of the L² metric operator. -/
  derivative : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period)
  /-- The stated time derivative is the genuine derivative at every interior time. -/
  hasDeriv : ∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT (metricOperatorPath period T metric
      continuous))
    (extendPath T hT derivative t) t
  /-- Positive square-root coercivity constant. -/
  c : ℝ
  /-- Strict metric coercivity. -/
  c_pos : 0 < c
  /-- Pointwise symmetry of the actual metric. -/
  symmetric : ∀ t x v w, ⟪(metric t).coefficient x v,w⟫_ℝ = ⟪v,(metric t).coefficient x w⟫_ℝ
  /-- Pointwise positive lower bound for the actual metric. -/
  coercive : ∀ t x v, c^2*‖v‖^2 ≤ ⟪(metric t).coefficient x v,v⟫_ℝ
  /-- The actual metric inverts the coefficient in the pressure equation. -/
  inverse : ∀ t x v, (metric t).coefficient x ((D.metric.coefficient t).coefficient x v) = v
  /-- Uniform metric multiplier bound. -/
  bound : ℝ
  /-- Uniform first spatial derivative bound. -/
  first : ℝ
  /-- Uniform time derivative operator bound. -/
  time : ℝ
  /-- The multiplier budget is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- The spatial derivative budget is nonnegative. -/
  first_nonneg : 0 ≤ first
  /-- The time derivative budget is nonnegative. -/
  time_nonneg : 0 ≤ time
  /-- The actual multiplier witness is bounded uniformly. -/
  bound_le : ∀ t, ((metric t).bound : ℝ) ≤ bound
  /-- The actual first derivative witness is bounded uniformly. -/
  first_le : ∀ t, ((metric t).firstBound : ℝ) ≤ first
  /-- The actual time derivative is bounded uniformly. -/
  time_le : ∀ t, ‖derivative t‖ ≤ time

/-- The canonical genuine base-order coefficient jet. -/
def baseMetricJet {q : ℕ} (hq : 6 ≤ q + 1) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)) (t : Icc (0 : ℝ) T) :
    CoefficientJet period standardDirection 6 (D.metric.coefficient t) :=
  EulerH6Pressure.CoefficientJet.restrict (D.metric.jet t) 6 hq

/-- The actual metric budget determines its concrete continuous L² multiplier path. -/
def MetricBudget.operatorPath {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} (K : MetricBudget period T hT D) :
    C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period) := metricOperatorPath period T K.metric
        K.continuous

/-- The actual metric operator is coercive with the same pointwise constant. -/
theorem MetricBudget.operator_coercive {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} (K : MetricBudget period T hT D)
    (t : Icc (0 : ℝ) T) (v : LiftL2 period) : K.c^2*‖v‖^2 ≤ ⟪K.operatorPath period t v,v⟫_ℝ :=
  EulerLiftedPressure.coefficientOperator_coercive (K.metric t).coefficient (K.metric t).measurable
    (K.metric t).bound (K.metric t).norm_bound (K.c^2) (K.coercive t) v

/-- The actual canonical base jet inherits the given derivative budget. -/
theorem SpatialBudget.base_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (t : Icc (0 : ℝ) T) (r : ℕ) (hr : r ≤ 6) :
    EulerJetProductBounds.boundLevel period (baseMetricJet period hq D t) r ≤ S.B := by
  change EulerJetProductBounds.boundLevel period (EulerH6Pressure.CoefficientJet.restrict
      (D.metric.jet t) 6 hq) r ≤ S.B
  rw [EulerH6Pressure.coefficient_restrict_level period (D.metric.jet t) hq hr]
  exact S.metric_base t r hr

/-- The fixed constant part of the actual metric-growth majorant. -/
def MetricBudget.growth0 {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} (K : MetricBudget period T hT D) (B0 : ℝ) :
        ℝ
        :=
  growthBudgetBase K.c K.time K.first + growthBudgetSlope K.c K.first*sobolevEmbeddingConstant
      period 6*B0

/-- The fixed linear part of the actual metric-growth majorant. -/
def MetricBudget.growth1 {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} (K : MetricBudget period T hT D) : ℝ :=
  growthBudgetSlope K.c K.first*sobolevEmbeddingConstant period 6*metricAmplification K.c

/-- The fixed coefficient multiplying the actual forcing norm. -/
def MetricBudget.multiplier {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} (K : MetricBudget period T hT D) : ℝ :=
        K.bound/K.c

/-- All fixed metric-growth and forcing coefficients are nonnegative. -/
theorem MetricBudget.constants_nonneg {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} (K : MetricBudget period T hT D) (B0 : ℝ)
        (hB0 : 0 ≤ B0) :
    0 ≤ K.growth0 period B0 ∧ 0 ≤ K.growth1 period ∧ 0 ≤ K.multiplier := by
  have he := sobolevEmbeddingConstant_nonneg period 6
  have hm : 0 ≤ metricAmplification K.c := (by
      norm_num : (0 : ℝ) ≤ 1).trans (metricAmplification_one_le K.c_pos)
  have ht := K.time_nonneg
  have hl := K.first_nonneg
  have hk := K.bound_nonneg
  have hc := K.c_pos.le
  unfold MetricBudget.growth0 MetricBudget.growth1 MetricBudget.multiplier growthBudgetBase
      growthBudgetSlope
  constructor
  · positivity
  constructor <;> positivity

end EulerCorrectionEnergyData
