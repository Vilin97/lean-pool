/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GlobalInviscidGevrey
public import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionCompatibility

@[expose] public section

/-! Coherent prescribed cylinder data at every finite Sobolev order. -/

noncomputable section

namespace EulerAllOrderCorrectionData

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
  EulerCorrectionLowerData EulerCorrectionEnergyData
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A single actual coefficient field with genuine derivative jets and continuous multiplier action at every finite order. -/
structure CoefficientTower (T : ℝ) where
  /-- The actual smooth bounded coefficient at each time. -/
  coefficient : Icc (0 : ℝ) T → SmoothCoefficient period
  /-- Genuine strong derivative jets of this same coefficient. -/
  jet : ∀ q t, CoefficientJet period standardDirection q (coefficient t)
  /-- Actual multiplier continuity at every finite Sobolev order. -/
  continuous : ∀ q, Continuous (fun t => coefficientSobolevOperator period (jet q t))

/-- A single prescribed L² path realized by actual continuous Sobolev paths at every order. -/
structure FieldTower (T : ℝ) where
  /-- The common actual L² field path. -/
  field : C(Icc (0 : ℝ) T,LiftL2 period)
  /-- Actual finite-order Sobolev realizations of that field. -/
  realization : ∀ q, C(Icc (0 : ℝ) T,SobolevSpace period q)
  /-- Each realization represents exactly the prescribed field. -/
  value_eq : ∀ q t, value period (realization q t)=field t

/-- Coherence of prescribed Sobolev realizations follows from genuine derivative uniqueness. -/
theorem FieldTower.truncate {T : ℝ} (f : FieldTower period T) (q : ℕ) :
    (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) (f.realization (q+1)) =
      f.realization q := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  change value period (truncateOperator period q (f.realization (q+1) t))=value period
    (f.realization q t)
  rw [value_truncateOperator,f.value_eq,f.value_eq]

/-- Actual all-order prescribed coefficient, approximation and residual data; no correction solution or energy estimate is contained here. -/
structure Data (T : ℝ) where
  /-- The fixed spatial scale in the lifted derivative. -/
  κ : ℝ
  /-- The fixed angular direction. -/
  direction : Vector3
  /-- The actual scale bound used by transport. -/
  scale_bound : |κ| ≤ 1
  /-- The actual direction bound used by transport. -/
  direction_bound : ‖direction‖ ≤ 1
  /-- The actual pressure coefficient and all its derivative jets. -/
  metric : CoefficientTower period T
  /-- The coefficient is continuous as an actual L² multiplier. -/
  metric_continuous : Continuous (fun t => (metric.coefficient t).operator)
  /-- The actual positive coercivity constant. -/
  coercivity : ℝ
  /-- Strict positivity of that constant. -/
  coercivity_pos : 0 < coercivity
  /-- Pointwise coercivity of the actual coefficient. -/
  metric_pos : ∀ t x v, coercivity*‖v‖^2 ≤ inner ℝ ((metric.coefficient t).coefficient x v) v
  /-- The actual order-zero linear coefficient. -/
  linear : CoefficientTower period T
  /-- The three actual order-zero quadratic coefficients. -/
  quadratic : Fin 3 → CoefficientTower period T
  /-- The prescribed approximate solution, with all actual Sobolev realizations. -/
  approximation : FieldTower period T
  /-- The prescribed residual, with all actual Sobolev realizations. -/
  residual : FieldTower period T

/-- The literal finite-order correction data extracted from a coherent prescribed tower. -/
def Data.atOrder {T : ℝ} (A : Data period T) (q : ℕ) : CorrectionData period q (Icc (0 : ℝ) T) where
  κ := A.κ
  direction := A.direction
  scale_bound := A.scale_bound
  direction_bound := A.direction_bound
  metric := ⟨A.metric.coefficient,A.metric.jet q,A.metric.continuous q⟩
  coercivity := A.coercivity
  coercivity_pos := A.coercivity_pos
  metric_pos := A.metric_pos
  linear := ⟨A.linear.coefficient,A.linear.jet q,A.linear.continuous q⟩
  quadratic i := ⟨(A.quadratic i).coefficient,(A.quadratic i).jet q,(A.quadratic i).continuous q⟩
  approximation := A.approximation.realization (q+1)
  residual := A.residual.realization q

/-- Lowering the actual prescribed data gives exactly the next member of the same tower. -/
theorem Data.lower_atOrder {T : ℝ} (A : Data period T) (q : ℕ) :
    lowerData period (A.atOrder period (q+1)) (A.metric.jet q) (A.linear.jet q)
      (fun i => (A.quadratic i).jet q) (A.metric.continuous q) (A.linear.continuous q)
      (fun i => (A.quadratic i).continuous q) = A.atOrder period q := by
  unfold lowerData Data.atOrder
  congr 1
  · exact A.approximation.truncate period (q+1)
  · exact A.residual.truncate period q

/-- A single actual inverse-metric budget applies to every finite realization of the same coefficient field. -/
def Data.metricBudget {T : ℝ} (A : Data period T) (hT : 0 ≤ T)
    (K : MetricBudget period T hT (A.atOrder period 1)) (q : ℕ) :
    MetricBudget period T hT (A.atOrder period (q+1)) where
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
  bound_nonneg := K.bound_nonneg
  first_nonneg := K.first_nonneg
  time_nonneg := K.time_nonneg
  bound_le := K.bound_le
  first_le := K.first_le
  time_le := K.time_le

end EulerAllOrderCorrectionData
