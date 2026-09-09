/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants

/-! Actual all-order Gevrey input budgets with radius loss controlled by the transport drift. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderDriftCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerAllOrderCorrectionData EulerCorrectionAssembly

variable (period : ℝ) [Fact (0 < period)]

/-- Genuine coherent input budgets for the drift-aware all-order correction theorem.
Full background norms enter the proved polynomial constants; only the actual transport drift enters
the shrinking-radius slope. -/
structure Budget {T : ℝ} (hT : 0 < T) (A : Data period T) where
  /-- The actual common inverse metric and its genuine time derivative. -/
  metric : MetricBudget period T hT.le (A.atOrder period 1)
  /-- The common positive shrinking radius. -/
  radius : C(Icc (0 : ℝ) T, ℝ)
  /-- The common scalar dominating the proved nonlinear growth constants. -/
  growthCoefficient : ℝ
  /-- The desired common correction bound. -/
  delta : ℝ
  /-- The common initial radius. -/
  initialRadius : ℝ
  /-- Actual coefficient, full-velocity, drift and residual bounds at every construction order. -/
  spatial : ∀ q (hq : 6 ≤ q), EulerDriftCorrectionBudget.Budget period
    (hq.trans (by omega : q ≤ (q+1)+1)) (A.atOrder period ((q+1)+1)) (q-4) radius
  /-- The common scalar bounds each actual proved energy constant. -/
  growth_bound : ∀ q hq, combinedConstant period (spatial q hq).full
    (A.metricBudget period hT.le metric (q+1)) ≤ growthCoefficient
  /-- The target error is strictly positive. -/
  delta_pos : 0 < delta
  /-- The target error is at most one. -/
  delta_le_one : delta ≤ 1
  /-- The initial radius is strictly positive. -/
  radius_pos : 0 < initialRadius
  /-- The actual drift permits retention of half of the initial radius. -/
  decay : ∀ q hq, 2*growthCoefficient*((spatial q hq).drift+delta)*T ≤ initialRadius/2
  /-- The coefficient scale fits the initial radius. -/
  scale : ∀ q hq, initialRadius*(spatial q hq).full.Rc ≤ 1
  /-- The actual residual bound beats the genuine Gronwall factor. -/
  small : ∀ q hq, 2*(spatial q hq).full.residual*Real.exp (3*growthCoefficient*T) ≤ delta/2
  /-- The same actual radius is used at every order, with slope determined by the drift envelope. -/
  radius_eq : ∀ q hq t,
    radius t = initialRadius-2*growthCoefficient*((spatial q hq).drift+delta)*t.val
  /-- The prescribed approximation satisfies the actual lifted divergence constraint. -/
  divergence : ∀ t, A.approximation.field t ∈ divergenceFreeSpace period A.κ A.direction

/-- The drift-aware input budget provides the genuine comparison data required by finite-order
uniqueness. -/
def Budget.comparisonData {T : ℝ} {hT : 0 < T} {A : Data period T}
    (B : Budget period hT A) : ComparisonData period hT A where
  metric := B.metric
  radius := B.radius
  spatial := (B.spatial 6 le_rfl).full
  divergence := B.divergence

end EulerAllOrderDriftCorrection
