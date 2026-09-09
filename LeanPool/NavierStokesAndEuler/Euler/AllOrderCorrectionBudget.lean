/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionCoherence
import LeanPool.NavierStokesAndEuler.Euler.GlobalInviscidGevrey
import LeanPool.NavierStokesAndEuler.Euler.InviscidSobolevEvolution

/-! Concrete uniform Gevrey budgets for one coherent family of prescribed data. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionBudget

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerAllOrderCorrectionData EulerGevreyMetricEstimate EulerGlobalInviscidGevrey
  EulerCorrectionLowerData EulerVolterraConvolution EulerInviscidSobolevEvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual all-order data budgets with common radius, error size and time interval; these are
coefficient/background/residual inequalities, not solution or energy hypotheses. -/
structure Budget {T : ℝ} (hT : 0 < T) (A : Data period T) where
  /-- The common actual inverse metric and its genuine time derivative. -/
  metric : MetricBudget period T hT.le (A.atOrder period 1)
  /-- The common positive shrinking-radius path. -/
  radius : C(Icc (0 : ℝ) T,ℝ)
  /-- The common scalar growth coefficient. -/
  boundConstant : ℝ
  /-- The common desired error size. -/
  delta : ℝ
  /-- The common initial radius. -/
  initialRadius : ℝ
  /-- Genuine coefficient, background and residual bounds at each finite construction cutoff. -/
  spatial : ∀ q (hq : 6 ≤ q), SpatialBudget period (hq.trans (by omega : q ≤ (q+1)+1))
    (A.atOrder period ((q+1)+1)) (q-4) radius
  /-- The fixed scalar dominates each proved nonlinear energy constant. -/
  constant_bound : ∀ q hq, combinedConstant period (spatial q hq)
    (A.metricBudget period hT.le metric (q+1)) ≤ boundConstant
  /-- Strictly positive target error size. -/
  delta_pos : 0 < delta
  /-- The target error is at most one. -/
  delta_le_one : delta ≤ 1
  /-- Strictly positive initial radius. -/
  radius_pos : 0 < initialRadius
  /-- Every construction retains half the common initial radius. -/
  decay : ∀ q hq, 2*boundConstant*((spatial q hq).B0+delta)*T ≤ initialRadius/2
  /-- The coefficient scale fits the common initial radius. -/
  scale : ∀ q hq, initialRadius*(spatial q hq).Rc ≤ 1
  /-- The actual residual budgets beat the genuine Gronwall factor. -/
  small : ∀ q hq, 2*(spatial q hq).residual*Real.exp (3*boundConstant*T) ≤ delta/2
  /-- Every finite construction uses the same actual shrinking radius. -/
  radius_eq : ∀ q hq t, radius t=initialRadius-2*boundConstant*((spatial q hq).B0+delta)*t.val
  /-- The prescribed approximate field is genuinely lifted divergence-free. -/
  divergence : ∀ t, A.approximation.field t ∈ divergenceFreeSpace period A.κ A.direction

/-- The concrete all-order budgets construct an actual finite-order inviscid correction, with
retained Gevrey energy and its actual equation. -/
theorem finite_exists {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) :
    ∃ e : C(Icc (0 : ℝ) T,SobolevSpace period (q+1)),
      e ⟨0,le_rfl,hT.le⟩=0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period A.κ A.direction) ∧
      (∀ (P : ℕ) (_ : P ≤ q-4) (hP : P+6 ≤ q+1) t,
        energyNorm period P hP (B.radius t) (B.metric.operatorPath period t) (e t) ≤ B.delta/2) ∧
      ∀ t (ht : t ∈ Ioo 0 T), HasDerivAt (fun r => value period (extendPath T hT.le e r))
        (value period (((A.atOrder period q).coefficients period hq).apply
          ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩))) t := by
  have h := exists_global_inviscid_gevrey_PDE period hq T hT (A.atOrder period ((q+1)+1))
    (A.metric.jet (q+1)) (A.linear.jet (q+1)) (fun i => (A.quadratic i).jet (q+1))
    (A.metric.continuous (q+1)) (A.linear.continuous (q+1)) (fun i => (A.quadratic i).continuous
        (q+1))
    (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
    (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q)
    A.metric_continuous (q-4) (by omega) (by omega) B.radius (B.spatial q hq)
    (A.metricBudget period hT.le B.metric (q+1)) B.boundConstant B.delta B.initialRadius
    (B.constant_bound q hq) B.delta_pos B.delta_le_one B.radius_pos (B.decay q hq)
    (B.scale q hq) (B.small q hq) (B.radius_eq q hq)
    (fun t => by simpa only [Data.atOrder,A.approximation.value_eq] using B.divergence t)
  rw [A.lower_twice period q] at h
  obtain ⟨e,hi,hd,_,he,hp⟩ := h
  refine ⟨e,hi,hd,(fun P hP hPq t => (he P hP hPq t).2),?_⟩
  intro t ht
  have hs := hp t ht
  rw [← CorrectionData.source_sobolev] at hs
  exact (valueOperator period q).hasFDerivAt.comp_hasDerivAt t hs

end EulerAllOrderCorrectionBudget
