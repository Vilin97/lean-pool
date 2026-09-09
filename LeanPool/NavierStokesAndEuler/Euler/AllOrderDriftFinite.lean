/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftBudget
import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionCoherence
import LeanPool.NavierStokesAndEuler.Euler.DriftGlobalInviscidGevrey
import LeanPool.NavierStokesAndEuler.Euler.InviscidSobolevEvolution

/-! Actual finite inviscid corrections constructed from the all-order drift-aware input budget. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderDriftCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerAllOrderCorrectionData EulerCorrectionAssembly EulerGevreyMetricEstimate
  EulerDriftGlobalInviscidGevrey EulerVolterraConvolution EulerInviscidSobolevEvolution

variable (period : ℝ) [Fact (0 < period)]

/-- Genuine drift-aware input budgets construct an actual finite-order inviscid correction with
quantitative retained Gevrey energy.
Finite existence, an energy inequality and convergence are conclusions of the imported actual
construction, not hypotheses here. -/
theorem finite_exists {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) :
    ∃ e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
      e ⟨0, le_rfl, hT.le⟩ = 0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period A.κ A.direction) ∧
      (∀ (P : ℕ) (_ : P ≤ q-4) (hP : P+6 ≤ q+1) t,
        energyNorm period P hP (B.radius t) (B.metric.operatorPath period t) (e t) ≤
          2*(B.spatial q hq).full.residual*Real.exp (3*B.growthCoefficient*t.val) ∧
        energyNorm period P hP (B.radius t) (B.metric.operatorPath period t) (e t) ≤ B.delta/2) ∧
      ∀ t (ht : t ∈ Ioo 0 T), HasDerivAt (fun r => value period (extendPath T hT.le e r))
        (value period (((A.atOrder period q).coefficients period hq).apply
          ⟨t, ht.1.le, ht.2.le⟩ (e ⟨t, ht.1.le, ht.2.le⟩))) t := by
  have h := exists_global_inviscid_gevrey_PDE period hq T hT (A.atOrder period ((q+1)+1))
    (A.metric.jet (q+1)) (A.linear.jet (q+1)) (fun i => (A.quadratic i).jet (q+1))
    (A.metric.continuous (q+1)) (A.linear.continuous (q+1)) (fun i => (A.quadratic i).continuous
        (q+1))
    (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
    (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q)
    A.metric_continuous (q-4) (by omega) (by omega) B.radius (B.spatial q hq)
    (A.metricBudget period hT.le B.metric (q+1)) B.growthCoefficient B.delta B.initialRadius
    (B.growth_bound q hq) B.delta_pos B.delta_le_one B.radius_pos (B.decay q hq)
    (B.scale q hq) (B.small q hq) (B.radius_eq q hq)
    (fun t => by simpa only [Data.atOrder, A.approximation.value_eq] using B.divergence t)
  rw [A.lower_twice period q] at h
  obtain ⟨e, hi, hd, _, he, hp⟩ := h
  refine ⟨e, hi, hd, he, ?_⟩
  intro t ht
  have hs := hp t ht
  rw [← CorrectionData.source_sobolev] at hs
  exact (valueOperator period q).hasFDerivAt.comp_hasDerivAt t hs

/-- The genuine finite solution chosen from the proved drift-aware construction. -/
def Budget.solution {T : ℝ} {hT : 0 < T} {A : Data period T} (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)) :=
  Classical.choose (finite_exists period hT A B q hq)

/-- The actual selected finite solutions retain both residual and target-error energy estimates. -/
theorem Budget.solution_energy {T : ℝ} {hT : 0 < T} {A : Data period T} (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (P : ℕ) (hPN : P ≤ q - 4) (hP : P + 6 ≤ q + 1) (t : Icc (0 : ℝ) T) :
    energyNorm period P hP (B.radius t) (B.metric.operatorPath period t) (B.solution period q hq t)
        ≤
      2*(B.spatial q hq).full.residual*Real.exp (3*B.growthCoefficient*t.val) ∧
    energyNorm period P hP (B.radius t) (B.metric.operatorPath period t) (B.solution period q hq t)
        ≤ B.delta/2 :=
  (Classical.choose_spec (finite_exists period hT A B q hq)).2.2.1 P hPN hP t

/-- Actual drift-aware data construct the complete finite correction family; no finite-existence
hypothesis is supplied. -/
def Budget.family {T : ℝ} {hT : 0 < T} {A : Data period T} (B : Budget period hT A) :
    FiniteFamily period hT A where
  solution := B.solution period
  initial q hq := (Classical.choose_spec (finite_exists period hT A B q hq)).1
  divergence q hq := (Classical.choose_spec (finite_exists period hT A B q hq)).2.1
  equation q hq := (Classical.choose_spec (finite_exists period hT A B q hq)).2.2.2

end EulerAllOrderDriftCorrection
