/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ViscosityDefect
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.GlobalGevreyCorrection

/-! A genuine uniformly bounded viscous approximation family with a uniformly vanishing PDE
viscosity term. -/

@[expose] public section


noncomputable section

namespace EulerViscousCorrectionFamily

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerGevreyMetricEstimate
  EulerQuadraticSource EulerPacketWeights EulerGlobalGevreyCorrection EulerViscosityDefect
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual finite-cutoff correction has a viscosity approximation sequence with uniform energy
control and a uniformly vanishing literal viscous term.
This theorem does not assert convergence of the nonlinear solution sequence itself. -/
theorem exists_viscous_correction_family {q : ℕ} (hq : 6 ≤ q) (S : ℝ) (hS : 0 < S)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) S))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (hNfull : q + 1 ≤ N + 6) (R : C(Icc (0 : ℝ) S, ℝ))
    (B : SpatialBudget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period S hS.le D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period B K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 < ρ0)
    (hdecay : 2 * C * (B.B0 + Δ) * S ≤ ρ0 / 2) (hscale : ρ0 * B.Rc ≤ 1)
    (hsmall : 2 * B.residual * Real.exp (3 * C * S) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (B.B0 + Δ) * t.val)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ e : ℕ → C(Icc (0 : ℝ) S,SobolevSpace period (q+1)),
      (∀ n, (e n) ⟨0,le_rfl,hS.le⟩ = 0 ∧
        (∀ t, value period (e n t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
        (∀ t, e n t = quadraticDuhamel period (viscositySequence n) (viscositySequence_pos n) hS.le
            le_rfl
          ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 (e n) t) ∧
        (∀ t, energyNorm period N hN (R t) (K.operatorPath period t) (e n t)
            ≤ 2*B.residual*Real.exp (3*C*t.val) ∧
          energyNorm period N hN (R t) (K.operatorPath period t) (e n t) ≤ Δ/2) ∧
        ‖e n‖ ≤ metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N) ∧
      Filter.Tendsto (fun n => viscousDefect period (by
          omega : 2 ≤ q+1) (viscositySequence n) S (e n))
        Filter.atTop (𝓝 0) := by
  have h := fun n => exists_global_gevrey_correction period hq S hS D KG KL KQ hGq hLq hQq hG
    N hN hNfull R B K C Δ ρ0 hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR
    (viscositySequence n) (viscositySequence_pos n) (viscositySequence_le_one n) hz
  choose e hi hd hm he hb using h
  refine ⟨e,fun n => ⟨hi n,hd n,hm n,he n,hb n⟩,?_⟩
  exact viscousDefect_tendsto_zero period (by omega : 2 ≤ q+1) S
    (metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N) e hb

end EulerViscousCorrectionFamily
