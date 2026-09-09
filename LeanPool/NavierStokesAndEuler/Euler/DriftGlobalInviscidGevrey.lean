/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBudget
import LeanPool.NavierStokesAndEuler.Euler.CorrectionLimitEquation
import LeanPool.NavierStokesAndEuler.Euler.DriftGevreyInviscidEnergyCompactness
import LeanPool.NavierStokesAndEuler.Euler.InviscidSobolevEvolution

/-! Drift-aware version: Whole-interval inviscid correction retaining quantitative Gevrey bounds and
its actual finite-Sobolev pressure equation. -/

@[expose] public section


noncomputable section

namespace EulerDriftGlobalInviscidGevrey

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerGevreyMetricEstimate
  EulerQuadraticSource EulerPacketWeights EulerDriftGevreyInviscidEnergyCompactness
      EulerCorrectionLimitEquation EulerVolterraConvolution
  EulerInviscidSobolevEvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Concrete Gevrey data construct an actual global inviscid correction, retaining both quantitative
energy bounds at every surviving cutoff, with its literal signed-pressure derivative in Hq. -/
theorem exists_global_inviscid_gevrey_PDE {q : ℕ} (hq : 6 ≤ q) (S : ℝ) (hS : 0 < S)
    (D : CorrectionData period ((q + 1) + 1) (Icc (0 : ℝ) S))
    (KG1 : ∀ t, CoefficientJet period standardDirection (q + 1) (D.metric.coefficient t))
    (KL1 : ∀ t, CoefficientJet period standardDirection (q + 1) (D.linear.coefficient t))
    (KQ1 : ∀ i t, CoefficientJet period standardDirection (q + 1) ((D.quadratic i).coefficient t))
    (hG1 : Continuous (fun t => coefficientSobolevOperator period (KG1 t)))
    (hL1 : Continuous (fun t => coefficientSobolevOperator period (KL1 t)))
    (hQ1 : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ1 i t)))
    (KG0 : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL0 : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ0 : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG0 : Continuous (fun t => coefficientSobolevOperator period (KG0 t)))
    (hL0 : Continuous (fun t => coefficientSobolevOperator period (KL0 t)))
    (hQ0 : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ0 i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ (q + 1) + 1) (hNfull : (q + 1) + 1 ≤ N + 6) (R : C(Icc (0 : ℝ) S, ℝ))
    (B : EulerDriftCorrectionBudget.Budget period (hq.trans (Nat.le_succ q) |>.trans (Nat.le_succ
        (q + 1))) D N R) (K : MetricBudget period S hS.le D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period B.full K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 <
        ρ0)
    (hdecay : 2 * C * (B.drift + Δ) * S ≤ ρ0 / 2) (hscale : ρ0 * B.full.Rc ≤ 1)
    (hsmall : 2 * B.full.residual * Real.exp (3 * C * S) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (B.drift + Δ) * t.val)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction) :
    let Dlow := lowerData period (lowerData period D KG1 KL1 KQ1 hG1 hL1 hQ1)
      KG0 KL0 KQ0 hG0 hL0 hQ0
    ∃ e : C(Icc (0 : ℝ) S,SobolevSpace period (q+1)),
      e ⟨0,le_rfl,hS.le⟩=0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
      ‖e‖ ≤ metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N ∧
      (∀ (P : ℕ) (_ : P ≤ N) (hP : P+6 ≤ q+1) t,
        energyNorm period P hP (R t) (K.operatorPath period t) (e t) ≤
          2*B.full.residual*Real.exp (3*C*t.val) ∧
        energyNorm period P hP (R t) (K.operatorPath period t) (e t) ≤ Δ/2) ∧
      ∀ t (ht : t ∈ Ioo 0 S),
        HasDerivAt (fun r => truncateOperator period q (extendPath S hS.le e r))
          (-Dlow.rawSource period hq ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩) -
            coefficientSobolevOperator period (Dlow.metric.jet ⟨t,ht.1.le,ht.2.le⟩)
              (Dlow.pressure period hq ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩))) t := by
  obtain ⟨u,e,hu,hconv,hi,hd,hM,hE⟩ :=
      EulerDriftGevreyInviscidEnergyCompactness.exists_gevrey_inviscid_energy_limit period (q :=
          q+1)
    (hq.trans (Nat.le_succ q)) S hS D KG1 KL1 KQ1 hG1 hL1 hQ1 hG
    N hN hNfull R B K C Δ ρ0 hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR hz
  refine ⟨e,hi,hd,hM,hE,?_⟩
  apply correction_sobolev_hasDerivAt period hq S hS.le
    (lowerData period (lowerData period D KG1 KL1 KQ1 hG1 hL1 hQ1)
      KG0 KL0 KQ0 hG0 hL0 hQ0) e
  exact correction_limit_equation period hq S hS.le (lowerData period D KG1 KL1 KQ1 hG1 hL1 hQ1)
    KG0 KL0 KQ0 hG0 hL0 hQ0 u e (metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N)
    (fun n => (hu n).2.2.2) hconv (fun n => (hu n).2.2.1)

end EulerDriftGlobalInviscidGevrey
