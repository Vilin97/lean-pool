/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBootstrap
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionBudgetRestriction
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionContinuation

@[expose] public section

/-! The actual nonlinear Gevrey bootstrap applies uniformly to every partial correction solution. -/

noncomputable section

namespace EulerDriftPartialCorrectionBootstrap

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
    EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerCorrectionEnergyBootstrap
  EulerCorrectionBudgetRestriction EulerCorrectionContinuation EulerGevreyMetricEstimate
  EulerQuadraticSource EulerVolterraConvolution EulerSobolevHeat
open EulerDriftCorrectionBudget
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual partial solution inherits the same quantitative shrinking-radius estimate from the fixed global data. -/
theorem partial_correction_bootstrap {q : ℕ} (hq : 6 ≤ q) (S : ℝ) (hS : 0 ≤ S)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) S))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N+6 ≤ q+1) (R : C(Icc (0 : ℝ) S,ℝ))
    (B : Budget period (by omega : 6 ≤ q+1) D N R) (K : MetricBudget period S hS D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period B.full K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 <
      ρ0)
    (hdecay : 2*C*(B.drift+Δ)*S ≤ ρ0/2) (hscale : ρ0*B.full.Rc ≤ 1)
    (hsmall : 2*B.full.residual*Real.exp (3*C*S) ≤ Δ/2)
    (hR : ∀ t, R t = ρ0-2*C*(B.drift+Δ)*t.val)
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (e : C(Icc (0 : ℝ) T,SobolevSpace period (q+1)))
    (hsol : ∀ t, e t = quadraticDuhamel period ν hν hT hTS
      ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 e t) :
    ∀ t : Icc (0 : ℝ) T,
      energyNorm period N hN (R (timeInclusion hTS t)) (K.operatorPath period (timeInclusion hTS
        t)) (e t)
        ≤ 2*B.full.residual*Real.exp (3*C*t.val) ∧
      energyNorm period N hN (R (timeInclusion hTS t)) (K.operatorPath period (timeInclusion hTS
        t)) (e t) ≤ Δ/2 := by
  let f := timeInclusion hTS
  let Dt := D.comp period f
  let Bt := EulerDriftCorrectionBudget.Budget.restrict period B hTS
  let Kt := EulerCorrectionBudgetRestriction.MetricBudget.restrict period K hT hTS
  let Rt := R.comp f
  let Rd : C(Icc (0 : ℝ) T,ℝ) := ContinuousMap.const _ (-2*C*(B.drift+Δ))
  have hCp : 0 < C := (combinedConstant_pos period B.full K).trans_le hC
  have hB0 := B.drift_nonneg
  have hr := B.full.residual_pos
  have hdecayT : 2*C*(B.drift+Δ)*T ≤ ρ0/2 :=
    (mul_le_mul_of_nonneg_left hTS (by positivity : 0 ≤ 2*C*(B.drift+Δ))).trans hdecay
  have hsmallT : 2*B.full.residual*Real.exp (3*C*T) ≤ Δ/2 := by
    apply le_trans _ hsmall
    gcongr
  have he := correction_mild_divergenceFree period hq ν hν hT hTS
    (lowerData period D KG KL KQ hGq hLq hQq) e hsol
  have ht := EulerDriftCorrectionBootstrap.correction_mild_bootstrap period hq T hT Dt
    (fun t => KG (f t)) (fun t => KL (f t)) (fun i t => KQ i (f t))
    (hGq.comp f.continuous) (hLq.comp f.continuous) (fun i => (hQq i).comp f.continuous)
    (hG.comp f.continuous) N hN Rt Rd Bt Kt C Δ ρ0 hC hΔ hΔ1 hρ0
    hdecayT hscale hsmallT (fun t => hR (f t)) (fun _ => rfl) ν hν hν1 e
    (fun t => hsol t) (fun t => hz (f t)) he
  exact ht

end EulerDriftPartialCorrectionBootstrap
