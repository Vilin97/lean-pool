/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.CorrectionContinuation
import LeanPool.NavierStokesAndEuler.Euler.GevreyPathNorm
import LeanPool.NavierStokesAndEuler.Euler.PartialCorrectionBootstrap

/-! Actual global-in-time viscous correction from concrete Gevrey coefficient and residual budgets.
-/

@[expose] public section


noncomputable section

namespace EulerGlobalGevreyCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerPartialCorrectionBootstrap
  EulerCorrectionContinuation EulerGevreyMetricEstimate EulerGevreyPathNorm EulerEnergyMetricPaths
  EulerQuadraticSource EulerPacketWeights
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Concrete coefficient and residual bounds yield an actual viscous correction throughout the
prescribed interval.
The a-priori energy estimate and the continuation bound are proved inside this theorem, not supplied
as hypotheses. -/
theorem exists_global_gevrey_correction {q : ℕ} (hq : 6 ≤ q) (S : ℝ) (hS : 0 < S)
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
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ e : C(Icc (0 : ℝ) S,SobolevSpace period (q+1)),
      e ⟨0,le_rfl,hS.le⟩ = 0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
      (∀ t, e t = quadraticDuhamel period ν hν hS.le le_rfl
        ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 e t) ∧
      (∀ t, energyNorm period N hN (R t) (K.operatorPath period t) (e t)
          ≤ 2*B.residual*Real.exp (3*C*t.val) ∧
        energyNorm period N hN (R t) (K.operatorPath period t) (e t) ≤ Δ/2) ∧
      ‖e‖ ≤ metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N := by
  let δ := min (ρ0/2) 1
  let M := metricAmplification K.c*(Δ/2)/weight δ N
  have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have ha : 0 ≤ metricAmplification K.c :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (metricAmplification_one_le K.c_pos)
  have hM : 0 ≤ M := div_nonneg (mul_nonneg ha (by positivity)) (weight_pos hδ N).le
  have hCp : 0 < C := (combinedConstant_pos period B K).trans_le hC
  have hcoef : 0 ≤ 2*C*(B.B0+Δ) := by have := B.B0_nonneg; positivity
  have hrad (t : Icc (0 : ℝ) S) : δ ≤ R t := by
    rw [hR t]
    apply (min_le_left (ρ0/2) 1).trans
    have hm := mul_le_mul_of_nonneg_left t.property.2 hcoef
    linarith
  have hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (e : C(Icc (0 : ℝ) T,SobolevSpace period (q+1))),
      (∀ t, e t = quadraticDuhamel period ν hν hT hTS
        ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 e t) → ‖e‖ ≤ M := by
    intro T hT hTS e hsol
    have hb := partial_correction_bootstrap period hq S hS.le D KG KL KQ hGq hLq hQq hG
      N hN R B K C Δ ρ0 hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR ν hν hν1 hz T hT hTS e hsol
    apply norm_le_of_energy_bound period N hN hNfull T (R.comp (timeInclusion hTS))
      ((K.operatorPath period).comp (timeInclusion hTS)) e K.c δ (Δ/2) K.c_pos hδ hδ1 (by
          positivity)
      (fun t => hrad (timeInclusion hTS t)) (fun t => K.operator_coercive period (timeInclusion hTS
          t))
    intro t
    rw [energyPath_apply]
    exact (hb t).2
  obtain ⟨e,he,hi,hd,hsol⟩ := exists_global_correction_of_bound period hq ν hν S hS M hM
    (lowerData period D KG KL KQ hGq hLq hQq) hbound
  have hb := partial_correction_bootstrap period hq S hS.le D KG KL KQ hGq hLq hQq hG
    N hN R B K C Δ ρ0 hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR ν hν hν1 hz S hS.le le_rfl e hsol
  exact ⟨e,hi,hd,hsol,hb,he⟩

end EulerGlobalGevreyCorrection
