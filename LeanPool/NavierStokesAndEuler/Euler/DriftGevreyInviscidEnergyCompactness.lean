/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityDefect
import LeanPool.NavierStokesAndEuler.Euler.CorrectionFamilyCompactness
import LeanPool.NavierStokesAndEuler.Euler.GevreyPathNorm
import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBootstrap

/-! Drift-aware version: Actual strong inviscid compactness retaining the quantitative Gevrey metric
energies. -/

section

/-! Actual global-in-time viscous correction from concrete Gevrey coefficient and residual budgets.
-/

section

/-! The actual nonlinear Gevrey bootstrap applies uniformly to every partial correction solution. -/

@[expose] public section

noncomputable section

namespace EulerDriftPartialCorrectionBootstrap

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerCorrectionBudgetRestriction EulerCorrectionContinuation EulerGevreyMetricEstimate
  EulerQuadraticSource EulerVolterraConvolution EulerSobolevHeat
open EulerDriftCorrectionBudget
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual partial solution inherits the same quantitative shrinking-radius estimate from the
fixed global data. -/
theorem partial_correction_bootstrap {q : ℕ} (hq : 6 ≤ q) (S : ℝ) (hS : 0 ≤ S)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) S))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R : C(Icc (0 : ℝ) S, ℝ))
    (B : Budget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period S hS D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period B.full K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 <
        ρ0)
    (hdecay : 2 * C * (B.drift + Δ) * S ≤ ρ0 / 2) (hscale : ρ0 * B.full.Rc ≤ 1)
    (hsmall : 2 * B.full.residual * Real.exp (3 * C * S) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (B.drift + Δ) * t.val)
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerDriftGlobalGevreyCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerDriftPartialCorrectionBootstrap
  EulerCorrectionContinuation EulerGevreyMetricEstimate EulerGevreyPathNorm EulerEnergyMetricPaths
  EulerQuadraticSource EulerPacketWeights
open EulerDriftCorrectionBudget
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
    (B : Budget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period S hS.le D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period B.full K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 <
        ρ0)
    (hdecay : 2 * C * (B.drift + Δ) * S ≤ ρ0 / 2) (hscale : ρ0 * B.full.Rc ≤ 1)
    (hsmall : 2 * B.full.residual * Real.exp (3 * C * S) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (B.drift + Δ) * t.val)
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ e : C(Icc (0 : ℝ) S,SobolevSpace period (q+1)),
      e ⟨0,le_rfl,hS.le⟩ = 0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
      (∀ t, e t = quadraticDuhamel period ν hν hS.le le_rfl
        ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 e t) ∧
      (∀ t, energyNorm period N hN (R t) (K.operatorPath period t) (e t)
          ≤ 2*B.full.residual*Real.exp (3*C*t.val) ∧
        energyNorm period N hN (R t) (K.operatorPath period t) (e t) ≤ Δ/2) ∧
      ‖e‖ ≤ metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N := by
  let δ := min (ρ0/2) 1
  let M := metricAmplification K.c*(Δ/2)/weight δ N
  have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have ha : 0 ≤ metricAmplification K.c :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (metricAmplification_one_le K.c_pos)
  have hM : 0 ≤ M := div_nonneg (mul_nonneg ha (by positivity)) (weight_pos hδ N).le
  have hCp : 0 < C := (combinedConstant_pos period B.full K).trans_le hC
  have hcoef : 0 ≤ 2*C*(B.drift+Δ) := by have := B.drift_nonneg; positivity
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
    have hb := EulerDriftPartialCorrectionBootstrap.partial_correction_bootstrap period hq S hS.le
        D KG KL KQ hGq hLq hQq hG
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
  have hb := EulerDriftPartialCorrectionBootstrap.partial_correction_bootstrap period hq S hS.le D
      KG KL KQ hGq hLq hQq hG
    N hN R B K C Δ ρ0 hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR ν hν hν1 hz S hS.le le_rfl e hsol
  exact ⟨e,hi,hd,hsol,hb,he⟩

end EulerDriftGlobalGevreyCorrection

end
end

end

section

/-! Drift-aware version: A genuine uniformly bounded viscous approximation family with a uniformly
vanishing PDE viscosity term. -/

@[expose] public section

noncomputable section

namespace EulerDriftViscousCorrectionFamily

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerGevreyMetricEstimate
  EulerQuadraticSource EulerPacketWeights EulerDriftGlobalGevreyCorrection EulerViscosityDefect
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
    (B : EulerDriftCorrectionBudget.Budget period (by
        omega : 6 ≤ q + 1) D N R) (K : MetricBudget period S hS.le D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period B.full K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 <
        ρ0)
    (hdecay : 2 * C * (B.drift + Δ) * S ≤ ρ0 / 2) (hscale : ρ0 * B.full.Rc ≤ 1)
    (hsmall : 2 * B.full.residual * Real.exp (3 * C * S) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (B.drift + Δ) * t.val)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ e : ℕ → C(Icc (0 : ℝ) S,SobolevSpace period (q+1)),
      (∀ n, (e n) ⟨0,le_rfl,hS.le⟩ = 0 ∧
        (∀ t, value period (e n t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
        (∀ t, e n t = quadraticDuhamel period (viscositySequence n) (viscositySequence_pos n) hS.le
            le_rfl
          ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 (e n) t) ∧
        (∀ t, energyNorm period N hN (R t) (K.operatorPath period t) (e n t)
            ≤ 2*B.full.residual*Real.exp (3*C*t.val) ∧
          energyNorm period N hN (R t) (K.operatorPath period t) (e n t) ≤ Δ/2) ∧
        ‖e n‖ ≤ metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N) ∧
      Filter.Tendsto (fun n => viscousDefect period (by
          omega : 2 ≤ q+1) (viscositySequence n) S (e n))
        Filter.atTop (𝓝 0) := by
  have h := fun n => EulerDriftGlobalGevreyCorrection.exists_global_gevrey_correction period hq S
      hS D KG KL KQ hGq hLq hQq hG
    N hN hNfull R B K C Δ ρ0 hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR
    (viscositySequence n) (viscositySequence_pos n) (viscositySequence_le_one n) hz
  choose e hi hd hm he hb using h
  refine ⟨e,fun n => ⟨hi n,hd n,hm n,he n,hb n⟩,?_⟩
  exact viscousDefect_tendsto_zero period (by omega : 2 ≤ q+1) S
    (metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N) e hb

end EulerDriftViscousCorrectionFamily

end
end

end

@[expose] public section

noncomputable section

namespace EulerDriftGevreyInviscidEnergyCompactness

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerGevreyMetricEstimate
  EulerQuadraticSource EulerPacketWeights EulerViscosityDefect EulerDriftViscousCorrectionFamily
       EulerCorrectionFamilyCompactness EulerGevreyFamilyCompactness
          EulerGevreyEnergyPathLimit
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited Sobolev normed-group instance for compactness. -/
local instance energyCompactnessSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q)
    := inferInstance
/-- The inherited real Sobolev module instance for compactness. -/
local instance energyCompactnessSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance

/-- The actual Gevrey correction construction produces its strong inviscid limit with both
quantitative energy bounds at every retained cutoff.
No convergence, compactness, energy inequality, or comparison estimate is supplied as a hypothesis.
-/
theorem exists_gevrey_inviscid_energy_limit {q : ℕ} (hq : 6 ≤ q) (S : ℝ) (hS : 0 < S)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) S))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (hNfull : q + 1 ≤ N + 6) (R : C(Icc (0 : ℝ) S, ℝ))
    (B : EulerDriftCorrectionBudget.Budget period (hq.trans (Nat.le_succ q)) D N R) (K :
        MetricBudget period S hS.le D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period B.full K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 <
        ρ0)
    (hdecay : 2 * C * (B.drift + Δ) * S ≤ ρ0 / 2) (hscale : ρ0 * B.full.Rc ≤ 1)
    (hsmall : 2 * B.full.residual * Real.exp (3 * C * S) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (B.drift + Δ) * t.val)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ u : ℕ → C(Icc (0 : ℝ) S,SobolevSpace period (q+1)),
      ∃ e : C(Icc (0 : ℝ) S,SobolevSpace period q),
        (∀ n, u n ⟨0,le_rfl,hS.le⟩ = 0 ∧
          (∀ t, value period (u n t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
          (∀ t, u n t = quadraticDuhamel period (viscositySequence n) (viscositySequence_pos n)
              hS.le le_rfl
            ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 (u n) t) ∧
          ‖u n‖ ≤ metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N) ∧
        Filter.Tendsto (fun n => (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) S)
            (u n))
          Filter.atTop (𝓝 e) ∧
        e ⟨0,le_rfl,hS.le⟩ = 0 ∧
        (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
        ‖e‖ ≤ metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N ∧
        ∀ (P : ℕ) (_ : P ≤ N) (hP : P+6 ≤ q) t,
          energyNorm period P hP (R t) (K.operatorPath period t) (e t) ≤
            2*B.full.residual*Real.exp (3*C*t.val) ∧
          energyNorm period P hP (R t) (K.operatorPath period t) (e t) ≤ Δ/2 := by
  obtain ⟨u,hu,hdefect⟩ := EulerDriftViscousCorrectionFamily.exists_viscous_correction_family
      period (q := q) hq S hS D KG KL KQ hGq hLq hQq hG
    N hN hNfull R B K C Δ ρ0 hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR hz
  refine ⟨u,?_⟩
  let M := metricAmplification K.c*(Δ/2)/weight (min (ρ0/2) 1) N
  have huM (n : ℕ) : ‖u n‖ ≤ M := (hu n).2.2.2.2
  have hiFamily : ∀ n, u n ⟨0,le_rfl,hS.le⟩ = 0 := fun n => (hu n).1
  have hdFamily : ∀ n t, value period (u n t) ∈ divergenceFreeSpace period D.κ D.direction :=
    fun n => (hu n).2.1
  have hmFamily : ∀ n t, u n t = quadraticDuhamel period (viscositySequence n)
      (viscositySequence_pos n) hS.le le_rfl
      ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 (u n) t :=
    fun n => (hu n).2.2.1
  have heFamily : ∀ n t, energyNorm period N hN (R t) (K.operatorPath period t) (u n t)
      ≤ 2*B.full.residual*Real.exp (3*C*t.val) ∧
      energyNorm period N hN (R t) (K.operatorPath period t) (u n t) ≤ Δ/2 :=
    fun n => (hu n).2.2.2.1
  clear hu hdefect hG hNfull hC hΔ hΔ1 hρ0 hdecay hscale hsmall hR
  have hvc : CauchySeq viscositySequence := viscositySequence_tendsto.cauchySeq
  have hlim := exists_limit_of_gevrey_family period (q := q) hq S hS.le D KG KL KQ hGq hLq hQq N R
      B.full K
    viscositySequence viscositySequence_pos viscositySequence_le_one hvc
  apply Exists.imp (fun e he => ?_) (hlim u M huM hiFamily hmFamily hz hdFamily)
  refine ⟨(fun n => ⟨hiFamily n,hdFamily n,hmFamily n,huM n⟩),
    he.1,he.2.1,he.2.2.1,he.2.2.2,?_⟩
  intro P hPN hP t
  have hconv : Filter.Tendsto (fun n =>
      (restrictOperator period (Nat.le_succ q)).compLeftContinuous ℝ (Icc (0 : ℝ) S) (u n))
      Filter.atTop (𝓝 e) := by
    simpa only [restrict_eq_truncate] using he.1
  exact ⟨energyNorm_path_limit_bound period (Nat.le_succ q) hN S R B.full.radius_pos
      (K.operatorPath period) u e hconv (fun τ => 2*B.full.residual*Real.exp (3*C*τ.val))
      (fun n τ => (heFamily n τ).1) P hPN hP t,
    energyNorm_path_limit_bound period (Nat.le_succ q) hN S R B.full.radius_pos
      (K.operatorPath period) u e hconv (fun _ => Δ/2)
      (fun n τ => (heFamily n τ).2) P hPN hP t⟩

end EulerDriftGevreyInviscidEnergyCompactness
