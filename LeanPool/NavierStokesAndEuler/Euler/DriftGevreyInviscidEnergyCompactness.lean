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
import LeanPool.NavierStokesAndEuler.Euler.DriftViscousCorrectionFamily
import LeanPool.NavierStokesAndEuler.Euler.GevreyEnergyPathLimit
import LeanPool.NavierStokesAndEuler.Euler.GevreyFamilyCompactness

/-! Drift-aware version: Actual strong inviscid compactness retaining the quantitative Gevrey metric
energies. -/

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
