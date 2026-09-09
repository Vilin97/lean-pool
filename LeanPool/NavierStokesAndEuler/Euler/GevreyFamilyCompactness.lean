/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyStabilityBudget
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionFamilyCompactness

@[expose] public section

/-! Applying the concrete Gevrey budgets to a genuinely bounded viscous correction family. -/

noncomputable section

namespace EulerGevreyFamilyCompactness

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
    EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerQuadraticSource EulerGevreyStabilityBudget
    EulerCorrectionFamilyCompactness
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Concrete Gevrey and inverse-metric budgets turn a genuinely bounded correction family into its actual strong lower-order limit. -/
theorem exists_limit_of_gevrey_family {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (N : ℕ) (R : C(Icc (0 : ℝ) T,ℝ))
    (B : SpatialBudget period (by omega : 6 ≤ q+1) D N R) (K : MetricBudget period T hT D)
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n) (hν1 : ∀ n, ν n ≤ 1) (hνc : CauchySeq ν)
    (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period (q+1))) (M : ℝ)
    (huM : ∀ n, ‖u n‖ ≤ M) (hu0 : ∀ n, u n ⟨0,le_rfl,hT⟩=0)
    (hu : ∀ n t, u n t = quadraticDuhamel period (ν n) (hν n) hT le_rfl
      ((lowerData period D KG KL KQ hGq hLq hQq).coefficients period hq) 0 (u n) t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ n t, value period (u n t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ e : C(Icc (0 : ℝ) T,SobolevSpace period q),
      Filter.Tendsto (fun n => (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u
        n))
        Filter.atTop (𝓝 e) ∧
      e ⟨0,le_rfl,hT⟩=0 ∧ (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
        ‖e‖ ≤ M := by
  let Dlow := lowerData period D KG KL KQ hGq hLq hQq
  let Bstable := stabilityBudgetLower period hT D KG KL KQ hGq hLq hQq N R (by omega) B K
  have hcz : ∀ t, value period (Dlow.approximation t) ∈ divergenceFreeSpace period Dlow.κ
    Dlow.direction := by
    intro t
    exact hz t
  exact exists_correction_family_limit period hq T hT Dlow Bstable ν hν hν1 hνc u M huM hu0 hu hcz
    hud

end EulerGevreyFamilyCompactness
