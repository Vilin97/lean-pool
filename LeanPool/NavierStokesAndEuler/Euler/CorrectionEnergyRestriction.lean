/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData

@[expose] public section

/-! The constructed higher nonlinear source and pressure restrict exactly to the actual lower mild
  equation. -/

noncomputable section

namespace EulerCorrectionEnergyRestriction

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerCorrectionOperators
    EulerSobolevTransport
  EulerCorrectionEnergyTime EulerCorrectionLowerData EulerTimeCorrectionSource
    EulerSobolevWordValueIdentity
  EulerTimeLp EulerVolterraConvolution EulerRegularizedTopBlocks
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual higher raw nonlinear time field restricts to the actual continuous source of the lower equation. -/
theorem rawTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (U : TimeLp T (SobolevSpace period (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
      (𝓝 U)) :
    (fun t => truncateOperator period q (rawTime period (by omega : 6 ≤ q+1) T hT D e U t))
      =ᵐ[timeMeasure T]
      extendPath T hT (rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e) := by
  have h := rawSourceTime_restriction period hq T hT (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear D.quadratic KL KQ D.approximation D.residual e (reindexMaximalTime period q T U)
    (reindexMaximalTime_restriction period T hT e U hU)
  filter_upwards [h] with t ht
  exact ht.trans (rawPath_lower period hq D KG KL KQ hG hL hQ e (projIcc 0 T hT t)).symm

/-- The actual full-order projected time forcing restricts to the literal lower mild source without a source-regularity premise. -/
theorem sourceTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (U : TimeLp T (SobolevSpace period (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
      (𝓝 U)) :
    (fun t => truncateOperator period q (sourceTime period (by omega : 6 ≤ q+1) T hT D e U t))
      =ᵐ[timeMeasure T]
      extendPath T hT (forcingPath period hq (lowerData period D KG KL KQ hG hL hQ) e) :=
  projectedTime_restriction period T hT D.metric KG D.κ D.direction D.coercivity D.coercivity_pos
    D.metric_pos
    (rawTime period (by omega : 6 ≤ q+1) T hT D e U)
    (extendPath T hT (rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e))
    (rawTime_restriction period hq T hT D KG KL KQ hG hL hQ e U hU)

/-- The actual full-order signed pressure restricts exactly to the continuous pressure in the lower correction equation. -/
theorem signedPressureTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (U : TimeLp T (SobolevSpace period (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
      (𝓝 U)) :
    (fun t => truncateOperator period q (signedPressureTime period (by omega : 6 ≤ q+1) T hT D e U
      t)) =ᵐ[timeMeasure T]
      extendPath T hT (pressurePath period hq (lowerData period D KG KL KQ hG hL hQ) e) :=
  pressureTime_restriction period T hT D.metric KG D.κ D.direction D.coercivity D.coercivity_pos
    D.metric_pos
    (rawTime period (by omega : 6 ≤ q+1) T hT D e U)
    (extendPath T hT (rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e))
    (rawTime_restriction period hq T hT D KG KL KQ hG hL hQ e U hU)

end EulerCorrectionEnergyRestriction
