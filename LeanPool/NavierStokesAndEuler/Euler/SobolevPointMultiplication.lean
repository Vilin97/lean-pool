/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointEvaluation
public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction

/-! Pointwise evaluation of actual smooth coefficient multiplication in finite cylinder Sobolev
spaces. -/

@[expose] public section


noncomputable section

namespace EulerSobolevPointMultiplication

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevPointEvaluation
  EulerMetricTransport

variable (period : ℝ) [Fact (0 < period)]

/-- Bounded evaluation of a genuine Sobolev coefficient product equals the literal pointwise matrix
product. -/
theorem pointEvaluation_coefficient {q : ℕ} (hq : 3 ≤ q) (G : SmoothCoefficient period)
    (K : CoefficientJet period standardDirection q G) (u : SobolevSpace period q)
    (x : LiftDomain period) :
    pointEvaluation period x (restrictOperator period hq (coefficientSobolevOperator period K u)) =
      G.coefficient x (pointEvaluation period x (restrictOperator period hq u)) := by
  apply pointEvaluation_eq period x _
    (fun y => G.coefficient y (pointEvaluation period y (restrictOperator period hq u)))
  · exact (smoothField_continuous period G.coefficient G.smooth).clm_apply
      (representative_continuous period (restrictOperator period hq u))
  · simp only [value_restrictOperator, coefficientSobolevOperator_value]
    filter_upwards [G.operator_ae (value period u),
      representative_ae period (restrictOperator period hq u)] with y hG hu
    exact hG.trans (congrArg (G.coefficient y) hu)

end EulerSobolevPointMultiplication
