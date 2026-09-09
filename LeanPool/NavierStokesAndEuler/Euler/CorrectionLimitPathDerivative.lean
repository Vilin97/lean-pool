/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticSourceLimit
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityDefect
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityCauchy
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.CorrectionLimitDerivative
import LeanPool.NavierStokesAndEuler.Euler.ViscousPathDerivative

/-! The actual viscous derivative expressed using the identical lower-order nonlinear source. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionLimitPathDerivative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
   EulerQuadraticSource EulerQuadraticSourceLimit
  EulerViscosityDefect EulerViscosityCauchy EulerVolterraConvolution
      EulerSobolevHeatGenerator
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group on each actual Sobolev value space. -/
local instance limitDerivativeGroup (s : ℕ) : NormedAddCommGroup (SobolevSpace period s) :=
    inferInstance

/-- The inherited real normed space on each actual Sobolev value space. -/
local instance limitDerivativeSpace (s : ℕ) : NormedSpace ℝ (SobolevSpace period s) := inferInstance

/-- The actual derivative of a high-order mild correction equals viscosity plus the literal
lower-order nonlinear source. -/
theorem lower_mild_path_derivative {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (ν : ℝ) (hν : 0 < ν) (u : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (hsol : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl
      (D.coefficients period (by omega : 6 ≤ q + 1)) 0 u t)
    (r : ℝ) (hr : r ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT (valuePath period T u))
      (extendPath T hT (viscousDefect period (by omega : 2 ≤ (q+1)+1) ν T u +
        valuePath period T (sourcePath ((lowerData period D KG KL KQ hG hL hQ).coefficients period
            hq)
          ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u))) r) r := by
  exact EulerViscousPathDerivative.hasDerivAt_path period (by omega : 2 ≤ (q+1)+1) ν T hT u
    (sourcePath ((lowerData period D KG KL KQ hG hL hQ).coefficients period hq)
      ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)) r hr
    (EulerCorrectionLimitDerivative.lower_mild_value_derivative period hq T hT D KG KL KQ hG hL hQ
        ν hν u hsol r hr)

end EulerCorrectionLimitPathDerivative
