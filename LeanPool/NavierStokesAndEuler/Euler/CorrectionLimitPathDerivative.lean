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
import LeanPool.NavierStokesAndEuler.Euler.CorrectionSourceRestriction
import LeanPool.NavierStokesAndEuler.Euler.MildEquationBridge

/-! The actual viscous derivative expressed using the identical lower-order nonlinear source. -/

section

/-! The actual viscous derivative expressed using the identical lower-order nonlinear source. -/

@[expose] public section

noncomputable section

namespace EulerCorrectionLimitDerivative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionSourceRestriction EulerQuadraticSource
    EulerVolterraConvolution EulerMildEquationBridge
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
theorem lower_mild_value_derivative {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
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
    HasDerivAt (fun x => value period (extendPath T hT u x))
      (ν • laplacianEvaluation period ((q+1)+1) (by omega) (u ⟨r,hr.1.le,hr.2.le⟩) +
        value period (((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply
          ⟨r,hr.1.le,hr.2.le⟩ (truncateOperator period (q+1) (u ⟨r,hr.1.le,hr.2.le⟩)))) r := by
  let τ : Icc (0 : ℝ) T := ⟨r,hr.1.le,hr.2.le⟩
  have hx := viscous_mild_hasDerivAt period (by omega : 2 ≤ q+1) ν hν T hT 0
    (D.coefficients period (by omega : 6 ≤ q+1)).apply
    (D.coefficients period (by omega : 6 ≤ q+1)).continuous u hsol r hr
  have hs := congrArg (value period (q := q)) (truncate_source period hq D KG KL KQ hG hL hQ τ (u
      τ))
  rw [value_truncateOperator] at hs
  apply hx.congr_deriv
  exact congrArg (fun v => ν • laplacianEvaluation period ((q+1)+1) (by omega) (u τ)+v) hs

end EulerCorrectionLimitDerivative

end
end

end

section

/-! A pointwise viscous derivative expressed as a continuous path. -/

@[expose] public section

noncomputable section

namespace EulerViscousPathDerivative

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator
  EulerViscosityDefect EulerViscosityCauchy EulerVolterraConvolution

variable (period : ℝ) [Fact (0 < period)]

/-- The actual pointwise viscous derivative equals evaluation of its continuous source path. -/
theorem hasDerivAt_path {s q : ℕ} (hs : 2 ≤ s) (ν T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (r : ℝ) (hr : r ∈ Ioo 0 T)
    (hd : HasDerivAt (fun x => value period (extendPath T hT u x))
      (ν • laplacianEvaluation period s hs (u ⟨r, hr.1.le, hr.2.le⟩) +
        value period (f ⟨r, hr.1.le, hr.2.le⟩)) r) :
    HasDerivAt (extendPath T hT (valuePath period T u))
      (extendPath T hT (viscousDefect period hs ν T u + valuePath period T f) r) r := by
  apply hd.congr_deriv
  change _ = (viscousDefect period hs ν T u + valuePath period T f) (projIcc 0 T hT r)
  rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
  rfl

end EulerViscousPathDerivative

end
end

end

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
