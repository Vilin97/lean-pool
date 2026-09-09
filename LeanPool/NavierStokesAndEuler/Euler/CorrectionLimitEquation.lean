/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ViscosityDefect
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.CorrectionLimitPathDerivative
import LeanPool.NavierStokesAndEuler.Euler.IntegralPathLimit
import LeanPool.NavierStokesAndEuler.Euler.ViscousSourcePathLimit

/-! The literal inviscid correction equation follows from the actual strongly convergent viscous
family. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionLimitEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
   EulerQuadraticSource EulerQuadraticSourceLimit
      EulerIntegralPathLimit
   EulerViscosityDefect EulerViscosityCauchy EulerVolterraConvolution
   EulerSobolevHeatGenerator EulerCorrectionLimitPathDerivative
   EulerViscousSourcePathLimit
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group on each actual Sobolev value space. -/
local instance limitEquationGroup (s : ℕ) : NormedAddCommGroup (SobolevSpace period s) :=
    inferInstance

/-- The inherited real normed space on each actual Sobolev value space. -/
local instance limitEquationSpace (s : ℕ) : NormedSpace ℝ (SobolevSpace period s) := inferInstance

/-- A genuine bounded viscous family converging one Sobolev order lower solves the actual inviscid
correction equation at the limit.
The nonlinear source restriction and convergence, the vanishing viscosity term, and the integral
passage are proved internally. -/
theorem correction_limit_equation {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (M : ℝ) (huM : ∀ n, ‖u n‖ ≤ M)
    (hconv : Filter.Tendsto (fun n => (truncateOperator period (q + 1)).compLeftContinuous ℝ (Icc (0
        : ℝ) T) (u n))
      Filter.atTop (𝓝 e))
    (hsol : ∀ n t, u n t = quadraticDuhamel period (viscositySequence n) (viscositySequence_pos n)
        hT le_rfl
      (D.coefficients period (by omega : 6 ≤ q + 1)) 0 (u n) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT e r))
      (value period (((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply
        ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩))) t := by
  let Dlow := lowerData period D KG KL KQ hG hL hQ
  let g := valuePath period T (sourcePath (Dlow.coefficients period hq) e)
  let f := fun n => viscousSourcePath period (by omega : 2 ≤ (q+1)+1)
    (viscositySequence n) T (Dlow.coefficients period hq) (u n)
  have hf : Filter.Tendsto f Filter.atTop (𝓝 g) :=
    viscousSourcePath_tendsto period (by omega : 2 ≤ (q+1)+1) T
      (Dlow.coefficients period hq) u e M huM hconv
  have huval := valuePath_tendsto_of_truncate period T u e hconv
  have hd : ∀ n r, r ∈ Ioo 0 T → HasDerivAt (extendPath T hT (valuePath period T (u n)))
      (extendPath T hT (f n) r) r := by
    intro n r hr
    exact lower_mild_path_derivative period hq T hT D KG KL KQ hG hL hQ
      (viscositySequence n) (viscositySequence_pos n) (u n) (hsol n) r hr
  have heq : ∀ τ, valuePath period T e τ = valuePath period T e ⟨0,le_rfl,hT⟩ +
      pathIntegralOperator T hT 0 τ.val g :=
    integral_equation_limit T hT (fun n => valuePath period T (u n)) f (valuePath period T e) g
        huval hf
      (fun n => integral_equation_of_hasDerivAt T hT (valuePath period T (u n)) (f n) (hd n))
  have hder := hasDerivAt_of_integral_equation T hT (valuePath period T e) g heq t ht
  change HasDerivAt (fun r => value period (extendPath T hT e r))
    (value period ((Dlow.coefficients period hq).apply (projIcc 0 T hT t) (e (projIcc 0 T hT t))))
        t at hder
  rw [projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩] at hder
  exact hder

end EulerCorrectionLimitEquation
