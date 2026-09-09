/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HeatGradientEnergy

@[expose] public section

/-! Integrated genuine heat gradient energy, with the source measured only in L². -/

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevLaplacian EulerSobolevHeatGenerator
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual integrated heat energy gains the full Laplacian in L² time without a source derivative in the bound. -/
theorem heat_laplacian_integral_bound (u : ℝ → SobolevSpace period 3)
    (f : ℝ → SobolevSpace period 1) (ν s t : ℝ) (hν : 0 < ν) (hst : s ≤ t)
    (hu : ContinuousOn u (Icc s t)) (hf : ContinuousOn f (Icc s t))
    (hd : ∀ r ∈ Ioo s t, ∀ i : Fin 4,
      HasDerivAt (fun a => value period (derivativeOperator period 2 i (u a)))
        (value period (derivativeOperator period 0 i (ν • laplacianOperator period 1 (u r) + f r)))
          r) :
    ν * (∫ r in s..t, ‖laplacianEvaluation period 3 (by norm_num) (u r)‖^2) ≤
      gradientEnergy period (restrictOperator period (by norm_num : 1 ≤ 3) (u s)) +
        ν⁻¹ * (∫ r in s..t, ‖value period (f r)‖^2) := by
  let G := fun r => gradientEnergy period (restrictOperator period (by norm_num : 1 ≤ 3) (u r))
  let L := fun r => ‖laplacianEvaluation period 3 (by norm_num) (u r)‖^2
  let F := fun r => ‖value period (f r)‖^2
  have hG : ContinuousOn G (Icc s t) :=
    (gradientEnergy_continuous period).comp_continuousOn
      ((restrictOperator period (by norm_num : 1 ≤ 3)).continuous.comp_continuousOn hu)
  have hL : ContinuousOn L (Icc s t) :=
    (((laplacianEvaluation period 3 (by norm_num)).continuous.comp_continuousOn hu).norm).pow 2
  have hF : ContinuousOn F (Icc s t) :=
    (((valueOperator period 1).continuous.comp_continuousOn hf).norm).pow 2
  have hLi : IntervalIntegrable L volume s t := hL.intervalIntegrable_of_Icc hst
  have hFi : IntervalIntegrable F volume s t := hF.intervalIntegrable_of_Icc hst
  have hφ : IntegrableOn (fun r => -ν * L r + ν⁻¹ * F r) (Icc s t) :=
    ((hL.const_mul (-ν)).add (hF.const_mul ν⁻¹)).integrableOn_Icc
  have hdiff : ∀ r ∈ Ioo s t, HasDerivAt G (deriv G r) r := by
    intro r hr
    exact (heat_gradient_energy_hasDerivAt period u (f r) ν r (hd r hr)).differentiableAt.hasDerivAt
  have hb : ∀ r ∈ Ioo s t, deriv G r ≤ -ν * L r + ν⁻¹ * F r := by
    intro r hr
    exact heat_gradient_energy_bound period u (f r) ν r hν (hd r hr)
  have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst hG
    (fun r hr => (hdiff r hr).hasDerivWithinAt) hφ hb
  rw [intervalIntegral.integral_add (hLi.const_mul (-ν)) (hFi.const_mul ν⁻¹),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hnonneg := gradientEnergy_nonneg period (restrictOperator period (by norm_num : 1 ≤ 3) (u t))
  change G t - G s ≤ -ν * (∫ r in s..t, L r) + ν⁻¹ * (∫ r in s..t, F r) at hi
  change 0 ≤ G t at hnonneg
  change ν * (∫ r in s..t, L r) ≤ G s + ν⁻¹ * (∫ r in s..t, F r)
  linarith

end EulerHeatGradientEnergy
