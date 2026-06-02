/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib.Tactic.Common
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Homotopy.Basic

/-!
# Winding Number from PV Integral Limit

Convert a Tendsto result for the PV integral into a generalized winding number value.
This is the final step shared by all winding number computations.

## Main results

* `gWN_eq_of_pv_tendsto` — general: gWN = L / (2πi) from Tendsto
* `gWN_eq_neg_half_of_pv_tendsto` — specialized: L = -πi implies gWN = -1/2
* `gWN_eq_neg_sixth_of_pv_tendsto` — specialized: L = -πi/3 implies gWN = -1/6
-/

open Complex

namespace ContourIntegral

/-- If the PV integral of (γ(t) - s)⁻¹ · deriv(γ - s)(t) tends to L as ε → 0⁺,
then `generalizedWindingNumber' γ a b s = L / (2 * π * I)`. -/
theorem gWN_eq_of_pv_tendsto (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) (L : ℂ)
    (h : Filter.Tendsto
      (fun ε => ∫ t in a..b,
        if (ε < ‖(γ t - s : ℂ) - 0‖) then (γ t - s)⁻¹ * deriv (fun t => γ t - s) t else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    generalizedWindingNumber' γ a b s = L / (2 * Real.pi * I) := by
  have key : cauchyPrincipalValue' (·⁻¹) (fun t => γ t - s) a b 0 = L := h.limUnder_eq
  simp only [generalizedWindingNumber', key, mul_comm, div_eq_mul_inv]

/-- Specialized version: if the PV integral tends to -(π * I), then gWN = -1/2. -/
theorem gWN_eq_neg_half_of_pv_tendsto (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (h : Filter.Tendsto
      (fun ε => ∫ t in a..b,
        if (ε < ‖(γ t - s : ℂ) - 0‖) then (γ t - s)⁻¹ * deriv (fun t => γ t - s) t else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.pi * I)))) :
    generalizedWindingNumber' γ a b s = -1/2 := by
  have key : cauchyPrincipalValue' (·⁻¹) (fun t => γ t - s) a b 0 = -(Real.pi * I) :=
    h.limUnder_eq
  simp only [generalizedWindingNumber', key]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-- Specialized version: if the PV integral tends to -(π / 3 * I), then gWN = -1/6. -/
theorem gWN_eq_neg_sixth_of_pv_tendsto (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (h : Filter.Tendsto
      (fun ε => ∫ t in a..b,
        if (ε < ‖(γ t - s : ℂ) - 0‖) then (γ t - s)⁻¹ * deriv (fun t => γ t - s) t else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.pi / 3 * I)))) :
    generalizedWindingNumber' γ a b s = -1/6 := by
  have key : cauchyPrincipalValue' (·⁻¹) (fun t => γ t - s) a b 0 = -(Real.pi / 3 * I) :=
    h.limUnder_eq
  simp only [generalizedWindingNumber', key]
  field_simp [Real.pi_ne_zero, I_ne_zero]
  norm_num

end ContourIntegral
