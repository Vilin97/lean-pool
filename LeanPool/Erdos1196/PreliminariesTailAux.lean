/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc
-/
import LeanPool.Erdos1196.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation

/-!
# Auxiliary tail lemmas for primitive sets above `x`

This file contains the standalone calculus lemmas reused in the proof of `tailEstimate`.
Its main output is a small API for the model kernels `1 / (t log(ct)^2)` and
`2 / (t log(ct)^3)`: each kernel is integrable on an admissible tail, and its tail integral can
be computed exactly.

## Main statements

* `integrableOn_Ioi_inv_log_sq`
* `integral_Ioi_inv_log_sq`
* `integrableOn_Ioi_two_inv_log_cube`
* `integral_Ioi_two_inv_log_cube`
-/

open scoped ArithmeticFunction BigOperators Topology
open Filter MeasureTheory

namespace PrimitiveSetsAboveX

/--
The logarithmic antiderivative underlying `tailEstimate` has derivative
`-1 / (t log(ct)^2)`.
-/
lemma hasDerivAt_inv_log_mul {c t : ℝ} (hc : 0 < c) (hct : 1 < c * t) :
    HasDerivAt (fun u => (Real.log (c * u))⁻¹)
      (-(1 / (t * Real.log (c * t) ^ 2))) t := by
  have hmul : HasDerivAt (fun u => c * u) c t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul c
  have hlog : HasDerivAt (fun u => Real.log (c * u)) ((c * t)⁻¹ * c) t :=
    (Real.hasDerivAt_log (show c * t ≠ 0 by positivity)).comp t hmul
  have hlog_ne : Real.log (c * t) ≠ 0 :=
    Real.log_ne_zero.mpr ⟨by linarith, by constructor <;> linarith⟩
  convert hlog.inv hlog_ne using 1
  field_simp

/--
Squaring the inverse logarithm gives the exact derivative
`-2 / (t log(ct)^3)`.
-/
lemma hasDerivAt_inv_log_sq_mul {c t : ℝ} (hc : 0 < c) (hct : 1 < c * t) :
    HasDerivAt (fun u => (Real.log (c * u))⁻¹ ^ 2)
      (-(2 / (t * Real.log (c * t) ^ 3))) t := by
  have h := (hasDerivAt_inv_log_mul hc hct).pow 2
  convert h using 1
  ring

/-- The logarithmic kernel `1 / (t log(ct)^2)` is integrable on every admissible tail, and its
integral is exactly `1 / log(cy)`. -/
private lemma integrableOn_Ioi_inv_log_sq_and_integral_eq {c y : ℝ} (hc : 0 < c)
    (hy : 1 < c * y) :
    IntegrableOn (fun t => (1 : ℝ) / (t * Real.log (c * t) ^ 2)) (Set.Ioi y) ∧
      ∫ t in Set.Ioi y, (1 : ℝ) / (t * Real.log (c * t) ^ 2) = (Real.log (c * y))⁻¹ := by
  have hderiv : ∀ x ∈ Set.Ici y, HasDerivAt (fun u => (Real.log (c * u))⁻¹)
      (-(1 / (x * Real.log (c * x) ^ 2))) x := by
    intro x hx
    apply hasDerivAt_inv_log_mul hc
    have hxy : y ≤ x := hx
    have hcx : c * y ≤ c * x := mul_le_mul_of_nonneg_left hxy hc.le
    exact lt_of_lt_of_le hy hcx
  have hlim_log : Tendsto (fun u => Real.log (c * u)) atTop atTop := by
    have hmul : Tendsto (fun u : ℝ => c * u) atTop atTop := by
      simpa [mul_comm] using tendsto_id.const_mul_atTop' hc
    exact Real.tendsto_log_atTop.comp hmul
  have hlim : Tendsto (fun u => (Real.log (c * u))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hlim_log
  have hint : IntegrableOn (fun x => -(1 / (x * Real.log (c * x) ^ 2))) (Set.Ioi y) := by
    refine integrableOn_Ioi_deriv_of_nonpos' hderiv ?_ hlim
    intro x hx
    have hxy : y < x := hx
    have hcx : c * y < c * x := mul_lt_mul_of_pos_left hxy hc
    have hx' : 1 < c * x := lt_trans hy hcx
    have hnonneg : 0 ≤ 1 / (x * Real.log (c * x) ^ 2) := by
      have hx0 : 0 < x := by nlinarith [hc, hx']
      have hlog : 0 < Real.log (c * x) := Real.log_pos hx'
      positivity
    linarith
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  refine ⟨?_, ?_⟩
  · simpa [integrableOn_neg_iff] using hint
  · have hneg := congrArg Neg.neg hmain
    simpa [sub_eq_add_neg, integral_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hneg

/-- The logarithmic kernel `1 / (t log(ct)^2)` is integrable on every admissible tail. -/
lemma integrableOn_Ioi_inv_log_sq {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    IntegrableOn (fun t => (1 : ℝ) / (t * Real.log (c * t) ^ 2)) (Set.Ioi y) :=
  (integrableOn_Ioi_inv_log_sq_and_integral_eq hc hy).1

/-- The integral of `1 / (t log(ct)^2)` over a tail is exactly `1 / log(cy)`. -/
lemma integral_Ioi_inv_log_sq {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    ∫ t in Set.Ioi y, (1 : ℝ) / (t * Real.log (c * t) ^ 2) = (Real.log (c * y))⁻¹ :=
  (integrableOn_Ioi_inv_log_sq_and_integral_eq hc hy).2

/-- The cubic logarithmic kernel `2 / (t log(ct)^3)` is integrable on every admissible tail, and
its integral equals the square of the inverse logarithm. -/
private lemma integrableOn_Ioi_two_inv_log_cube_and_integral_eq {c y : ℝ} (hc : 0 < c)
    (hy : 1 < c * y) :
    IntegrableOn (fun t => 2 / (t * Real.log (c * t) ^ 3)) (Set.Ioi y) ∧
      ∫ t in Set.Ioi y, 2 / (t * Real.log (c * t) ^ 3) = (Real.log (c * y))⁻¹ ^ 2 := by
  have hderiv : ∀ x ∈ Set.Ici y, HasDerivAt (fun u => (Real.log (c * u))⁻¹ ^ 2)
      (-(2 / (x * Real.log (c * x) ^ 3))) x := by
    intro x hx
    apply hasDerivAt_inv_log_sq_mul hc
    have hxy : y ≤ x := hx
    have hcx : c * y ≤ c * x := mul_le_mul_of_nonneg_left hxy hc.le
    exact lt_of_lt_of_le hy hcx
  have hlim_log : Tendsto (fun u => Real.log (c * u)) atTop atTop := by
    have hmul : Tendsto (fun u : ℝ => c * u) atTop atTop := by
      simpa [mul_comm] using tendsto_id.const_mul_atTop' hc
    exact Real.tendsto_log_atTop.comp hmul
  have hlim : Tendsto (fun u => (Real.log (c * u))⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hlim_log).pow 2
  have hint : IntegrableOn (fun x => -(2 / (x * Real.log (c * x) ^ 3))) (Set.Ioi y) := by
    refine integrableOn_Ioi_deriv_of_nonpos' hderiv ?_ hlim
    intro x hx
    have hxy : y < x := hx
    have hcx : c * y < c * x := mul_lt_mul_of_pos_left hxy hc
    have hx' : 1 < c * x := lt_trans hy hcx
    have hnonneg : 0 ≤ 2 / (x * Real.log (c * x) ^ 3) := by
      have hx0 : 0 < x := by nlinarith [hc, hx']
      have hlog : 0 < Real.log (c * x) := Real.log_pos hx'
      positivity
    linarith
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  refine ⟨?_, ?_⟩
  · simpa [integrableOn_neg_iff] using hint
  · have hneg := congrArg Neg.neg hmain
    simpa [sub_eq_add_neg, integral_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hneg

/-- The cubic logarithmic kernel `2 / (t log(ct)^3)` is integrable on every admissible tail. -/
lemma integrableOn_Ioi_two_inv_log_cube {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    IntegrableOn (fun t => 2 / (t * Real.log (c * t) ^ 3)) (Set.Ioi y) :=
  (integrableOn_Ioi_two_inv_log_cube_and_integral_eq hc hy).1

/-- The integral of `2 / (t log(ct)^3)` over a tail equals the square of the inverse logarithm. -/
lemma integral_Ioi_two_inv_log_cube {c y : ℝ} (hc : 0 < c) (hy : 1 < c * y) :
    ∫ t in Set.Ioi y, 2 / (t * Real.log (c * t) ^ 3) = (Real.log (c * y))⁻¹ ^ 2 :=
  (integrableOn_Ioi_two_inv_log_cube_and_integral_eq hc hy).2

end PrimitiveSetsAboveX
