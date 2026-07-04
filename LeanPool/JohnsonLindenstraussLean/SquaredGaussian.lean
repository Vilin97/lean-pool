/-
Copyright (c) 2026 claytomode. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: claytomode
-/
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The moment generating function of a squared standard Gaussian

This file proves the flagship analytic lemma of the development:
if `Z ~ N(0,1)` then for `t < 1/2`,
`E[exp (t · Z²)] = (1 - 2t)^(-1/2)`.

We phrase the right-hand side as `(√(1 - 2t))⁻¹`, which is `(1-2t)^(-1/2)`,
and which raises cleanly to the `k`-th power for the chi-squared MGF.

The proof reduces the moment generating function to a Gaussian integral via
`integral_gaussianReal_eq_integral_smul` and then evaluates it with
mathlib's `integral_gaussian`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace JL

/-- The standard Gaussian measure `N(0,1)` on `ℝ`. -/
noncomputable def stdGaussian : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure stdGaussian := by
  unfold stdGaussian; infer_instance

/-- The density of the standard Gaussian, written out. -/
lemma stdGaussian_pdf (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) := by
  rw [gaussianPDFReal]
  norm_num

/-- **Squared-Gaussian MGF.** For `t < 1/2`, the moment generating function of `Z²`
with `Z ~ N(0,1)` is `(1 - 2t)^(-1/2) = (√(1 - 2t))⁻¹`. -/
theorem sqGaussian_mgf {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun x => x ^ 2) stdGaussian t = (√(1 - 2 * t))⁻¹ := by
  have hb : (0 : ℝ) < 1 / 2 - t := by linarith
  -- Unfold the MGF as a Gaussian integral.
  rw [mgf, stdGaussian, integral_gaussianReal_eq_integral_smul (by norm_num)]
  -- Rewrite the integrand as a constant times a Gaussian `exp (-(1/2 - t) x²)`.
  have hexp : ∀ x : ℝ, -x ^ 2 / 2 + t * x ^ 2 = -(1 / 2 - t) * x ^ 2 := fun x => by ring
  have hint : (fun x : ℝ => gaussianPDFReal 0 1 x • rexp (t * x ^ 2))
      = (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-(1 / 2 - t) * x ^ 2)) := by
    funext x
    rw [stdGaussian_pdf, smul_eq_mul, mul_assoc, ← Real.exp_add, hexp]
  rw [hint, integral_const_mul, integral_gaussian]
  -- Now simplify `(√(2π))⁻¹ * √(π / (1/2 - t)) = (√(1 - 2t))⁻¹`.
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
  congr 1
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hb' : (1 / 2 - t) ≠ 0 := ne_of_gt hb
  field_simp

end JL
