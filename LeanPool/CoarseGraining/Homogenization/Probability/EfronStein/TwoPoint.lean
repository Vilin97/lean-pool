/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Two-point variance identity and a Jensen bound

Building blocks for the Efron–Stein inequality.

* `Homogenization.variance_eq_half_integral_sub_sq`: for a bounded measurable
  real random variable `X` on a probability space,
  `Var[X] = ½ ∫∫ (X a − X b)² dμ dμ`.
* `Homogenization.sq_integral_le_integral_sq`: Jensen's inequality in the
  form `(∫ X)² ≤ ∫ X²` for a bounded measurable `X` on a probability space.

Everything is stated for *bounded* observables, which makes all integrability
side conditions immediate; no `L²`-generality is attempted.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Homogenization

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

section Bounded

variable {X : Ω → ℝ} (hX : Measurable X) {M : ℝ} (hM : ∀ ω, |X ω| ≤ M)

include hX hM

/-- A bounded measurable function is `MemLp 2` on a probability (finite) measure. -/
theorem memLp_two_of_bound : MemLp X 2 μ :=
  memLp_of_bounded (Eventually.of_forall fun ω => abs_le.mp (hM ω)) hX.aestronglyMeasurable 2

/-- A bounded measurable function is integrable on a probability (finite) measure. -/
theorem integrable_of_bound : Integrable X μ :=
  (memLp_two_of_bound μ hX hM).integrable one_le_two

/-- The square of a bounded measurable function is integrable. -/
theorem integrable_sq_of_bound : Integrable (fun ω => (X ω) ^ 2) μ :=
  (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp (memLp_two_of_bound μ hX hM)

end Bounded

/-- **Two-point variance identity.** For a bounded measurable real random variable
`X` on a probability space, the variance equals one half of the mean squared
difference of two independent samples. -/
theorem variance_eq_half_integral_sub_sq {X : Ω → ℝ} (hX : Measurable X) {M : ℝ}
    (hM : ∀ ω, |X ω| ≤ M) :
    Var[X; μ] = (1 / 2) * ∫ a, ∫ b, (X a - X b) ^ 2 ∂μ ∂μ := by
  set m : ℝ := ∫ ω, X ω ∂μ with hm
  set s : ℝ := ∫ ω, (X ω) ^ 2 ∂μ with hs
  have hintX : Integrable X μ := integrable_of_bound μ hX hM
  have hintXsq : Integrable (fun ω => (X ω) ^ 2) μ := integrable_sq_of_bound μ hX hM
  -- inner integral, for each fixed `a`
  have hinner : ∀ a, ∫ b, (X a - X b) ^ 2 ∂μ = (X a) ^ 2 - 2 * (X a) * m + s := by
    intro a
    have hcongr : ∀ b, (X a - X b) ^ 2 = (X a) ^ 2 - (2 * X a) * X b + (X b) ^ 2 := by
      intro b; ring
    calc
      ∫ b, (X a - X b) ^ 2 ∂μ
          = ∫ b, ((X a) ^ 2 - (2 * X a) * X b + (X b) ^ 2) ∂μ := by
            simp_rw [hcongr]
      _ = (∫ _b, (X a) ^ 2 ∂μ) - (∫ b, (2 * X a) * X b ∂μ) + ∫ b, (X b) ^ 2 ∂μ := by
            rw [integral_add, integral_sub]
            · exact integrable_const _
            · exact hintX.const_mul _
            · exact (integrable_const _).sub (hintX.const_mul _)
            · exact hintXsq
      _ = (X a) ^ 2 - 2 * (X a) * m + s := by
            rw [integral_const, integral_const_mul]
            simp [hm, hs, mul_assoc]
  -- outer integral
  have houter :
      ∫ a, ∫ b, (X a - X b) ^ 2 ∂μ ∂μ = 2 * s - 2 * m ^ 2 := by
    simp_rw [hinner]
    have hcongr : ∀ a, (X a) ^ 2 - 2 * (X a) * m + s
        = (X a) ^ 2 - (2 * m) * X a + s := by intro a; ring
    calc
      ∫ a, ((X a) ^ 2 - 2 * (X a) * m + s) ∂μ
          = ∫ a, ((X a) ^ 2 - (2 * m) * X a + s) ∂μ := by simp_rw [hcongr]
      _ = (∫ a, (X a) ^ 2 ∂μ) - (∫ a, (2 * m) * X a ∂μ) + ∫ _a, s ∂μ := by
            rw [integral_add, integral_sub]
            · exact hintXsq
            · exact hintX.const_mul _
            · exact hintXsq.sub (hintX.const_mul _)
            · exact integrable_const _
      _ = 2 * s - 2 * m ^ 2 := by
            rw [integral_const, integral_const_mul]
            simp only [hm, hs, probReal_univ, smul_eq_mul]
            ring
  rw [houter, variance_eq_sub (memLp_two_of_bound μ hX hM)]
  simp only [Pi.pow_apply]
  rw [← hs, ← hm]
  ring

/-- **Jensen's inequality**, `(∫ X)² ≤ ∫ X²`, for a bounded measurable function on
a probability space. -/
theorem sq_integral_le_integral_sq {X : Ω → ℝ} (hX : Measurable X) {M : ℝ}
    (hM : ∀ ω, |X ω| ≤ M) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, (X ω) ^ 2 ∂μ := by
  have h := variance_nonneg X μ
  rw [variance_eq_sub (memLp_two_of_bound μ hX hM)] at h
  simp only [Pi.pow_apply] at h
  linarith

end Homogenization
