/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Zeta.Basic

/-!
# The extremal test function has total mass one

The normalisation that makes `f₀` a probability density, and hence makes the Montgomery–Taylor
constant the value of the pair-correlation functional at its self-convolution rather than a
multiple of it.

The constant `√2 sin(1/√2)` in the denominator of `f₀` is exactly what the substitution
`x ↦ √2 x` produces, which is why the mass comes out at one on the nose.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory intervalIntegral

/-- The extremal test function vanishes off `[-1/2, 1/2]`. -/
private lemma extremalTest_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    extremalTest x = 0 := by
  rw [extremalTest, ite_eq_right]
  intro habs
  exact hx (abs_le.mp habs)

/-- **The extremal test function has total mass one.** -/
@[zz_tag "lem_f0_integral"]
theorem integral_extremalTest : ∫ x : ℝ, extremalTest x = 1 := by
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsin : 0 < Real.sin (1 / Real.sqrt 2) := sin_inv_sqrt_two_pos
  have hden : Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) ≠ 0 := ne_of_gt (mul_pos hs2 hsin)
  -- restrict to the support
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Icc (-(1/2) : ℝ) (1/2)) fun x hx => extremalTest_eq_zero_of_notMem hx]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  -- on the interval the function is the cosine quotient
  have hcongr : ∫ x in (-(1/2) : ℝ)..(1/2), extremalTest x
      = ∫ x in (-(1/2) : ℝ)..(1/2),
          Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)] at hx
    rw [extremalTest, ite_eq_left (abs_le.mpr hx)]
  rw [hcongr, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_left Real.cos (ne_of_gt hs2), integral_cos]
  -- √2 * (1/2) = 1/√2, so the bracket is 2 sin(1/√2)
  have hhalf : Real.sqrt 2 * (1 / 2) = 1 / Real.sqrt 2 := by
    rw [eq_div_iff (ne_of_gt hs2)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [show Real.sqrt 2 * (-(1/2) : ℝ) = -(Real.sqrt 2 * (1/2)) by ring, hhalf, Real.sin_neg]
  simp only [smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

end ZetaZeros
