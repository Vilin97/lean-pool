/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.MeasureTheory.Integral.CircleIntegral
import LeanPool.PoincareThreeBody.ChapterVILatticeReduction

/-!
# Finite Laurent coefficient extraction by a complex contour

Poincaré's §94 introduces a one-variable Laurent series and extracts its coefficients by
integrating around a circle.  This file verifies that contour extraction for finite Laurent
polynomials.  It is the complex-analytic counterpart of the finite lattice reduction in
`ChapterVILatticeReduction`.

The remaining §94 work is to justify exchanging the contour integral with an infinite Laurent
series on the annulus where it converges.
-/

noncomputable section

open Complex
open scoped BigOperators Real

namespace LeanPool.PoincareThreeBody

/-- The circle integral of an integer monomial is `2 * pi * I` in degree `-1` and zero in every
other degree. -/
theorem chapterVI_circleIntegral_zpow
    (exponent : ℤ) {radius : ℝ} (hradius : radius ≠ 0) :
    (∮ z in C(0, radius), z ^ exponent) =
      if exponent = -1 then 2 * Real.pi * I else 0 := by
  by_cases hexponent : exponent = -1
  · subst exponent
    rw [if_pos rfl]
    simp only [zpow_neg_one]
    simpa only [sub_zero] using circleIntegral.integral_sub_center_inv 0 hradius
  · rw [if_neg hexponent]
    simpa only [sub_zero] using
      circleIntegral.integral_sub_zpow_of_ne hexponent 0 0 radius

/-- A finite Laurent coefficient table. -/
abbrev ChapterVIFiniteLaurentTable := ℤ →₀ ℂ

/-- The standard coefficient-extraction integrand, already multiplied by `z⁻ᵏ⁻¹`. -/
def chapterVIFiniteCoefficientIntegrand
    (coefficients : ChapterVIFiniteLaurentTable) (coefficientIndex : ℤ) (z : ℂ) : ℂ :=
  coefficients.sum fun exponent coefficient ↦
    coefficient * z ^ (exponent - coefficientIndex - 1)

/-- Every monomial in the finite coefficient integrand is integrable on a nonzero circle. -/
theorem circleIntegrable_chapterVIFiniteCoefficientMonomial
    (coefficient : ℂ) (exponent coefficientIndex : ℤ)
    {radius : ℝ} (hradius : radius ≠ 0) :
    CircleIntegrable
      (fun z : ℂ ↦ coefficient * z ^ (exponent - coefficientIndex - 1)) 0 radius := by
  have hzero : (0 : ℂ) ∉ Metric.sphere 0 |radius| := by
    simp only [Metric.mem_sphere, dist_self]
    exact (abs_ne_zero.mpr hradius).symm
  have hpower : CircleIntegrable
      (fun z : ℂ ↦ (z - 0) ^ (exponent - coefficientIndex - 1)) 0 radius := by
    rw [circleIntegrable_sub_zpow_iff]
    exact Or.inr (Or.inr hzero)
  simpa only [sub_zero, smul_eq_mul] using
    (hpower.const_fun_smul (a := coefficient))

/-- The normalized circle integral extracts exactly one coefficient from a finite Laurent
polynomial.  This is the finite contour calculation underlying Poincaré's `Phi(z)` in §94. -/
theorem chapterVI_finiteLaurent_circleCoefficient
    (coefficients : ChapterVIFiniteLaurentTable) (coefficientIndex : ℤ)
    {radius : ℝ} (hradius : radius ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, radius),
          chapterVIFiniteCoefficientIntegrand coefficients coefficientIndex z) =
      coefficients coefficientIndex := by
  classical
  have hintegral :
      (∮ z in C(0, radius),
        chapterVIFiniteCoefficientIntegrand coefficients coefficientIndex z) =
        coefficients coefficientIndex * (2 * Real.pi * I) := by
    unfold chapterVIFiniteCoefficientIntegrand
    simp only [Finsupp.sum]
    rw [circleIntegral.integral_fun_sum]
    · simp_rw [circleIntegral.integral_const_mul, chapterVI_circleIntegral_zpow _ hradius]
      have hindex : ∀ exponent : ℤ,
          exponent - coefficientIndex - 1 = -1 ↔ exponent = coefficientIndex := by
        intro exponent
        omega
      simp_rw [hindex]
      by_cases hmem : coefficientIndex ∈ coefficients.support
      · rw [Finset.sum_eq_single coefficientIndex]
        · simp
        · intro exponent hexponent hne
          simp [hne]
        · intro hnotmem
          exact (hnotmem hmem).elim
      · have hcoefficient : coefficients coefficientIndex = 0 :=
          Finsupp.notMem_support_iff.mp hmem
        rw [hcoefficient, zero_mul]
        apply Finset.sum_eq_zero
        intro exponent hexponent
        have hne : exponent ≠ coefficientIndex := by
          intro hequal
          exact hmem (hequal ▸ hexponent)
        simp [hne]
    · intro exponent hexponent
      exact circleIntegrable_chapterVIFiniteCoefficientMonomial
        (coefficients exponent) exponent coefficientIndex hradius
  rw [hintegral]
  have hnormalization : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [mul_comm (coefficients coefficientIndex), ← mul_assoc,
    inv_mul_cancel₀ hnormalization, one_mul]

/-- After Poincaré's shear reduction, the same contour extracts the requested coefficient of the
resulting finite one-variable Laurent polynomial. -/
theorem chapterVIReducedCoefficient_circleIntegral
    (coefficients : ChapterVIFiniteCoefficientTable) (a c : ℤ) (parameter : ℂ)
    (coefficientIndex : ℤ)
    {radius : ℝ} (hradius : radius ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, radius),
          chapterVIFiniteCoefficientIntegrand
            (chapterVIReducedCoefficientTable coefficients a c parameter) coefficientIndex z) =
      chapterVIReducedCoefficientTable coefficients a c parameter coefficientIndex :=
  chapterVI_finiteLaurent_circleCoefficient _ _ hradius

end LeanPool.PoincareThreeBody
