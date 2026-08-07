/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# The lattice reduction in Poincaré's Chapter VI, §94

Section 94 of Volume I starts with a Fourier series in two mean anomalies and studies its
coefficients along an affine ray

`(m₁, m₂) = (a n + b, c n + d)`.

Poincaré makes a monomial change of variables for which the exponent of the integration variable
is `c m₁ - a m₂`.  Coprimality of `a` and `c` implies that fixing this exponent to
`c b - a d` selects exactly the affine ray above.  This file verifies that Diophantine step and
the corresponding coefficient extraction for a finite two-variable Fourier polynomial.

The finite-support restriction keeps this algebraic reduction independent of convergence and
contour integration.  Passing to Poincaré's analytic Fourier series requires summability and
complex contour arguments, which belong to later stages of the Chapter VI formalization.
-/

noncomputable section

open scoped BigOperators

namespace LeanPool.PoincareThreeBody

/-- The exponent of Poincaré's auxiliary integration variable after the §94 monomial change of
variables. -/
def chapterVIShearExponent (a c : ℤ) (frequency : ℤ × ℤ) : ℤ :=
  c * frequency.1 - a * frequency.2

/-- Every point on the affine frequency ray has the same shear exponent. -/
theorem chapterVIShearExponent_affineRay
    (a c b d n : ℤ) :
    chapterVIShearExponent a c (a * n + b, c * n + d) = c * b - a * d := by
  unfold chapterVIShearExponent
  ring_nf

/-- The Diophantine core of §94: when `a` and `c` are coprime and `a` is nonzero, the level set of
`c m₁ - a m₂` through `(b,d)` is exactly the affine lattice ray
`(a n + b, c n + d)`. -/
theorem chapterVIShearExponent_eq_iff_mem_affineRay
    {a c b d m₁ m₂ : ℤ}
    (ha : a ≠ 0) (hcoprime : Int.gcd a c = 1) :
    chapterVIShearExponent a c (m₁, m₂) = c * b - a * d ↔
      ∃ n : ℤ, m₁ = a * n + b ∧ m₂ = c * n + d := by
  constructor
  · intro hexponent
    have hproduct : c * (m₁ - b) = a * (m₂ - d) := by
      unfold chapterVIShearExponent at hexponent
      linarith
    have hadivides : a ∣ c * (m₁ - b) := by
      rw [hproduct]
      exact dvd_mul_right a (m₂ - d)
    have hadifference : a ∣ m₁ - b :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hadivides hcoprime
    rcases hadifference with ⟨n, hn⟩
    refine ⟨n, ?_, ?_⟩
    · linarith
    · have hcancel : a * (c * n) = a * (m₂ - d) := by
        calc
          a * (c * n) = c * (a * n) := by ring_nf
          _ = c * (m₁ - b) := by rw [hn]
          _ = a * (m₂ - d) := hproduct
      have : c * n = m₂ - d := mul_left_cancel₀ ha hcancel
      linarith
  · rintro ⟨n, rfl, rfl⟩
    exact chapterVIShearExponent_affineRay a c b d n

/-- A finite coefficient table for a Fourier polynomial in two angles. -/
abbrev ChapterVIFiniteCoefficientTable := (ℤ × ℤ) →₀ ℂ

/-- The finite Fourier polynomial represented by a coefficient table. -/
def chapterVIFiniteFourierPolynomial
    (coefficients : ChapterVIFiniteCoefficientTable) (firstAngle secondAngle : ℂ) : ℂ :=
  coefficients.sum fun frequency coefficient ↦
    coefficient * Complex.exp
      (Complex.I * (frequency.1 * firstAngle + frequency.2 * secondAngle))

/-- The finite one-variable coefficient table obtained after Poincaré's shear substitution.
The second complex variable remains as a parameter. -/
def chapterVIReducedCoefficientTable
    (coefficients : ChapterVIFiniteCoefficientTable) (a c : ℤ) (parameter : ℂ) : ℤ →₀ ℂ :=
  coefficients.sum fun frequency coefficient ↦
    Finsupp.single (chapterVIShearExponent a c frequency)
      (coefficient * Complex.exp (Complex.I * frequency.2 * parameter))

/-- Poincaré's linearized §94 substitution turns a finite two-angle Fourier polynomial into the
one-variable polynomial with shear-indexed coefficients. -/
theorem chapterVIFiniteFourierPolynomial_substitution
    (coefficients : ChapterVIFiniteCoefficientTable)
    (a c : ℤ) (parameter integrationVariable : ℂ) :
    chapterVIFiniteFourierPolynomial coefficients
        (c * integrationVariable) (-a * integrationVariable + parameter) =
      (chapterVIReducedCoefficientTable coefficients a c parameter).sum
        fun exponent coefficient ↦
          coefficient * Complex.exp (Complex.I * exponent * integrationVariable) := by
  classical
  unfold chapterVIFiniteFourierPolynomial chapterVIReducedCoefficientTable
  rw [Finsupp.sum_sum_index]
  · apply Finsupp.sum_congr
    intro frequency hfrequency
    rw [Finsupp.sum_single_index (by simp)]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    unfold chapterVIShearExponent
    push_cast
    ring_nf
  · simp
  · intro exponent first second
    ring_nf

/-- The finite sum of the weighted coefficients on one affine ray. -/
def chapterVIAffineRayCoefficientSum
    (coefficients : ChapterVIFiniteCoefficientTable)
    (a c b d : ℤ) (parameter : ℂ) : ℂ := by
  classical
  exact ∑ frequency ∈ coefficients.support with
      ∃ n : ℤ,
        frequency.1 = a * n + b ∧ frequency.2 = c * n + d,
    coefficients frequency *
      Complex.exp (Complex.I * frequency.2 * parameter)

/-- The coefficient of the shear exponent through `(b,d)` is the sum of precisely those original
coefficients whose frequencies lie on the affine ray `(a n + b, c n + d)`.

This is the finite coefficient-extraction statement underlying Poincaré's contour integral
`Phi(z)` in §94. -/
theorem chapterVIReducedCoefficient_eq_sum_affineRay
    (coefficients : ChapterVIFiniteCoefficientTable)
    {a c b d : ℤ} (parameter : ℂ)
    (ha : a ≠ 0) (hcoprime : Int.gcd a c = 1) :
    chapterVIReducedCoefficientTable coefficients a c parameter (c * b - a * d) =
      chapterVIAffineRayCoefficientSum coefficients a c b d parameter := by
  classical
  unfold chapterVIReducedCoefficientTable chapterVIAffineRayCoefficientSum
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  simp only [Finsupp.sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  simp only [chapterVIShearExponent_eq_iff_mem_affineRay ha hcoprime]

end LeanPool.PoincareThreeBody
