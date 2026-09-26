/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaRationality
public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaUniqueness

/-!
# Euler recurrences for a formal effective-divisor zeta series

This file packages the exact formal boundary between the remaining
closed-place combinatorics and zeta rationality.  A coefficient sequence `A`
satisfies Euler's recurrence when marking one degree unit in an effective
divisor gives the convolution with extension point counts.  That recurrence
is precisely the coefficient form of `Z' = Z * pointCountDerivativeSeries`.

Together with the proved uniqueness and eventual-recurrence results, this
turns the two explicit coefficient identities into either the indexed or the
standard polynomial zeta numerator.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

/-- The formal power series with effective-divisor counts as coefficients. -/
def effectiveDivisorCountSeries (A : ℕ → ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (A n : ℂ)

/-- Euler's marked-effective-divisor recurrence.  The antidiagonal form is
exactly the multiplication formula for formal power series. -/
def HasEffectiveDivisorPointCountRecurrence
    (A pointCount : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    A (n + 1) * (n + 1) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        A ij.1 * pointCount (ij.2 + 1)

/-- Euler's recurrence is the formal point-count derivative identity. -/
theorem effectiveDivisorCountSeries_hasPointCountDerivative
    (A pointCount : ℕ → ℕ)
    (hrec : HasEffectiveDivisorPointCountRecurrence A pointCount) :
    HasFormalZetaPointCountDerivative
      (effectiveDivisorCountSeries A) pointCount := by
  rw [HasFormalZetaPointCountDerivative]
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul]
  simp only [effectiveDivisorCountSeries, PowerSeries.coeff_mk,
    pointCountDerivativeSeries]
  exact_mod_cast hrec n

/-- A normalized effective-divisor series satisfying Euler's recurrence is
the canonical exponential point-count zeta series. -/
theorem effectiveDivisorCountSeries_eq_formalPointCountZeta
    (A pointCount : ℕ → ℕ) (hA0 : A 0 = 1)
    (hrec : HasEffectiveDivisorPointCountRecurrence A pointCount) :
    effectiveDivisorCountSeries A = formalPointCountZeta pointCount := by
  apply eq_formalPointCountZeta_of_normalized_pointCountDerivative
  · simp [effectiveDivisorCountSeries, hA0]
  · exact effectiveDivisorCountSeries_hasPointCountDerivative A pointCount hrec

/-- Euler's recurrence and an eventual step-one divisor recurrence produce
the normalized standard curve-zeta numerator for the point-count series. -/
theorem exists_formalPointCountZeta_rational_of_effectiveDivisor_recurrences
    (A pointCount : ℕ → ℕ) (q N : ℕ)
    (hA0 : A 0 = 1)
    (hEuler : HasEffectiveDivisorPointCountRecurrence A pointCount)
    (hlinear : ∀ n, N ≤ n →
      (A (n + 2) : ℂ) =
        ((q : ℂ) + 1) * (A (n + 1) : ℂ) - (q : ℂ) * (A n : ℂ)) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        HasCurveZetaRationalForm (formalPointCountZeta pointCount) q P := by
  obtain ⟨P, hP0, hP⟩ :=
    exists_normalized_curveZetaRationalForm_of_eventual_coeff_recurrence
      (effectiveDivisorCountSeries A) q N
      (by simp [effectiveDivisorCountSeries, hA0])
      (by simpa [effectiveDivisorCountSeries] using hlinear)
  refine ⟨P, hP0, ?_⟩
  rw [← effectiveDivisorCountSeries_eq_formalPointCountZeta
    A pointCount hA0 hEuler]
  exact hP

/-- The corresponding indexed conclusion before the divisor-degree index is
proved to be one. -/
theorem exists_formalPointCountZeta_indexed_rational_of_effectiveDivisor_recurrences
    (A pointCount : ℕ → ℕ) (q d N : ℕ) (hd : 0 < d)
    (hA0 : A 0 = 1)
    (hEuler : HasEffectiveDivisorPointCountRecurrence A pointCount)
    (hlinear : ∀ n, N ≤ n →
      (A (n + 2 * d) : ℂ) =
        ((q : ℂ) ^ d + 1) * (A (n + d) : ℂ) -
          (q : ℂ) ^ d * (A n : ℂ)) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        HasIndexedCurveZetaRationalForm
          (formalPointCountZeta pointCount) q d P := by
  obtain ⟨P, hP0, hP⟩ :=
    exists_normalized_indexedCurveZetaRationalForm_of_eventual_coeff_recurrence
      (effectiveDivisorCountSeries A) q d N hd
      (by simp [effectiveDivisorCountSeries, hA0])
      (by simpa [effectiveDivisorCountSeries] using hlinear)
  refine ⟨P, hP0, ?_⟩
  rw [← effectiveDivisorCountSeries_eq_formalPointCountZeta
    A pointCount hA0 hEuler]
  exact hP

end

end BGS.HasseWeil
