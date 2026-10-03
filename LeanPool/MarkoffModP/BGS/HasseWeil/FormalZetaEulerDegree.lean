/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaEuler
public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaRationalityDegree

/-!
# Euler composition with numerator-degree bounds

This file combines the marked-divisor Euler recurrence with the truncation
degree bounds.  It is the degree-aware version of the compositions in
`FormalZetaEuler`.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

/-- Euler's recurrence and an eventual step-one divisor recurrence produce
a normalized standard numerator of degree `< N + 2`. -/
theorem exists_formalPointCountZeta_rational_with_natDegree_lt_of_effectiveDivisor_recurrences
    (A pointCount : ℕ → ℕ) (q N : ℕ)
    (hA0 : A 0 = 1)
    (hEuler : HasEffectiveDivisorPointCountRecurrence A pointCount)
    (hlinear : ∀ n, N ≤ n →
      (A (n + 2) : ℂ) =
        ((q : ℂ) + 1) * (A (n + 1) : ℂ) - (q : ℂ) * (A n : ℂ)) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ P.natDegree < N + 2 ∧
        HasCurveZetaRationalForm (formalPointCountZeta pointCount) q P := by
  obtain ⟨P, hP0, hPdegree, hP⟩ :=
    exists_normalized_curveZetaRationalForm_with_natDegree_lt
      (effectiveDivisorCountSeries A) q N
      (by simp [effectiveDivisorCountSeries, hA0])
      (by simpa [effectiveDivisorCountSeries] using hlinear)
  refine ⟨P, hP0, hPdegree, ?_⟩
  rw [← effectiveDivisorCountSeries_eq_formalPointCountZeta
    A pointCount hA0 hEuler]
  exact hP

/-- Before proving the divisor index is one, the same composition gives an
indexed numerator of degree `< N + 2d`. -/
theorem
  exists_formalPointCountZeta_indexed_rational_with_natDegree_lt_of_effectiveDivisor_recurrences
    (A pointCount : ℕ → ℕ) (q d N : ℕ) (hd : 0 < d)
    (hA0 : A 0 = 1)
    (hEuler : HasEffectiveDivisorPointCountRecurrence A pointCount)
    (hlinear : ∀ n, N ≤ n →
      (A (n + 2 * d) : ℂ) =
        ((q : ℂ) ^ d + 1) * (A (n + d) : ℂ) -
          (q : ℂ) ^ d * (A n : ℂ)) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ P.natDegree < N + 2 * d ∧
        HasIndexedCurveZetaRationalForm
          (formalPointCountZeta pointCount) q d P := by
  obtain ⟨P, hP0, hPdegree, hP⟩ :=
    exists_normalized_indexedCurveZetaRationalForm_with_natDegree_lt
      (effectiveDivisorCountSeries A) q d N hd
      (by simp [effectiveDivisorCountSeries, hA0])
      (by simpa [effectiveDivisorCountSeries] using hlinear)
  refine ⟨P, hP0, hPdegree, ?_⟩
  rw [← effectiveDivisorCountSeries_eq_formalPointCountZeta
    A pointCount hA0 hEuler]
  exact hP

end

end BGS.HasseWeil
