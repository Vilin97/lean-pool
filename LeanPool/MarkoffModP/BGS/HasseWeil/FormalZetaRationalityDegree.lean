/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaRationality

/-!
# Degree bounds in formal zeta rationality

The recurrence construction in `FormalZetaRationality` chooses its numerator
as a finite truncation.  This file exposes the resulting degree bound, which
is needed to turn a Riemann--Roch threshold into a uniform Hasse coefficient.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

/-- A normalized eventual step-one recurrence produces a numerator whose
degree is strictly smaller than the truncation length `N + 2`. -/
theorem exists_normalized_curveZetaRationalForm_with_natDegree_lt
    (Z : PowerSeries ℂ) (q N : ℕ)
    (hZ0 : PowerSeries.constantCoeff Z = 1)
    (hrec : ∀ n, N ≤ n →
      PowerSeries.coeff (n + 2) Z =
        ((q : ℂ) + 1) * PowerSeries.coeff (n + 1) Z -
          (q : ℂ) * PowerSeries.coeff n Z) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ P.natDegree < N + 2 ∧
        HasCurveZetaRationalForm Z q P := by
  let F := Z * curveZetaDenominator q
  have hzero : ∀ m, N + 2 ≤ m → PowerSeries.coeff m F = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hn : N ≤ N + n := Nat.le_add_right N n
    rw [show N + 2 + n = (N + n) + 2 by omega]
    rw [coeff_mul_curveZetaDenominator_succ_succ]
    rw [hrec (N + n) hn]
    ring
  let P := PowerSeries.trunc (N + 2) F
  have hform : HasCurveZetaRationalForm Z q P := by
    exact powerSeries_eq_coe_trunc_of_coeff_eq_zero F (N + 2) hzero
  have hdegree : P.natDegree < N + 2 := by
    simpa [P, show N + 2 = (N + 1) + 1 by omega] using
      (PowerSeries.natDegree_trunc_lt F (N + 1))
  have hconstant := congrArg PowerSeries.constantCoeff hform
  have hP0 : P.coeff 0 = 1 := by
    simpa [HasCurveZetaRationalForm, hZ0] using hconstant.symm
  exact ⟨P, hP0, hdegree, hform⟩

/-- The indexed recurrence likewise exposes the exact truncation-degree
bound `N + 2d`. -/
theorem exists_normalized_indexedCurveZetaRationalForm_with_natDegree_lt
    (Z : PowerSeries ℂ) (q d N : ℕ) (hd : 0 < d)
    (hZ0 : PowerSeries.constantCoeff Z = 1)
    (hrec : ∀ n, N ≤ n →
      PowerSeries.coeff (n + 2 * d) Z =
        ((q : ℂ) ^ d + 1) * PowerSeries.coeff (n + d) Z -
          (q : ℂ) ^ d * PowerSeries.coeff n Z) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ P.natDegree < N + 2 * d ∧
        HasIndexedCurveZetaRationalForm Z q d P := by
  let F := Z * indexedCurveZetaDenominator q d
  have hzero : ∀ m, N + 2 * d ≤ m → PowerSeries.coeff m F = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hn : N ≤ N + n := Nat.le_add_right N n
    rw [show N + 2 * d + n = (N + n) + 2 * d by omega]
    rw [coeff_mul_indexedCurveZetaDenominator]
    rw [hrec (N + n) hn]
    ring
  let P := PowerSeries.trunc (N + 2 * d) F
  have hform : HasIndexedCurveZetaRationalForm Z q d P := by
    exact powerSeries_eq_coe_trunc_of_coeff_eq_zero F (N + 2 * d) hzero
  have hlength : 0 < N + 2 * d := by omega
  have hdegree : P.natDegree < N + 2 * d := by
    have hpred : N + 2 * d - 1 + 1 = N + 2 * d := by omega
    simpa [P, hpred] using
      (PowerSeries.natDegree_trunc_lt F (N + 2 * d - 1))
  have hconstant := congrArg PowerSeries.constantCoeff hform
  have hP0 : P.coeff 0 = 1 := by
    simpa [HasIndexedCurveZetaRationalForm, indexedCurveZetaDenominator,
      hZ0, Nat.ne_of_gt hd] using hconstant.symm
  exact ⟨P, hP0, hdegree, hform⟩

end

end BGS.HasseWeil
