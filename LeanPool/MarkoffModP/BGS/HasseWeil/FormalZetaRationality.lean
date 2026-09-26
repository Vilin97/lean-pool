/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaTrace
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Formal zeta rationality from an eventual coefficient recurrence

This file isolates the algebraic last step in the divisor-count proof of
zeta rationality.  If the coefficients of a power series eventually satisfy
the recurrence with characteristic polynomial `(1 - T)(1 - qT)`, then
multiplication by that denominator has finite support.  Its truncation is
therefore an actual polynomial numerator.

No geometric or point-count hypothesis is used here.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

/-- Expanded form of the standard curve-zeta denominator. -/
theorem curveZetaDenominator_eq_quadratic (q : ℕ) :
    curveZetaDenominator q =
      1 - PowerSeries.C ((q : ℂ) + 1) * PowerSeries.X +
        PowerSeries.C (q : ℂ) * PowerSeries.X ^ 2 := by
  simp [curveZetaDenominator, linearPowerSeriesFactor]
  ring

/-- The coefficient of `Z(T)(1-T)(1-qT)` in terms of three consecutive
coefficients of `Z`. -/
theorem coeff_mul_curveZetaDenominator_succ_succ
    (Z : PowerSeries ℂ) (q n : ℕ) :
    PowerSeries.coeff (n + 2) (Z * curveZetaDenominator q) =
      PowerSeries.coeff (n + 2) Z -
        ((q : ℂ) + 1) * PowerSeries.coeff (n + 1) Z +
          (q : ℂ) * PowerSeries.coeff n Z := by
  rw [curveZetaDenominator_eq_quadratic]
  rw [show Z * (1 - PowerSeries.C ((q : ℂ) + 1) * PowerSeries.X +
          PowerSeries.C (q : ℂ) * PowerSeries.X ^ 2) =
        Z - PowerSeries.C ((q : ℂ) + 1) * (Z * PowerSeries.X) +
          PowerSeries.C (q : ℂ) * (Z * PowerSeries.X ^ 2) by ring]
  rw [map_add, map_sub]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  simp

/-- A power series whose coefficients vanish from `N` onward is exactly its
`N`-term polynomial truncation. -/
theorem powerSeries_eq_coe_trunc_of_coeff_eq_zero
    {R : Type*} [CommSemiring R] (F : PowerSeries R) (N : ℕ)
    (hzero : ∀ n, N ≤ n → PowerSeries.coeff n F = 0) :
    F = (PowerSeries.trunc N F : PowerSeries R) := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact hzero n (Nat.le_of_not_gt hn)

/-- An eventual recurrence with roots `1` and `q` produces a polynomial
curve-zeta numerator. -/
theorem exists_curveZetaRationalForm_of_eventual_coeff_recurrence
    (Z : PowerSeries ℂ) (q N : ℕ)
    (hrec : ∀ n, N ≤ n →
      PowerSeries.coeff (n + 2) Z =
        ((q : ℂ) + 1) * PowerSeries.coeff (n + 1) Z -
          (q : ℂ) * PowerSeries.coeff n Z) :
    ∃ P : Polynomial ℂ, HasCurveZetaRationalForm Z q P := by
  let F := Z * curveZetaDenominator q
  have hzero : ∀ m, N + 2 ≤ m → PowerSeries.coeff m F = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hn : N ≤ N + n := Nat.le_add_right N n
    rw [show N + 2 + n = (N + n) + 2 by omega]
    rw [coeff_mul_curveZetaDenominator_succ_succ]
    rw [hrec (N + n) hn]
    ring
  refine ⟨PowerSeries.trunc (N + 2) F, ?_⟩
  exact powerSeries_eq_coe_trunc_of_coeff_eq_zero F (N + 2) hzero

/-- Normalized constant coefficient is preserved by the recurrence
construction. -/
theorem exists_normalized_curveZetaRationalForm_of_eventual_coeff_recurrence
    (Z : PowerSeries ℂ) (q N : ℕ)
    (hZ0 : PowerSeries.constantCoeff Z = 1)
    (hrec : ∀ n, N ≤ n →
      PowerSeries.coeff (n + 2) Z =
        ((q : ℂ) + 1) * PowerSeries.coeff (n + 1) Z -
          (q : ℂ) * PowerSeries.coeff n Z) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ HasCurveZetaRationalForm Z q P := by
  obtain ⟨P, hP⟩ :=
    exists_curveZetaRationalForm_of_eventual_coeff_recurrence Z q N hrec
  refine ⟨P, ?_, hP⟩
  have hconstant := congrArg PowerSeries.constantCoeff hP
  simpa [HasCurveZetaRationalForm, hZ0] using hconstant.symm

/-- The denominator that occurs before proving that the divisor-degree index
is one.  An index `d` permits nonzero divisor coefficients only along residue
classes modulo `d`. -/
def indexedCurveZetaDenominator (q d : ℕ) : PowerSeries ℂ :=
  (1 - PowerSeries.X ^ d) *
    (1 - PowerSeries.C ((q : ℂ) ^ d) * PowerSeries.X ^ d)

/-- Rationality with a possibly nontrivial divisor-degree index. -/
def HasIndexedCurveZetaRationalForm
    (Z : PowerSeries ℂ) (q d : ℕ) (P : Polynomial ℂ) : Prop :=
  Z * indexedCurveZetaDenominator q d = (P : PowerSeries ℂ)

/-- Coefficient expansion for the indexed denominator. -/
theorem coeff_mul_indexedCurveZetaDenominator
    (Z : PowerSeries ℂ) (q d n : ℕ) :
    PowerSeries.coeff (n + 2 * d)
        (Z * indexedCurveZetaDenominator q d) =
      PowerSeries.coeff (n + 2 * d) Z -
        ((q : ℂ) ^ d + 1) * PowerSeries.coeff (n + d) Z +
          (q : ℂ) ^ d * PowerSeries.coeff n Z := by
  rw [indexedCurveZetaDenominator]
  rw [show Z * ((1 - PowerSeries.X ^ d) *
          (1 - PowerSeries.C ((q : ℂ) ^ d) * PowerSeries.X ^ d)) =
        Z - (Z * PowerSeries.X ^ d) -
          PowerSeries.C ((q : ℂ) ^ d) * (Z * PowerSeries.X ^ d) +
          PowerSeries.C ((q : ℂ) ^ d) *
            (Z * PowerSeries.X ^ (2 * d)) by ring]
  rw [map_add, map_sub, map_sub]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  rw [ite_eq_left (by omega : d ≤ n + 2 * d),
    ite_eq_left (by omega : 2 * d ≤ n + 2 * d)]
  simp only [show n + 2 * d - d = n + d by omega,
    show n + 2 * d - 2 * d = n by omega]
  ring

/-- An eventual step-`d` recurrence produces an indexed polynomial zeta
numerator.  The case `d = 1` is the standard curve denominator above. -/
theorem exists_indexedCurveZetaRationalForm_of_eventual_coeff_recurrence
    (Z : PowerSeries ℂ) (q d N : ℕ)
    (hrec : ∀ n, N ≤ n →
      PowerSeries.coeff (n + 2 * d) Z =
        ((q : ℂ) ^ d + 1) * PowerSeries.coeff (n + d) Z -
          (q : ℂ) ^ d * PowerSeries.coeff n Z) :
    ∃ P : Polynomial ℂ, HasIndexedCurveZetaRationalForm Z q d P := by
  let F := Z * indexedCurveZetaDenominator q d
  have hzero : ∀ m, N + 2 * d ≤ m → PowerSeries.coeff m F = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hn : N ≤ N + n := Nat.le_add_right N n
    rw [show N + 2 * d + n = (N + n) + 2 * d by omega]
    rw [coeff_mul_indexedCurveZetaDenominator]
    rw [hrec (N + n) hn]
    ring
  refine ⟨PowerSeries.trunc (N + 2 * d) F, ?_⟩
  exact powerSeries_eq_coe_trunc_of_coeff_eq_zero F (N + 2 * d) hzero

/-- Normalized indexed rationality. -/
theorem exists_normalized_indexedCurveZetaRationalForm_of_eventual_coeff_recurrence
    (Z : PowerSeries ℂ) (q d N : ℕ)
    (hd : 0 < d)
    (hZ0 : PowerSeries.constantCoeff Z = 1)
    (hrec : ∀ n, N ≤ n →
      PowerSeries.coeff (n + 2 * d) Z =
        ((q : ℂ) ^ d + 1) * PowerSeries.coeff (n + d) Z -
          (q : ℂ) ^ d * PowerSeries.coeff n Z) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ HasIndexedCurveZetaRationalForm Z q d P := by
  obtain ⟨P, hP⟩ :=
    exists_indexedCurveZetaRationalForm_of_eventual_coeff_recurrence
      Z q d N hrec
  refine ⟨P, ?_, hP⟩
  have hconstant := congrArg PowerSeries.constantCoeff hP
  simpa [HasIndexedCurveZetaRationalForm, indexedCurveZetaDenominator, hZ0,
    Nat.ne_of_gt hd]
    using hconstant.symm

end

end BGS.HasseWeil
