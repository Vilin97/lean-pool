/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
/-!
# Valuations of standard Lubin--Tate iterates at a primitive point

At primitive level `n + 1`, the `i`-fold standard Lubin--Tate iterate has
normalized additive valuation `q ^ i` for `i ≤ n`.  The proof uses the
two-term formula

`f(y) = y ^ q + π y`.

The first summand has valuation `q ^ (i + 1)`.  The second has strictly
larger valuation because the image of the base uniformizer has valuation
equal to the totally ramified level degree `(q - 1) q ^ n`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The `i`-fold standard polynomial iterate, evaluated at the primitive
point in the complete level valuation ring. -/
noncomputable def standardLubinTatePrimitivePointIterateInteger
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  Polynomial.eval₂
    (standardLubinTateLevelCoefficientHom hπ n)
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePolynomialIterate F π i)

/-- The zeroth iterate is the primitive point itself. -/
@[simp]
theorem standardLubinTatePrimitivePointIterateInteger_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTatePrimitivePointIterateInteger hπ n 0 =
      standardLubinTatePrimitivePointInteger hπ n := by
  simp [standardLubinTatePrimitivePointIterateInteger]

/-- One more iterate is evaluation of `y ↦ y ^ q + π y`. -/
theorem standardLubinTatePrimitivePointIterateInteger_succ
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) :
    standardLubinTatePrimitivePointIterateInteger hπ n (i + 1) =
      standardLubinTatePrimitivePointIterateInteger hπ n i ^
          Nat.card F.residueField +
        standardLubinTateLevelCoefficientHom hπ n π *
          standardLubinTatePrimitivePointIterateInteger hπ n i := by
  rw [standardLubinTatePrimitivePointIterateInteger,
    standardLubinTatePolynomialIterate_succ,
    Polynomial.eval₂_comp,
    standardLubinTatePolynomial_formula,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_mul,
    Polynomial.eval₂_C]
  simp only [Polynomial.eval₂_X, standardLubinTatePrimitivePointIterateInteger]

/-- Before the annihilating level, the evaluated iterates have exact
normalized additive valuations `1, q, ..., q ^ n`. -/
theorem standardLubinTatePrimitivePointIterateInteger_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) (hi : i ≤ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTatePrimitivePointIterateInteger hπ n i) =
      (Nat.card F.residueField ^ i : ℕ) := by
  induction i with
  | zero =>
      simpa using
        standardLubinTatePrimitivePointInteger_addVal hπ n
  | succ i ih =>
      let target := standardLubinTateLevelCompleteDVF hπ n
      let q := Nat.card F.residueField
      let d := (q - 1) * q ^ n
      let y := standardLubinTatePrimitivePointIterateInteger hπ n i
      have hi' : i ≤ n := Nat.le_trans (Nat.le_succ i) hi
      have hiy :
          IsDiscreteValuationRing.addVal target.valuationSubring y =
            (q ^ i : ℕ) := by
        exact ih hi'
      have hπval :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (standardLubinTateLevelCoefficientHom hπ n π) =
            (d : ℕ) := by
        simpa [target, q, d, standardLubinTateLevelCoefficientHom] using
          standardLubinTateBaseUniformizerInteger_map_addVal hπ n
      have hpow :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (y ^ q) =
            (q ^ (i + 1) : ℕ) := by
        rw [IsDiscreteValuationRing.addVal_pow, hiy]
        simp [nsmul_eq_mul, pow_succ, Nat.mul_comm]
      have hmul :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (standardLubinTateLevelCoefficientHom hπ n π * y) =
            (d + q ^ i : ℕ) := by
        rw [IsDiscreteValuationRing.addVal_mul, hπval, hiy]
        rfl
      have hqone : 1 < q := by
        exact Finite.one_lt_card
      have hqpos : 0 < q := Nat.zero_lt_one.trans hqone
      have hpowle : q ^ (i + 1) ≤ q ^ n :=
        Nat.pow_le_pow_right hqpos hi
      have hqsub : 1 ≤ q - 1 := by
        omega
      have hdegreele : q ^ n ≤ d := by
        calc
          q ^ n = 1 * q ^ n := by simp
          _ ≤ (q - 1) * q ^ n :=
            Nat.mul_le_mul_right (q ^ n) hqsub
      have htailpos : 0 < q ^ i := Nat.pow_pos hqpos
      have hnatlt : q ^ (i + 1) < d + q ^ i :=
        hpowle.trans_lt
          (hdegreele.trans_lt (Nat.lt_add_of_pos_right htailpos))
      have henatlt :
          (q ^ (i + 1) : ℕ∞) < (d + q ^ i : ℕ) := by
        exact_mod_cast hnatlt
      have hdistinct :
          IsDiscreteValuationRing.addVal target.valuationSubring
                (y ^ q) ≠
            IsDiscreteValuationRing.addVal target.valuationSubring
              (standardLubinTateLevelCoefficientHom hπ n π * y) := by
        rw [hpow, hmul]
        exact ne_of_lt henatlt
      rw [standardLubinTatePrimitivePointIterateInteger_succ]
      rw [AddValuation.map_add_of_distinct_val
        (IsDiscreteValuationRing.addVal target.valuationSubring) hdistinct,
        hpow, hmul]
      rw [min_eq_left]
      exact henatlt.le

end LubinTate

end
