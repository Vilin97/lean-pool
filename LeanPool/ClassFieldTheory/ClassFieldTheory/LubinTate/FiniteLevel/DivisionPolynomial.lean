/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardSeries
import Mathlib.Algebra.Polynomial.Monic
/-!
# Standard Lubin--Tate division polynomials

For a local field `F` and an element `π` of its valuation ring, this file
packages the polynomial

`f(X) = X ^ q + π * X`,

where `q` is the cardinality of the residue field.  Its compositional iterates
and the factors

`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π`

are defined over the valuation ring itself.  These constructions do not use
an equal-characteristic model.  In particular, they apply unchanged to the
standard Lubin--Tate series over a mixed-characteristic local field.

The factorization

`f^[n+1](X) = f^[n](X) * Qₙ(X)`

is purely polynomial.  No assertion about roots, irreducibility, or finite
Lubin--Tate extensions is made here.
-/

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The polynomial `X ^ q + π * X` underlying the standard Lubin--Tate
series. -/
noncomputable def standardLubinTatePolynomial
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    Polynomial F.valuationSubring :=
  Polynomial.X ^ Nat.card F.residueField +
    Polynomial.C π * Polynomial.X

/-- The defining formula for the standard Lubin--Tate polynomial. -/
theorem standardLubinTatePolynomial_formula
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    standardLubinTatePolynomial F π =
      Polynomial.X ^ Nat.card F.residueField +
        Polynomial.C π * Polynomial.X :=
  rfl

/-- Evaluation of the standard polynomial has the expected two-term
formula. -/
@[simp]
theorem standardLubinTatePolynomial_eval
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (x : F.valuationSubring) :
    (standardLubinTatePolynomial F π).eval x =
      x ^ Nat.card F.residueField + π * x := by
  simp [standardLubinTatePolynomial]

/-- Coercing the standard polynomial to a power series gives the standard
Lubin--Tate power series. -/
@[simp]
theorem standardLubinTatePolynomial_toPowerSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    ((standardLubinTatePolynomial F π :
        Polynomial F.valuationSubring) :
      PowerSeries F.valuationSubring) =
        standardLubinTatePowerSeries F π := by
  simp [standardLubinTatePolynomial, standardLubinTatePowerSeries,
    add_comm]

/-- For a uniformizer, coercing the standard polynomial gives the underlying
series of the bundled standard Lubin--Tate input. -/
@[simp]
theorem standardLubinTatePolynomial_toPowerSeries_eq_series
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    ((standardLubinTatePolynomial F π :
        Polynomial F.valuationSubring) :
      PowerSeries F.valuationSubring) =
        (standardLubinTateSeries hπ).toPowerSeries := by
  rw [standardLubinTatePolynomial_toPowerSeries,
    LubinTateSeries.standardLubinTateSeries_toPowerSeries]

/-- The standard Lubin--Tate polynomial has degree `q`. -/
theorem standardLubinTatePolynomial_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    (standardLubinTatePolynomial F π).natDegree =
      Nat.card F.residueField := by
  rw [standardLubinTatePolynomial]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow _
  · rw [Polynomial.natDegree_X_pow]
    calc
      (Polynomial.C π * Polynomial.X).natDegree ≤ 1 := by
        simpa only [pow_one] using
          Polynomial.natDegree_C_mul_X_pow_le π 1
      _ < Nat.card F.residueField :=
        (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The standard Lubin--Tate polynomial is monic. -/
theorem standardLubinTatePolynomial_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    (standardLubinTatePolynomial F π).Monic := by
  rw [standardLubinTatePolynomial]
  refine (Polynomial.monic_X_pow _).add_of_left ?_
  calc
    (Polynomial.C π * Polynomial.X).degree ≤ 1 :=
      Polynomial.degree_C_mul_X_le π
    _ < (Polynomial.X ^ Nat.card F.residueField :
        Polynomial F.valuationSubring).degree := by
      rw [Polynomial.degree_X_pow]
      exact_mod_cast (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The `n`-fold compositional iterate of the standard polynomial, starting
from `X`. -/
noncomputable def standardLubinTatePolynomialIterate
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial F.valuationSubring :=
  (standardLubinTatePolynomial F π).comp^[n] Polynomial.X

/-- The zeroth compositional iterate is `X`. -/
@[simp]
theorem standardLubinTatePolynomialIterate_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    standardLubinTatePolynomialIterate F π 0 = Polynomial.X := by
  simp [standardLubinTatePolynomialIterate]

/-- A successor iterate is obtained by one further composition with the
standard polynomial. -/
theorem standardLubinTatePolynomialIterate_succ
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate F π (n + 1) =
      (standardLubinTatePolynomial F π).comp
        (standardLubinTatePolynomialIterate F π n) := by
  rw [standardLubinTatePolynomialIterate,
    Function.iterate_succ_apply']
  rfl

/-- The `n`-fold standard compositional iterate has degree `q ^ n`. -/
theorem standardLubinTatePolynomialIterate_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).natDegree =
      Nat.card F.residueField ^ n := by
  rw [standardLubinTatePolynomialIterate,
    Polynomial.natDegree_iterate_comp,
    standardLubinTatePolynomial_natDegree,
    Polynomial.natDegree_X, mul_one]

/-- Every compositional iterate of the standard polynomial is monic. -/
theorem standardLubinTatePolynomialIterate_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).Monic := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ]
      exact (standardLubinTatePolynomial_monic F π).comp ih
        (by
          rw [standardLubinTatePolynomialIterate_natDegree]
          exact pow_ne_zero n
            (ne_of_gt
              (Nat.zero_lt_one.trans
                (Finite.one_lt_card : 1 < Nat.card F.residueField))))

/-- Every standard compositional iterate vanishes at zero. -/
@[simp]
theorem standardLubinTatePolynomialIterate_eval_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).eval 0 = 0 := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ,
        Polynomial.eval_comp, ih]
      simp [standardLubinTatePolynomial,
        ne_of_gt
          (Nat.zero_lt_one.trans
            (Finite.one_lt_card : 1 < Nat.card F.residueField))]

/-- The primitive quotient polynomial at level `n + 1`. -/
noncomputable def standardLubinTatePrimitivePolynomial
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial F.valuationSubring :=
  standardLubinTatePolynomialIterate F π n ^
      (Nat.card F.residueField - 1) +
    Polynomial.C π

/-- The defining formula for the primitive quotient polynomial. -/
theorem standardLubinTatePrimitivePolynomial_formula
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomial F π n =
      standardLubinTatePolynomialIterate F π n ^
          (Nat.card F.residueField - 1) +
        Polynomial.C π :=
  rfl

/-- The primitive quotient polynomial has degree `(q - 1) * q ^ n`. -/
theorem standardLubinTatePrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).natDegree =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  rw [standardLubinTatePrimitivePolynomial]
  have hpos :
      0 < (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
    Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow,
      standardLubinTatePolynomialIterate_natDegree]
  · rw [Polynomial.natDegree_pow,
      standardLubinTatePolynomialIterate_natDegree,
      Polynomial.natDegree_C]
    exact hpos

/-- The primitive quotient polynomial is monic. -/
theorem standardLubinTatePrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).Monic := by
  rw [standardLubinTatePrimitivePolynomial]
  let A := standardLubinTatePolynomialIterate F π n
  have hA : A.Monic :=
    standardLubinTatePolynomialIterate_monic F π n
  have hmain :
      (A ^ (Nat.card F.residueField - 1)).Monic :=
    hA.pow _
  refine hmain.add_of_left ?_
  calc
    (Polynomial.C π).degree ≤ 0 :=
      Polynomial.degree_C_le
    _ < (A ^ (Nat.card F.residueField - 1)).degree := by
      rw [Polynomial.degree_eq_natDegree hmain.ne_zero,
        Polynomial.natDegree_pow,
        standardLubinTatePolynomialIterate_natDegree]
      exact_mod_cast Nat.mul_pos
        (Nat.sub_pos_of_lt
          (Finite.one_lt_card : 1 < Nat.card F.residueField))
        (Nat.pow_pos Nat.card_pos)

/-- The constant coefficient of the primitive quotient polynomial is `π`. -/
@[simp]
theorem standardLubinTatePrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).coeff 0 = π := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [standardLubinTatePrimitivePolynomial,
    standardLubinTatePolynomialIterate_eval_zero,
    ne_of_gt
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))]

/-- The next compositional iterate is the current iterate times its primitive
quotient polynomial. -/
theorem standardLubinTatePolynomialIterate_succ_factor
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate F π (n + 1) =
      standardLubinTatePolynomialIterate F π n *
        standardLubinTatePrimitivePolynomial F π n := by
  have hq : Nat.card F.residueField ≠ 0 :=
    ne_of_gt
      (Nat.zero_lt_one.trans
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
  rw [standardLubinTatePolynomialIterate_succ,
    standardLubinTatePolynomial,
    standardLubinTatePrimitivePolynomial]
  simp only [Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.mul_comp, Polynomial.C_comp]
  rw [← pow_sub_one_mul hq]
  ring

end LubinTate

end
