/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
/-!
# Eisenstein property of the standard primitive division polynomials

Let `F` be a local field, let `π` be a uniformizer, and put

`f(X) = X ^ q + π * X`,

where `q` is the cardinality of the residue field.  Reduction modulo the
maximal ideal sends the `n`-fold compositional iterate of `f` to
`X ^ (q ^ n)`.  Consequently, the primitive quotient polynomial

`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π`

reduces to its leading monomial.  Its constant coefficient is the
uniformizer itself, so `Qₙ` is Eisenstein at the maximal ideal and hence
irreducible over the valuation ring.

The argument is independent of the characteristic of `F`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Reduction modulo the maximal ideal sends the standard Lubin--Tate
polynomial to `X ^ q`. -/
theorem standardLubinTatePolynomial_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (standardLubinTatePolynomial F π).map F.residueMap =
      Polynomial.X ^ Nat.card F.residueField := by
  simp [standardLubinTatePolynomial,
    SameUniformizer.residueMap_uniformizer_eq_zero hπ]

/-- Reduction modulo the maximal ideal sends the `n`-fold standard iterate
to `X ^ (q ^ n)`. -/
theorem standardLubinTatePolynomialIterate_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).map F.residueMap =
      Polynomial.X ^ (Nat.card F.residueField ^ n) := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ,
        Polynomial.map_comp,
        standardLubinTatePolynomial_map_residue hπ,
        ih]
      simp [← pow_mul, pow_succ]

/-- Reduction modulo the maximal ideal sends the primitive quotient
polynomial to its leading monomial. -/
theorem standardLubinTatePrimitivePolynomial_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).map F.residueMap =
      Polynomial.X ^
        ((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n) := by
  simp [standardLubinTatePrimitivePolynomial,
    standardLubinTatePolynomialIterate_map_residue hπ,
    SameUniformizer.residueMap_uniformizer_eq_zero hπ,
    ← pow_mul, Nat.mul_comm]

/-- The standard primitive quotient polynomial is Eisenstein at the maximal
ideal of the valuation ring. -/
theorem standardLubinTatePrimitivePolynomial_isEisensteinAt
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).IsEisensteinAt
      F.maximalIdeal := by
  let Q := standardLubinTatePrimitivePolynomial F π n
  let d :=
    (Nat.card F.residueField - 1) *
      Nat.card F.residueField ^ n
  have hmonic : Q.Monic :=
    standardLubinTatePrimitivePolynomial_monic F π n
  have hprime : F.maximalIdeal.IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime
  refine hmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
  · intro i hi
    have hcoeff :
        F.residueMap (Q.coeff i) =
          (Polynomial.X ^ d : Polynomial F.residueField).coeff i := by
      simpa only [Q, d, Polynomial.coeff_map] using
        congrArg (fun p : Polynomial F.residueField ↦ p.coeff i)
          (standardLubinTatePrimitivePolynomial_map_residue hπ n)
    have hid : i < d := by
      simpa [Q, d,
        standardLubinTatePrimitivePolynomial_natDegree] using hi
    have hzero : F.residueMap (Q.coeff i) = 0 := by
      rw [hcoeff]
      simp [Polynomial.coeff_X_pow, ne_of_lt hid]
    exact (F.toCompleteDVF.residue_eq_zero_iff (Q.coeff i)).1 hzero
  · simpa [Q] using
      F.toCompleteDVF.uniformizer_not_mem_maximalIdeal_sq hπ

/-- Every standard primitive quotient polynomial is primitive. -/
theorem standardLubinTatePrimitivePolynomial_isPrimitive
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).IsPrimitive :=
  (standardLubinTatePrimitivePolynomial_monic F π n).isPrimitive

/-- The standard primitive quotient polynomial is irreducible by
Eisenstein's criterion. -/
theorem standardLubinTatePrimitivePolynomial_irreducible
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Irreducible (standardLubinTatePrimitivePolynomial F π n) := by
  apply (standardLubinTatePrimitivePolynomial_isEisensteinAt hπ n).irreducible
    (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime
    (standardLubinTatePrimitivePolynomial_isPrimitive F π n)
  rw [standardLubinTatePrimitivePolynomial_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

end LubinTate

end
