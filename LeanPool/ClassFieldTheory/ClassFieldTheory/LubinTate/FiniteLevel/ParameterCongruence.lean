/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
import Mathlib.RingTheory.Ideal.Quotient.Operations
/-!
# Parameter congruences for standard Lubin--Tate polynomials

The standard polynomial

`f_π(X) = X ^ q + π * X`

depends polynomially on its parameter.  Hence two parameters which become
equal after applying a ring homomorphism give the same polynomial, all the
same compositional iterates, and the same primitive quotient polynomial.

The final theorem records the corresponding ideal-congruence statement for
evaluations.  It is the algebraic input needed when comparing primitive
levels attached to two sufficiently close uniformizers; it is independent
of the characteristic and does not assume an equivalence between the two
levels.
-/

noncomputable section

open scoped Polynomial

universe u v w

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Equal images of two parameters give equal images of their standard
Lubin--Tate polynomials. -/
theorem standardLubinTatePolynomial_map_eq_of_parameter_eq
    (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ) :
    (standardLubinTatePolynomial F π).map f =
      (standardLubinTatePolynomial F ϖ).map f := by
  simp [standardLubinTatePolynomial, h]

/-- Equal images of two parameters give equal images of every compositional
iterate of the corresponding standard polynomials. -/
theorem standardLubinTatePolynomialIterate_map_eq_of_parameter_eq
    (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).map f =
      (standardLubinTatePolynomialIterate F ϖ n).map f := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ,
        standardLubinTatePolynomialIterate_succ,
        Polynomial.map_comp, Polynomial.map_comp,
        standardLubinTatePolynomial_map_eq_of_parameter_eq F f h, ih]

/-- Equal images of two parameters give equal images of their primitive
quotient polynomials at every finite level. -/
theorem standardLubinTatePrimitivePolynomial_map_eq_of_parameter_eq
    (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).map f =
      (standardLubinTatePrimitivePolynomial F ϖ n).map f := by
  simp only [standardLubinTatePrimitivePolynomial,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C,
    standardLubinTatePolynomialIterate_map_eq_of_parameter_eq F f h n, h]

/-- Equal parameter images make the two primitive polynomials have equal
evaluations at every point of the target ring. -/
theorem standardLubinTatePrimitivePolynomial_eval₂_eq_of_parameter_eq
    (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ)
    (n : ℕ) (x : R) :
    Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F π n) =
      Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F ϖ n) := by
  have hpoly :=
    standardLubinTatePrimitivePolynomial_map_eq_of_parameter_eq
      F f h n
  simpa only [Polynomial.eval_map] using
    congrArg (fun p : Polynomial R ↦ p.eval x) hpoly

/-- If two parameters are congruent modulo an ideal after mapping into a
commutative ring, then the evaluations of their primitive quotient
polynomials at the same point are congruent modulo that ideal. -/
theorem standardLubinTatePrimitivePolynomial_eval₂_sub_mem_of_parameter_sub_mem
    (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R) (I : Ideal R)
    {π ϖ : F.valuationSubring} (h : f π - f ϖ ∈ I)
    (n : ℕ) (x : R) :
    Polynomial.eval₂ f x
          (standardLubinTatePrimitivePolynomial F π n) -
        Polynomial.eval₂ f x
          (standardLubinTatePrimitivePolynomial F ϖ n) ∈ I := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hparameter : q (f π) = q (f ϖ) := by
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := I) (f π) (f ϖ)).2 h
  have heval :
      Polynomial.eval₂ (q.comp f) (q x)
          (standardLubinTatePrimitivePolynomial F π n) =
        Polynomial.eval₂ (q.comp f) (q x)
          (standardLubinTatePrimitivePolynomial F ϖ n) :=
    standardLubinTatePrimitivePolynomial_eval₂_eq_of_parameter_eq
      F (q.comp f) hparameter n (q x)
  apply
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := I)
      (Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F π n))
      (Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F ϖ n))).1
  calc
    q (Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F π n)) =
        Polynomial.eval₂ (q.comp f) (q x)
          (standardLubinTatePrimitivePolynomial F π n) := by
      exact Polynomial.hom_eval₂ _ _ _ _
    _ = Polynomial.eval₂ (q.comp f) (q x)
          (standardLubinTatePrimitivePolynomial F ϖ n) :=
      heval
    _ = q (Polynomial.eval₂ f x
          (standardLubinTatePrimitivePolynomial F ϖ n)) := by
      exact (Polynomial.hom_eval₂ _ _ _ _).symm

end LubinTate

end
