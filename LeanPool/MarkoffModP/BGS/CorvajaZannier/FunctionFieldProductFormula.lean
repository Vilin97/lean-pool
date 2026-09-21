/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# A normalized-factor product formula for the rational function field

This file proves the normalized-factor form of the degree-zero formula for a
principal divisor on `K(X)`.  At every normalized prime factor, the
multiplicity is identified with the actual Dedekind-domain exponent
`FractionalIdeal.count` of the principal fractional ideal.  Normalized
polynomial factorization makes the finite contribution explicit; the
remaining term is Mathlib's valuation at infinity.  Packaging that finite
contribution as one exhaustive sum over `HeightOneSpectrum K[X]` is completed
in `RatFuncExhaustiveProductFormula`.

This is the base-field input for the Corvaja--Zannier valuation argument.  It
does **not** yet supply the corresponding formula for a finite extension of
`K(X)`: Mathlib currently has no packaged degree map on the divisor group of
the integral closure, nor the global finite-place identity combining
ramification and residue degrees over each base place.
-/

open scoped nonZeroDivisors
open IsDedekindDomain Polynomial UniqueFactorizationMonoid
open Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- The height-one prime of `K[X]` cut out by a prime polynomial. -/
def polynomialFinitePlace (r : K[X]) (hr : Prime r) : HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {r}
  isPrime := (Ideal.span_singleton_prime hr.ne_zero).2 hr
  ne_bot := by
    intro h
    exact hr.ne_zero (Ideal.span_singleton_eq_bot.mp h)

@[simp]
theorem polynomialFinitePlace_asIdeal (r : K[X]) (hr : Prime r) :
    (polynomialFinitePlace r hr).asIdeal = Ideal.span {r} := rfl

/-- The sum of the degrees of the normalized irreducible factors of a
nonzero polynomial, with multiplicity, is its degree. -/
theorem sum_normalizedFactor_natDegree [DecidableEq K]
    (p : K[X]) (hp : p ≠ 0) :
    ∑ r ∈ (normalizedFactors p).toFinset,
        (normalizedFactors p).count r * r.natDegree = p.natDegree := by
  have hprodDegree : (normalizedFactors p).prod.natDegree = p.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated (prod_normalizedFactors hp))
  calc
    ∑ r ∈ (normalizedFactors p).toFinset,
        (normalizedFactors p).count r * r.natDegree =
        (Multiset.map Polynomial.natDegree (normalizedFactors p)).sum := by
          simpa [nsmul_eq_mul, mul_comm] using
            (Finset.sum_multiset_map_count (normalizedFactors p)
              Polynomial.natDegree).symm
    _ = (normalizedFactors p).prod.natDegree := by
      rw [Polynomial.natDegree_multiset_prod]
      exact zero_notMem_normalizedFactors p
    _ = p.natDegree := hprodDegree

/-- The additive order of a rational function at a finite polynomial place,
implemented by the Dedekind-domain exponent of its principal fractional ideal. -/
def ratFuncFiniteOrder (v : HeightOneSpectrum K[X]) (f : RatFunc K) : ℤ :=
  FractionalIdeal.count (RatFunc K) v
    (FractionalIdeal.spanSingleton (K[X])⁰ f)

private theorem ratFunc_principal_fractionalIdeal_representation
    (f : RatFunc K) :
    FractionalIdeal.spanSingleton (K[X])⁰ f =
      FractionalIdeal.spanSingleton (K[X])⁰
          ((algebraMap K[X] (RatFunc K) f.denom)⁻¹) *
        (↑(Ideal.span {f.num}) : FractionalIdeal (K[X])⁰ (RatFunc K)) := by
  rw [FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply congrArg (FractionalIdeal.spanSingleton (K[X])⁰)
  simpa only [div_eq_mul_inv, mul_comm] using (RatFunc.num_div_denom f).symm

/-- At a normalized prime polynomial, the Dedekind-domain order of a
nonzero rational function is the numerator multiplicity minus the denominator
multiplicity. -/
theorem ratFuncFiniteOrder_polynomialFinitePlace
    [DecidableEq K]
    (f : RatFunc K) (hf : f ≠ 0) (r : K[X]) (hr : Prime r)
    (hrnorm : normalize r = r) :
    ratFuncFiniteOrder (polynomialFinitePlace r hr) f =
      ((normalizedFactors f.num).count r : ℤ) -
        (normalizedFactors f.denom).count r := by
  have hprincipal :
      FractionalIdeal.spanSingleton (K[X])⁰ f ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff]
    exact hf
  rw [ratFuncFiniteOrder,
    FractionalIdeal.count_well_defined (RatFunc K)
      (polynomialFinitePlace r hr) hprincipal
      (ratFunc_principal_fractionalIdeal_representation f)]
  change
    ((Associates.mk (Ideal.span {r})).count
          (Associates.mk (Ideal.span {f.num})).factors : ℤ) -
      ((Associates.mk (Ideal.span {r})).count
          (Associates.mk (Ideal.span {f.denom})).factors : ℤ) = _
  congr 1 <;> norm_cast
  · rw [Ideal.count_associates_factors_eq
      (by
        intro h
        exact RatFunc.num_ne_zero hf (Ideal.span_singleton_eq_bot.mp h))
      ((Ideal.span_singleton_prime hr.ne_zero).2 hr)
      (by
        intro h
        exact hr.ne_zero (Ideal.span_singleton_eq_bot.mp h)),
      Ideal.count_span_normalizedFactors_eq (RatFunc.num_ne_zero hf) hr,
      hrnorm]
  · rw [Ideal.count_associates_factors_eq
      (by
        intro h
        exact f.denom_ne_zero (Ideal.span_singleton_eq_bot.mp h))
      ((Ideal.span_singleton_prime hr.ne_zero).2 hr)
      (by
        intro h
        exact hr.ne_zero (Ideal.span_singleton_eq_bot.mp h)),
      Ideal.count_span_normalizedFactors_eq f.denom_ne_zero hr,
      hrnorm]

/-- The degree-weighted finite-place contribution of a nonzero rational
function, written as its zero contribution minus its pole contribution.  The
preceding theorem identifies the multiplicities here with
`FractionalIdeal.count` at the corresponding height-one primes. -/
def ratFuncFinitePlaceDegreeSum [DecidableEq K] (f : RatFunc K) : ℤ :=
  (∑ r ∈ (normalizedFactors f.num).toFinset,
      (normalizedFactors f.num).count r * r.natDegree : ℕ) -
    (∑ r ∈ (normalizedFactors f.denom).toFinset,
      (normalizedFactors f.denom).count r * r.natDegree : ℕ)

/-- The additive order at infinity.  Mathlib's multiplicative infinity
valuation sends a nonzero `f` to `exp (-ratFuncInfinityOrder f)`. -/
def ratFuncInfinityOrder (f : RatFunc K) : ℤ := -f.intDegree

theorem inftyValuation_eq_exp_neg_ratFuncInfinityOrder
    [DecidableEq (RatFunc K)] (f : RatFunc K) (hf : f ≠ 0) :
    RatFunc.inftyValuation K f =
      exp (-ratFuncInfinityOrder f) := by
  rw [RatFunc.inftyValuation_apply]
  rw [RatFunc.inftyValuation_of_nonzero (F := K) hf]
  simp only [ratFuncInfinityOrder, neg_neg]

theorem ratFuncFinitePlaceDegreeSum_eq_intDegree
    [DecidableEq K]
    (f : RatFunc K) (hf : f ≠ 0) :
    ratFuncFinitePlaceDegreeSum f = f.intDegree := by
  rw [ratFuncFinitePlaceDegreeSum,
    sum_normalizedFactor_natDegree f.num (RatFunc.num_ne_zero hf),
    sum_normalizedFactor_natDegree f.denom f.denom_ne_zero]
  rfl

/-- The normalized-factor form of the product formula for `K(X)`: the
degree-weighted numerator-minus-denominator contribution plus the order at
infinity is zero. -/
theorem ratFunc_finitePlace_plus_infinity_productFormula
    [DecidableEq K]
    (f : RatFunc K) (hf : f ≠ 0) :
    ratFuncFinitePlaceDegreeSum f + ratFuncInfinityOrder f = 0 := by
  rw [ratFuncFinitePlaceDegreeSum_eq_intDegree f hf]
  simp only [ratFuncInfinityOrder, add_neg_cancel]

end

end BGS.CorvajaZannier
