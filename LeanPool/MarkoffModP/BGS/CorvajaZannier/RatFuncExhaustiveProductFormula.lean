/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FunctionFieldProductFormula
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-!
# The exhaustive finite-place product formula for the rational function field

This file packages the principal fractional ideal of a nonzero element of
`K(X)` as a `Finsupp` on the full `HeightOneSpectrum K[X]`.  Each height-one
prime is identified with its canonical normalized prime-polynomial generator,
so the degree-weighted sum can be reindexed to normalized polynomial
factorization.  The resulting exhaustive finite-place sum is `f.intDegree`;
after adding Mathlib's order at infinity, the total is zero.
-/

open scoped nonZeroDivisors
open IsDedekindDomain Polynomial UniqueFactorizationMonoid

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- Normalized prime polynomials, i.e. the canonical polynomial representatives
of finite places of `K(X)`. -/
abbrev NormalizedPrimePolynomial (K : Type*) [Field K] [DecidableEq K] :=
  {r : K[X] // Prime r ∧ normalize r = r}

/-- The normalized prime polynomial generating a finite place of `K(X)`. -/
def finitePlaceNormalizedPrime [DecidableEq K]
    (v : HeightOneSpectrum K[X]) : NormalizedPrimePolynomial K := by
  let g := Submodule.IsPrincipal.generator v.asIdeal
  refine ⟨normalize g, ?_, normalize_idem g⟩
  exact (normalize_associated g).symm.prime
    (Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot)

/-- The finite place cut out by a normalized prime polynomial. -/
def normalizedPrimeFinitePlace [DecidableEq K] (r : NormalizedPrimePolynomial K) :
    HeightOneSpectrum K[X] :=
  polynomialFinitePlace r r.property.1

@[simp]
theorem normalizedPrimeFinitePlace_finitePlaceNormalizedPrime
    [DecidableEq K] (v : HeightOneSpectrum K[X]) :
    normalizedPrimeFinitePlace (K := K) (finitePlaceNormalizedPrime v) = v := by
  apply HeightOneSpectrum.ext
  change Ideal.span {normalize (Submodule.IsPrincipal.generator v.asIdeal)} = v.asIdeal
  calc
    Ideal.span {normalize (Submodule.IsPrincipal.generator v.asIdeal)} =
        Ideal.span {Submodule.IsPrincipal.generator v.asIdeal} :=
      Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated _)
    _ = v.asIdeal := Ideal.span_singleton_generator v.asIdeal

@[simp]
theorem finitePlaceNormalizedPrime_normalizedPrimeFinitePlace
    [DecidableEq K] (r : NormalizedPrimePolynomial K) :
    finitePlaceNormalizedPrime (normalizedPrimeFinitePlace (K := K) r) = r := by
  apply Subtype.ext
  change normalize (Submodule.IsPrincipal.generator (Ideal.span {(r : K[X])})) = r
  calc
    normalize (Submodule.IsPrincipal.generator (Ideal.span {(r : K[X])})) =
        normalize (r : K[X]) := by
      exact normalize_eq_normalize_iff_associated.mpr
        (Submodule.IsPrincipal.associated_generator_span_self (r : K[X]))
    _ = r := r.property.2

/-- Normalized prime polynomials are equivalent to all finite places of `K(X)`. -/
def normalizedPrimePolynomialEquivFinitePlace [DecidableEq K] :
    NormalizedPrimePolynomial K ≃ HeightOneSpectrum K[X] where
  toFun := fun r => normalizedPrimeFinitePlace (K := K) r
  invFun := fun v => finitePlaceNormalizedPrime (K := K) v
  left_inv := finitePlaceNormalizedPrime_normalizedPrimeFinitePlace
  right_inv := normalizedPrimeFinitePlace_finitePlaceNormalizedPrime

/-- The finitely supported principal divisor at all finite places. -/
def ratFuncFiniteDivisor (f : RatFunc K) : HeightOneSpectrum K[X] →₀ ℤ :=
  let h := FractionalIdeal.finite_factors
    (FractionalIdeal.spanSingleton (K[X])⁰ f)
  Finsupp.mk h.toFinset (fun v => ratFuncFiniteOrder v f)
    (fun _ => h.mem_toFinset)

@[simp]
theorem ratFuncFiniteDivisor_apply (f : RatFunc K) (v : HeightOneSpectrum K[X]) :
    ratFuncFiniteDivisor f v = ratFuncFiniteOrder v f := rfl

/-- Degree of a finite place, defined using its canonical normalized prime generator. -/
def ratFuncFinitePlaceDegree [DecidableEq K] (v : HeightOneSpectrum K[X]) : ℕ :=
  (finitePlaceNormalizedPrime v : K[X]).natDegree

@[simp]
theorem ratFuncFinitePlaceDegree_normalizedPrimeFinitePlace [DecidableEq K]
    (r : NormalizedPrimePolynomial K) :
    ratFuncFinitePlaceDegree (normalizedPrimeFinitePlace (K := K) r) =
      (r : K[X]).natDegree := by
  simp [ratFuncFinitePlaceDegree]

/-- Factorization of a polynomial, restricted to normalized prime polynomials. -/
def normalizedPrimeFactorization [DecidableEq K] (p : K[X]) :
    NormalizedPrimePolynomial K →₀ ℕ :=
  Finsupp.comapDomain Subtype.val (factorization p) Subtype.val_injective.injOn

@[simp]
theorem normalizedPrimeFactorization_apply [DecidableEq K]
    (p : K[X]) (r : NormalizedPrimePolynomial K) :
    normalizedPrimeFactorization p r = (normalizedFactors p).count (r : K[X]) := by
  simp [normalizedPrimeFactorization, factorization_eq_count]

/-- The coefficient of the finite principal divisor is the difference of the
normalized-prime multiplicities in numerator and denominator. -/
theorem ratFuncFiniteOrder_eq_normalizedPrimeFactorization_sub
    [DecidableEq K] (f : RatFunc K) (hf : f ≠ 0)
    (v : HeightOneSpectrum K[X]) :
    ratFuncFiniteOrder v f =
      (normalizedPrimeFactorization f.num (finitePlaceNormalizedPrime v) : ℤ) -
        normalizedPrimeFactorization f.denom (finitePlaceNormalizedPrime v) := by
  let r := finitePlaceNormalizedPrime v
  have h := ratFuncFiniteOrder_polynomialFinitePlace (K := K) f hf
    (r : K[X]) r.property.1 r.property.2
  have hrplace : polynomialFinitePlace (r : K[X]) r.property.1 = v := by
    change normalizedPrimeFinitePlace (K := K) r = v
    exact normalizedPrimeFinitePlace_finitePlaceNormalizedPrime v
  rw [hrplace] at h
  simpa only [normalizedPrimeFactorization_apply] using h

/-- The numerator-minus-denominator factorization on canonical normalized
prime polynomial representatives. -/
def ratFuncNormalizedPrimeDivisor [DecidableEq K] (f : RatFunc K) :
    NormalizedPrimePolynomial K →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (Nat.cast_zero)
      (normalizedPrimeFactorization f.num) -
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (Nat.cast_zero)
      (normalizedPrimeFactorization f.denom)

@[simp]
theorem ratFuncNormalizedPrimeDivisor_apply [DecidableEq K]
    (f : RatFunc K) (r : NormalizedPrimePolynomial K) :
    ratFuncNormalizedPrimeDivisor f r =
      (normalizedPrimeFactorization f.num r : ℤ) -
        normalizedPrimeFactorization f.denom r := by
  simp [ratFuncNormalizedPrimeDivisor]

/-- The count-defined finite principal divisor agrees with the transported
normalized polynomial factorization. -/
theorem ratFuncFiniteDivisor_eq_equivMapDomain_normalizedPrimeDivisor
    [DecidableEq K] (f : RatFunc K) (hf : f ≠ 0) :
    ratFuncFiniteDivisor f =
      Finsupp.equivMapDomain normalizedPrimePolynomialEquivFinitePlace
        (ratFuncNormalizedPrimeDivisor f) := by
  ext v
  rw [ratFuncFiniteDivisor_apply, Finsupp.equivMapDomain_apply,
    ratFuncNormalizedPrimeDivisor_apply]
  exact ratFuncFiniteOrder_eq_normalizedPrimeFactorization_sub f hf v

private theorem factorization_support_subset_normalizedPrimePolynomial_range
    [DecidableEq K] (p : K[X]) :
    ((factorization p).support : Set K[X]) ⊆
      Set.range (Subtype.val : NormalizedPrimePolynomial K → K[X]) := by
  intro r hr
  have hr' : r ∈ normalizedFactors p := by
    simpa only [support_factorization, Finset.mem_coe, Multiset.mem_toFinset] using hr
  exact ⟨⟨r, prime_of_normalized_factor r hr', normalize_normalized_factor r hr'⟩, rfl⟩

private theorem normalizedPrimePolynomial_bijOn_factorizationSupport
    [DecidableEq K] (p : K[X]) :
    Set.BijOn (Subtype.val : NormalizedPrimePolynomial K → K[X])
      ((Subtype.val : NormalizedPrimePolynomial K → K[X]) ⁻¹'
        ((factorization p).support : Set K[X]))
      ((factorization p).support : Set K[X]) := by
  refine ⟨?_, Subtype.val_injective.injOn, ?_⟩
  · intro r hr
    exact hr
  · intro r hr
    obtain ⟨r', hr'eq⟩ :=
      factorization_support_subset_normalizedPrimePolynomial_range p hr
    refine ⟨r', ?_, hr'eq⟩
    simpa only [Set.mem_preimage, hr'eq] using hr

/-- The degree-weighted factorization over canonical normalized prime
representatives has total weight equal to polynomial degree. -/
theorem normalizedPrimeFactorization_degreeSum [DecidableEq K]
    (p : K[X]) (hp : p ≠ 0) :
    (normalizedPrimeFactorization p).sum
      (fun r n => n * (r : K[X]).natDegree) = p.natDegree := by
  calc
    (normalizedPrimeFactorization p).sum
        (fun r n => n * (r : K[X]).natDegree) =
        (factorization p).sum (fun r n => n * r.natDegree) := by
      change (Finsupp.comapDomain Subtype.val (factorization p)
        Subtype.val_injective.injOn).sum
          ((fun r : K[X] => fun n => n * r.natDegree) ∘ Subtype.val) = _
      exact Finsupp.sum_comapDomain
        (Subtype.val : NormalizedPrimePolynomial K → K[X])
        (factorization p) (fun r n => n * r.natDegree)
        (normalizedPrimePolynomial_bijOn_factorizationSupport p)
    _ = ∑ r ∈ (normalizedFactors p).toFinset,
          (normalizedFactors p).count r * r.natDegree := by
      simp only [Finsupp.sum, support_factorization, factorization_eq_count]
    _ = p.natDegree := sum_normalizedFactor_natDegree p hp

private theorem normalizedPrimeFactorization_intDegreeSum [DecidableEq K]
    (p : K[X]) (hp : p ≠ 0) :
    (normalizedPrimeFactorization p).sum
      (fun r n => (n : ℤ) * ((r : K[X]).natDegree : ℤ)) =
        (p.natDegree : ℤ) := by
  exact_mod_cast normalizedPrimeFactorization_degreeSum p hp

private theorem castNormalizedPrimeFactorization_intDegreeSum [DecidableEq K]
    (p : K[X]) (hp : p ≠ 0) :
    (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (normalizedPrimeFactorization p)).sum
        (fun r n => n * ((r : K[X]).natDegree : ℤ)) =
      (p.natDegree : ℤ) := by
  rw [Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
  exact normalizedPrimeFactorization_intDegreeSum p hp

/-- The exhaustive degree-weighted sum over all height-one primes of `K[X]`.
Its finite support is the support of the principal fractional ideal of `f`. -/
def ratFuncExhaustiveFinitePlaceDegreeSum [DecidableEq K] (f : RatFunc K) : ℤ :=
  (ratFuncFiniteDivisor f).sum
    (fun v n => n * (ratFuncFinitePlaceDegree v : ℤ))

private theorem ratFuncNormalizedPrimeDivisor_degreeSum_eq_intDegree
    [DecidableEq K] (f : RatFunc K) (hf : f ≠ 0) :
    (ratFuncNormalizedPrimeDivisor f).sum
      (fun r n => n * ((r : K[X]).natDegree : ℤ)) = f.intDegree := by
  rw [ratFuncNormalizedPrimeDivisor, Finsupp.sum_sub_index]
  · rw [castNormalizedPrimeFactorization_intDegreeSum f.num (RatFunc.num_ne_zero hf),
      castNormalizedPrimeFactorization_intDegreeSum f.denom f.denom_ne_zero]
    rfl
  · intro r a b
    ring

/-- The actual exhaustive finite-place degree formula for `K(X)`: the
degree-weighted sum of the principal-divisor coefficients over every
`HeightOneSpectrum K[X]` equals the rational-function degree. -/
theorem ratFuncExhaustiveFinitePlaceDegreeSum_eq_intDegree
    [DecidableEq K] (f : RatFunc K) (hf : f ≠ 0) :
    ratFuncExhaustiveFinitePlaceDegreeSum f = f.intDegree := by
  rw [ratFuncExhaustiveFinitePlaceDegreeSum,
    ratFuncFiniteDivisor_eq_equivMapDomain_normalizedPrimeDivisor f hf,
    Finsupp.sum_equivMapDomain]
  change (ratFuncNormalizedPrimeDivisor f).sum
    (fun r n => n * (ratFuncFinitePlaceDegree
      (normalizedPrimeFinitePlace (K := K) r) : ℤ)) = f.intDegree
  simpa only [ratFuncFinitePlaceDegree_normalizedPrimeFinitePlace] using
    ratFuncNormalizedPrimeDivisor_degreeSum_eq_intDegree f hf

/-- The exhaustive finite-place sum plus the order at infinity is zero. -/
theorem ratFunc_exhaustiveFinitePlace_plus_infinity_productFormula
    [DecidableEq K] (f : RatFunc K) (hf : f ≠ 0) :
    ratFuncExhaustiveFinitePlaceDegreeSum f + ratFuncInfinityOrder f = 0 := by
  rw [ratFuncExhaustiveFinitePlaceDegreeSum_eq_intDegree f hf]
  simp only [ratFuncInfinityOrder, add_neg_cancel]

end

end BGS.CorvajaZannier
