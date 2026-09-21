/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.AlmostIrreducible
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportConstantTermOne

/-!
# Factorisations over a divisible exponent subgroup

This file defines the factorisation objects in LM24, Theorem 6.5.7. The coefficient scalar is
retained explicitly: the printed product omits it, and therefore does not represent a nonunit
constant series. A nonpositive subgroup exponent represents the monomial factor, while a list
represents the finite family of almost irreducible factors.

The normalized finite-support factor and the monomial exponent have separate uniqueness
predicates. No uniqueness is asserted for the list of almost irreducible or irreducible factors.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {H : AddSubgroup ℝ} {K : Type v} [Field K]

/-- A corrected LM24, Theorem 6.5.7 factorisation: a nonzero coefficient scalar, a normalized
finite-support factor, a coefficient-one monomial, and finitely many almost irreducible factors
with infinite support. -/
def IsAlmostIrreducibleFactorization
    (b : Nonpositive H K) (k : Kˣ)
    (p : ConstantTermOneFiniteSupport (G := H) (K := K))
    (x : exponentMonoid H) (factors : List (Nonpositive H K)) : Prop :=
  b = C (k : K) *
      ((p : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K) *
      (finiteSupportMonomial (K := K) x : Nonpositive H K) * factors.prod ∧
    ∀ c ∈ factors, IsAlmostIrreducible c ∧ (c : K⟦H⟧).support.Infinite

/-- Characterization of an almost-irreducible factorisation over an exponent subgroup. -/
theorem isAlmostIrreducibleFactorization_iff
    (b : Nonpositive H K) (k : Kˣ)
    (p : ConstantTermOneFiniteSupport (G := H) (K := K))
    (x : exponentMonoid H) (factors : List (Nonpositive H K)) :
    IsAlmostIrreducibleFactorization b k p x factors ↔
      b = C (k : K) *
          ((p : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K) *
          (finiteSupportMonomial (K := K) x : Nonpositive H K) * factors.prod ∧
        ∀ c ∈ factors, IsAlmostIrreducible c ∧ (c : K⟦H⟧).support.Infinite :=
  Iff.rfl

/-- The normalized finite-support factor is unique among all corrected almost-irreducible
factorisations of the same series. -/
def IsUniqueNormalizedHFactor
    (b : Nonpositive H K)
    (p : ConstantTermOneFiniteSupport (G := H) (K := K)) : Prop :=
  ∀ (k : Kˣ) (q : ConstantTermOneFiniteSupport (G := H) (K := K))
    (x : exponentMonoid H) (factors : List (Nonpositive H K)),
      IsAlmostIrreducibleFactorization b k q x factors → q = p

/-- Characterization of uniqueness of the normalized finite-support factor. -/
theorem isUniqueNormalizedHFactor_iff
    (b : Nonpositive H K)
    (p : ConstantTermOneFiniteSupport (G := H) (K := K)) :
    IsUniqueNormalizedHFactor b p ↔
      ∀ (k : Kˣ) (q : ConstantTermOneFiniteSupport (G := H) (K := K))
        (x : exponentMonoid H) (factors : List (Nonpositive H K)),
          IsAlmostIrreducibleFactorization b k q x factors → q = p :=
  Iff.rfl

/-- The strengthened factorisation in LM24, Theorem 6.5.7, in which every infinite-support
factor is irreducible rather than merely almost irreducible. -/
def IsIrreducibleSubgroupFactorization
    (b : Nonpositive H K) (k : Kˣ)
    (p : ConstantTermOneFiniteSupport (G := H) (K := K))
    (x : exponentMonoid H) (factors : List (Nonpositive H K)) : Prop :=
  b = C (k : K) *
      ((p : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K) *
      (finiteSupportMonomial (K := K) x : Nonpositive H K) * factors.prod ∧
    ∀ c ∈ factors, Irreducible c ∧ (c : K⟦H⟧).support.Infinite

/-- Characterization of an irreducible infinite-support factorisation over an exponent
subgroup. -/
theorem isIrreducibleSubgroupFactorization_iff
    (b : Nonpositive H K) (k : Kˣ)
    (p : ConstantTermOneFiniteSupport (G := H) (K := K))
    (x : exponentMonoid H) (factors : List (Nonpositive H K)) :
    IsIrreducibleSubgroupFactorization b k p x factors ↔
      b = C (k : K) *
          ((p : FiniteSupportRing (G := H) (K := K)) : Nonpositive H K) *
          (finiteSupportMonomial (K := K) x : Nonpositive H K) * factors.prod ∧
        ∀ c ∈ factors, Irreducible c ∧ (c : K⟦H⟧).support.Infinite :=
  Iff.rfl

/-- An irreducible subgroup factorisation is, in particular, an almost-irreducible
factorisation with the same data. -/
theorem IsIrreducibleSubgroupFactorization.isAlmostIrreducibleFactorization
    {b : Nonpositive H K} {k : Kˣ}
    {p : ConstantTermOneFiniteSupport (G := H) (K := K)}
    {x : exponentMonoid H} {factors : List (Nonpositive H K)}
    (h : IsIrreducibleSubgroupFactorization b k p x factors) :
    IsAlmostIrreducibleFactorization b k p x factors := by
  rw [isIrreducibleSubgroupFactorization_iff] at h
  rw [isAlmostIrreducibleFactorization_iff]
  refine ⟨h.1, fun c hc ↦ ?_⟩
  exact ⟨HahnSeries.Nonpositive.Irreducible.isAlmostIrreducible
    (h.2 c hc).1, (h.2 c hc).2⟩

/-- The monomial exponent is unique among all irreducible subgroup factorisations of the same
series. -/
def IsUniqueIrreducibleFactorizationExponent
    (b : Nonpositive H K) (x : exponentMonoid H) : Prop :=
  ∀ (k : Kˣ) (p : ConstantTermOneFiniteSupport (G := H) (K := K))
    (y : exponentMonoid H) (factors : List (Nonpositive H K)),
      IsIrreducibleSubgroupFactorization b k p y factors → y = x

/-- Characterization of uniqueness of the monomial exponent in irreducible subgroup
factorisations. -/
theorem isUniqueIrreducibleFactorizationExponent_iff
    (b : Nonpositive H K) (x : exponentMonoid H) :
    IsUniqueIrreducibleFactorizationExponent b x ↔
      ∀ (k : Kˣ) (p : ConstantTermOneFiniteSupport (G := H) (K := K))
        (y : exponentMonoid H) (factors : List (Nonpositive H K)),
          IsIrreducibleSubgroupFactorization b k p y factors → y = x :=
  Iff.rfl

end HahnSeries.Nonpositive
