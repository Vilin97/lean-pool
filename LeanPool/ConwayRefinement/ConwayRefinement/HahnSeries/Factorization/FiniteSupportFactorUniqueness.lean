/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.InfiniteSupport

import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Uniqueness of the finite-support factor

This module proves the conditional core of LM24, Theorem 6.4.1. A factorisation consists of one
finite-support series followed by a finite list of irreducible series with infinite support. The
finite-support factor is unique up to multiplication by a nonzero coefficient scalar.

The proof first shows that every irreducible infinite-support factor has normalized maximal
finite-support divisor `1`. Multiplicativity of the normalized maximal divisor then identifies the
finite-support factor with the canonical divisor up to a scalar. No uniqueness assertion is made
about the list of infinite-support irreducible factors.

Finite-support greatest-common-divisor existence, finite-support unit classification, and
multiplicativity of the normalized maximal divisor remain explicit hypotheses; the coefficient
field has characteristic zero.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

private theorem degree_eq_of_associated {b c : Series K} (hbc : Associated b c) :
    (b : K⟦ℝ⟧).degree = (c : K⟦ℝ⟧).degree := by
  obtain ⟨u, hu⟩ := hbc
  have huDegree : (((u : Series K) : K⟦ℝ⟧).degree) = 0 :=
    degree_eq_zero_of_isUnit HahnSeries.Nonpositive.degree_mul u.isUnit
  have hdegree := HahnSeries.Nonpositive.degree_mul b (u : Series K)
  rw [hu, huDegree, add_zero] at hdegree
  exact hdegree.symm

/-- An irreducible series with infinite support has no nonunit finite-support divisor. -/
theorem hasOnlyUnitFiniteSupportDivisors_of_irreducible_of_support_infinite
    {c : Series K} (hcIrreducible : Irreducible c)
    (hcInfinite : (c : K⟦ℝ⟧).support.Infinite) :
    HasOnlyUnitFiniteSupportDivisors c := by
  apply (hasOnlyUnitFiniteSupportDivisors_iff c).mpr
  intro p hp
  rcases (hcIrreducible.dvd_iff).mp hp with hpUnit | hcp
  · apply isUnit_of_dvd_one
    apply (finiteSupport_dvd_iff_coe_dvd
      (1 : FiniteSupportRing (K := K)) p).mpr
    simpa using hpUnit.dvd
  · have hcNe : c ≠ 0 := by
      intro hzero
      subst c
      simp at hcInfinite
    have hpSeriesNe : (p : Series K) ≠ 0 := hcp.ne_zero_iff.mp hcNe
    have hpHahnNe : (p : K⟦ℝ⟧) ≠ 0 := by
      intro hzero
      exact hpSeriesNe (Subtype.ext hzero)
    have hpDegree : (p : K⟦ℝ⟧).degree = 0 := by
      rw [HahnSeries.degree_eq_zero]
      exact ⟨hpHahnNe, (mem_finiteSupportSubring_iff (p : Series K)).mp p.2⟩
    have hcDegree : (c : K⟦ℝ⟧).degree = 0 :=
      (degree_eq_of_associated hcp).trans hpDegree
    exact (not_le_of_gt
      (HahnSeries.degree_pos_iff_support_infinite.mpr hcInfinite) hcDegree.le).elim

/-- The normalized maximal finite-support divisor of an irreducible infinite-support series is
one. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_eq_one_of_irreducible_of_support_infinite
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ k : K, k ≠ 0 ∧
        p = finiteSupportScalarHom (G := ℝ) k)
    {c : Series K} (hcIrreducible : Irreducible c)
    (hcInfinite : (c : K⟦ℝ⟧).support.Infinite) :
    seriesNormalizedMaximalFiniteSupportDivisor c = 1 := by
  have hcPrimitive :=
    hasOnlyUnitFiniteSupportDivisors_of_irreducible_of_support_infinite
      hcIrreducible hcInfinite
  have hcPrimitive' := (hasOnlyUnitFiniteSupportDivisors_iff c).mp hcPrimitive
  apply seriesNormalizedMaximalFiniteSupportDivisor_eq_of_is hgcd hunits
  rw [isNormalizedSeriesMaximalFiniteSupportDivisor_iff]
  constructor
  · intro q
    constructor
    · exact fun hq ↦ (hcPrimitive' q hq).dvd
    · intro hq
      have hqSeries : (q : Series K) ∣ (1 : Series K) :=
        map_dvd (finiteSupportSubring (G := ℝ) (K := K)).subtype hq
      exact hqSeries.trans (one_dvd c)
  · refine Or.inr ⟨?_, isMonicFiniteSupport_one⟩
    intro hzero
    subst c
    simp at hcInfinite

/-- The normalized maximal finite-support divisor of a product list of irreducible
infinite-support series is one. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_list_prod_eq_one
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ k : K, k ≠ 0 ∧
        p = finiteSupportScalarHom (G := ℝ) k)
    (hmaxMul : ∀ b c : Series K,
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        seriesNormalizedMaximalFiniteSupportDivisor b *
          seriesNormalizedMaximalFiniteSupportDivisor c)
    (factors : List (Series K))
    (hfactors : ∀ c ∈ factors,
      Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) :
    seriesNormalizedMaximalFiniteSupportDivisor factors.prod = 1 := by
  induction factors with
  | nil =>
      simpa using seriesNormalizedMaximalFiniteSupportDivisor_eq_one_of_isPrincipal hunits
        (isPrincipal_one (R := K))
  | cons c factors ih =>
      rw [List.prod_cons, hmaxMul,
        seriesNormalizedMaximalFiniteSupportDivisor_eq_one_of_irreducible_of_support_infinite hgcd
          hunits (hfactors c (by simp)).1
            (hfactors c (by simp)).2,
        ih (fun d hd ↦ hfactors d (by simp [hd]))]
      exact one_mul 1

/-- A factorisation into one finite-support factor and finitely many irreducible
infinite-support factors. -/
def IsInfiniteSupportIrreducibleFactorization (b : Series K) (p : FiniteSupportRing (K := K))
    (factors : List (Series K)) : Prop :=
  b = (p : Series K) * factors.prod ∧
    ∀ c ∈ factors, Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite

omit [CharZero K] in
/-- Characterization of a factorisation into a finite-support factor and irreducible
infinite-support factors. -/
theorem isInfiniteSupportIrreducibleFactorization_iff
    (b : Series K) (p : FiniteSupportRing (K := K))
    (factors : List (Series K)) :
    IsInfiniteSupportIrreducibleFactorization b p factors ↔
      b = (p : Series K) * factors.prod ∧
        ∀ c ∈ factors, Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite :=
  Iff.rfl

/-- A finite-support factor is unique up to multiplication by a nonzero coefficient scalar
among all factorisations with irreducible infinite-support residual factors. -/
def IsUniqueFiniteSupportFactorUpToScalar (b : Series K) (p : FiniteSupportRing (K := K)) : Prop :=
  ∀ (q : FiniteSupportRing (K := K)) (factors : List (Series K)),
    IsInfiniteSupportIrreducibleFactorization b q factors →
      ∃ k : K, k ≠ 0 ∧ q = finiteSupportScalarHom (G := ℝ) k * p

omit [CharZero K] in
/-- Characterization of uniqueness of the finite-support factor up to a nonzero coefficient
scalar. -/
theorem isUniqueFiniteSupportFactorUpToScalar_iff (b : Series K) (p : FiniteSupportRing (K := K)) :
    IsUniqueFiniteSupportFactorUpToScalar b p ↔
      ∀ (q : FiniteSupportRing (K := K)) (factors : List (Series K)),
        IsInfiniteSupportIrreducibleFactorization b q factors →
          ∃ k : K, k ≠ 0 ∧ q = finiteSupportScalarHom (G := ℝ) k * p :=
  Iff.rfl

/-- Any finite-support factor in such a factorisation differs from the canonical normalized
maximal finite-support divisor by a nonzero coefficient scalar. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_eq_scalar_mul_of_factorization
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ k : K, k ≠ 0 ∧
        p = finiteSupportScalarHom (G := ℝ) k)
    (hmaxMul : ∀ b c : Series K,
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        seriesNormalizedMaximalFiniteSupportDivisor b *
          seriesNormalizedMaximalFiniteSupportDivisor c)
    {b : Series K} {p : FiniteSupportRing (K := K)}
    {factors : List (Series K)}
    (hfactorization : IsInfiniteSupportIrreducibleFactorization b p factors) :
    ∃ k : K, k ≠ 0 ∧
      seriesNormalizedMaximalFiniteSupportDivisor b =
        finiteSupportScalarHom (G := ℝ) k * p := by
  obtain ⟨k, hk, hp⟩ :=
    exists_scalar_seriesNormalizedMaximalFiniteSupportDivisor_coe hunits p
  refine ⟨k, hk, ?_⟩
  rw [hfactorization.1, hmaxMul, hp,
    seriesNormalizedMaximalFiniteSupportDivisor_list_prod_eq_one hgcd hunits hmaxMul factors
      hfactorization.2,
    mul_one]

/-- The finite-support factors in any two such factorisations differ by multiplication by a
nonzero coefficient scalar. -/
theorem finiteSupportFactor_eq_scalar_mul_of_factorizations
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ k : K, k ≠ 0 ∧
        p = finiteSupportScalarHom (G := ℝ) k)
    (hmaxMul : ∀ b c : Series K,
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        seriesNormalizedMaximalFiniteSupportDivisor b *
          seriesNormalizedMaximalFiniteSupportDivisor c)
    {b : Series K} {p q : FiniteSupportRing (K := K)}
    {factors otherFactors : List (Series K)}
    (hp : IsInfiniteSupportIrreducibleFactorization b p factors)
    (hq : IsInfiniteSupportIrreducibleFactorization b q otherFactors) :
    ∃ k : K, k ≠ 0 ∧ q = finiteSupportScalarHom (G := ℝ) k * p := by
  obtain ⟨a, ha, hpa⟩ :=
    seriesNormalizedMaximalFiniteSupportDivisor_eq_scalar_mul_of_factorization hgcd hunits hmaxMul
      hp
  obtain ⟨d, hd, hqd⟩ :=
    seriesNormalizedMaximalFiniteSupportDivisor_eq_scalar_mul_of_factorization hgcd hunits hmaxMul
      hq
  have haUnit :
      IsUnit (finiteSupportScalarHom (G := ℝ) a : FiniteSupportRing (K := K)) :=
    (hunits _).mpr ⟨a, ha, rfl⟩
  have hdUnit :
      IsUnit (finiteSupportScalarHom (G := ℝ) d : FiniteSupportRing (K := K)) :=
    (hunits _).mpr ⟨d, hd, rfl⟩
  have hmkP : Associates.mk (seriesNormalizedMaximalFiniteSupportDivisor b) =
      Associates.mk p := by
    rw [hpa, ← Associates.mk_mul_mk, Associates.mk_eq_one.mpr haUnit, one_mul]
  have hmkQ : Associates.mk (seriesNormalizedMaximalFiniteSupportDivisor b) =
      Associates.mk q := by
    rw [hqd, ← Associates.mk_mul_mk, Associates.mk_eq_one.mpr hdUnit, one_mul]
  exact exists_nonzero_scalar_mul_of_mk_eq_mk hunits (hmkP.symm.trans hmkQ)

/-- Conditional existence, Cantor-term bound, and finite-support-factor uniqueness underlying
LM24, Theorem 6.4.1. -/
theorem exists_factorization_with_unique_finiteSupportFactor
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ k : K, k ≠ 0 ∧
        p = finiteSupportScalarHom (G := ℝ) k)
    (hmaxMul : ∀ b c : Series K,
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
        seriesNormalizedMaximalFiniteSupportDivisor b *
          seriesNormalizedMaximalFiniteSupportDivisor c)
    {b : Series K} (hb : b ≠ 0) :
    ∃ (p : FiniteSupportRing (K := K)) (factors : List (Series K)),
      IsInfiniteSupportIrreducibleFactorization b p factors ∧
        factors.length ≤ HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) ∧
        IsUniqueFiniteSupportFactorUpToScalar b p := by
  obtain ⟨k, factors, hk, hfactor, hfactors, hbound⟩ :=
    exists_series_infinite_support_factorization_of_exists_gcd hgcd hunits hb
  let p := finiteSupportScalarHom (G := ℝ) k *
    seriesNormalizedMaximalFiniteSupportDivisor b
  have hpFactor : IsInfiniteSupportIrreducibleFactorization b p factors := by
    constructor
    · have hscalar :
          ((finiteSupportScalarHom (G := ℝ) k :
            FiniteSupportRing (K := K)) : Series K) = C k := by
        apply Subtype.ext
        rw [coe_finiteSupportScalarHom, coe_C]
      change b =
        ((finiteSupportScalarHom (G := ℝ) k *
          seriesNormalizedMaximalFiniteSupportDivisor b :
            FiniteSupportRing (K := K)) : Series K) * factors.prod
      rw [Subring.coe_mul, hscalar]
      exact hfactor
    · exact hfactors
  refine ⟨p, factors, hpFactor, hbound, ?_⟩
  intro q otherFactors hq
  exact finiteSupportFactor_eq_scalar_mul_of_factorizations hgcd hunits hmaxMul hpFactor hq

end

end Berarducci
