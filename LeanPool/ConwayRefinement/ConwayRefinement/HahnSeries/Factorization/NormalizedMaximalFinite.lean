/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.MaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportNormalization

/-!
# Normalized maximal finite-support divisors

This module passes from the intrinsic associate class of a maximal finite-support divisor to the
representative normalization used in LM24, Notation 5.4.5. The zero graded element is represented
by zero. For a nonzero graded element, the greatest exponent in the support of the representative
has coefficient `1`.

The normalization is defined for the canonical associate class without assuming greatest common
divisors or classifying units. Pairwise greatest-common-divisor existence proves that its associate
class is the maximal one. The same hypothesis then gives the representative form of LM24,
Proposition 5.4.8.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- A series is the normalized maximal finite-support divisor of a graded element when it has
exactly the finite-support divisors of that element and satisfies the normalization convention of
LM24, Notation 5.4.5. -/
def IsNormalizedGradedMaximalFiniteSupportDivisor (B : DegreeGraded K)
    (p : FiniteSupportRing (K := K)) : Prop :=
  (∀ q : FiniteSupportRing (K := K),
      finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p) ∧
    ((B = 0 ∧ p = 0) ∨
      (B ≠ 0 ∧ HahnSeries.Nonpositive.IsMonicFiniteSupport p))

omit [CharZero K] in
/-- Characterization of a normalized maximal finite-support divisor by divisibility and its zero
or monic normalization clause. -/
theorem isNormalizedGradedMaximalFiniteSupportDivisor_iff (B : DegreeGraded K)
    (p : FiniteSupportRing (K := K)) :
    IsNormalizedGradedMaximalFiniteSupportDivisor B p ↔
      (∀ q : FiniteSupportRing (K := K),
        finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p) ∧
      ((B = 0 ∧ p = 0) ∨
        (B ≠ 0 ∧ HahnSeries.Nonpositive.IsMonicFiniteSupport p)) :=
  Iff.rfl

/-- The normalized representative of the maximal finite-support divisor class of a graded
element. -/
def gradedNormalizedMaximalFiniteSupportDivisor
    (B : DegreeGraded K) : FiniteSupportRing (K := K) :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative (G := ℝ)
    (gradedMaximalFiniteSupportDivisor B)

omit [CharZero K] in
/-- The normalized maximal finite-support divisor is the canonical normalized representative of
its intrinsic associate class. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_eq_normalizedRepresentative
    (B : DegreeGraded K) :
    gradedNormalizedMaximalFiniteSupportDivisor B =
      HahnSeries.Nonpositive.normalizedAssociateRepresentative (G := ℝ)
        (gradedMaximalFiniteSupportDivisor B) :=
  (rfl)

omit [CharZero K] in
/-- The normalized maximal finite-support divisor satisfies the intrinsic normalization
predicate. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_isNormalized
    (B : DegreeGraded K) :
    HahnSeries.Nonpositive.IsNormalizedAssociateRepresentative
      (gradedMaximalFiniteSupportDivisor B)
      (gradedNormalizedMaximalFiniteSupportDivisor B) :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative_is _

omit [CharZero K] in
/-- The associate class of the normalized representative is the intrinsic maximal-divisor
class. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_mk (B : DegreeGraded K) :
    Associates.mk (gradedNormalizedMaximalFiniteSupportDivisor B) =
      gradedMaximalFiniteSupportDivisor B :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative_mk _

/-- On an embedded finite-support series, the graded normalized divisor is the normalized
representative of that series's own associate class. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_finiteSupport (p : FiniteSupportRing (K := K)) :
    gradedNormalizedMaximalFiniteSupportDivisor
        (finiteSupportGradedEmbedding K p) =
      HahnSeries.Nonpositive.normalizedAssociateRepresentative (G := ℝ)
        (Associates.mk p) := by
  rw [gradedNormalizedMaximalFiniteSupportDivisor,
    gradedMaximalFiniteSupportDivisor_eq_of_is
      (isGradedMaximalFiniteSupportDivisor_finiteSupport p)]

/-- Under pairwise greatest-common-divisor existence, the normalized representative has exactly
the finite-support divisors of the graded element. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_isMaximal_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : DegreeGraded K) :
    IsGradedMaximalFiniteSupportDivisor B
      (Associates.mk (gradedNormalizedMaximalFiniteSupportDivisor B)) := by
  rw [gradedNormalizedMaximalFiniteSupportDivisor_mk]
  exact gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B

/-- A nonzero graded element has a nonzero maximal finite-support divisor class. -/
theorem gradedMaximalFiniteSupportDivisor_ne_zero_of_ne_zero
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {B : DegreeGraded K} (hB : B ≠ 0) :
    gradedMaximalFiniteSupportDivisor B ≠ 0 := by
  intro hclass
  have hmax :=
    gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B
  have hzeroLe : Associates.mk (0 : FiniteSupportRing (K := K)) ≤
      gradedMaximalFiniteSupportDivisor B := by
    rw [hclass]
    exact le_rfl
  have hzeroDvd :=
    (isGradedMaximalFiniteSupportDivisor_iff B _).mp hmax 0 |>.mp hzeroLe
  obtain ⟨D, hD⟩ := hzeroDvd
  apply hB
  change B = finiteSupportGradedEmbedding K 0 * D at hD
  rw [map_zero, zero_mul] at hD
  exact hD

/-- The normalized maximal finite-support divisor of a nonzero graded element is monic. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {B : DegreeGraded K} (hB : B ≠ 0) :
    HahnSeries.Nonpositive.IsMonicFiniteSupport
      (gradedNormalizedMaximalFiniteSupportDivisor B) := by
  apply HahnSeries.Nonpositive.normalizedAssociateRepresentative_isMonic_of_ne_zero
  exact gradedMaximalFiniteSupportDivisor_ne_zero_of_ne_zero hgcd hB

/-- Under pairwise greatest-common-divisor existence, the chosen representative satisfies the
source-level normalized maximal-divisor predicate. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B : DegreeGraded K) :
    IsNormalizedGradedMaximalFiniteSupportDivisor B
      (gradedNormalizedMaximalFiniteSupportDivisor B) := by
  constructor
  · exact (isGradedMaximalFiniteSupportDivisor_mk_iff B _).mp
      (gradedNormalizedMaximalFiniteSupportDivisor_isMaximal_of_exists_gcd hgcd B)
  · by_cases hB : B = 0
    · subst B
      apply Or.inl
      refine ⟨rfl, ?_⟩
      have hmax := gradedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd 0
      have hzero : IsGradedMaximalFiniteSupportDivisor (0 : DegreeGraded K) 0 := by
        rw [isGradedMaximalFiniteSupportDivisor_iff]
        intro q
        constructor
        · intro _
          exact dvd_zero _
        · intro _
          exact Associates.mk_le_mk_of_dvd (dvd_zero q)
      have hclass := IsGradedMaximalFiniteSupportDivisor.eq hmax hzero
      rw [gradedNormalizedMaximalFiniteSupportDivisor, hclass,
        HahnSeries.Nonpositive.normalizedAssociateRepresentative_zero]
    · exact Or.inr ⟨hB,
        gradedNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hB⟩

omit [CharZero K] in
/-- The normalized maximal-divisor predicate determines at most one finite-support series when all
units are nonzero constant series. -/
theorem IsNormalizedGradedMaximalFiniteSupportDivisor.eq (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    {B : DegreeGraded K}
    {p q : FiniteSupportRing (K := K)}
    (hp : IsNormalizedGradedMaximalFiniteSupportDivisor B p)
    (hq : IsNormalizedGradedMaximalFiniteSupportDivisor B q) :
    p = q := by
  have hpMax :=
    (isGradedMaximalFiniteSupportDivisor_mk_iff B p).mpr hp.1
  have hqMax :=
    (isGradedMaximalFiniteSupportDivisor_mk_iff B q).mpr hq.1
  have hclasses : Associates.mk p = Associates.mk q :=
    IsGradedMaximalFiniteSupportDivisor.eq hpMax hqMax
  rcases hp.2 with hpZero | hpNonzero
  · rcases hq.2 with hqZero | hqNonzero
    · exact hpZero.2.trans hqZero.2.symm
    · exact (hqNonzero.1 hpZero.1).elim
  · rcases hq.2 with hqZero | hqNonzero
    · exact (hpNonzero.1 hqZero.1).elim
    · have hpNormalized :
          HahnSeries.Nonpositive.IsNormalizedAssociateRepresentative
            (Associates.mk p) p :=
        (HahnSeries.Nonpositive.isNormalizedAssociateRepresentative_iff
          (Associates.mk p) p).mpr
            (Or.inr ⟨Associates.mk_ne_zero.mpr hpNonzero.2.ne_zero,
              rfl, hpNonzero.2⟩)
      have hqNormalized :
          HahnSeries.Nonpositive.IsNormalizedAssociateRepresentative
            (Associates.mk p) q :=
        (HahnSeries.Nonpositive.isNormalizedAssociateRepresentative_iff
          (Associates.mk p) q).mpr
            (Or.inr ⟨Associates.mk_ne_zero.mpr hpNonzero.2.ne_zero,
              hclasses.symm, hqNonzero.2⟩)
      exact hpNormalized.eq hunits hqNormalized

/-- Any series satisfying the normalized maximal-divisor predicate is the chosen normalized
representative, under pairwise greatest-common-divisor existence and the unit classification. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_eq_of_is
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    {B : DegreeGraded K}
    {p : FiniteSupportRing (K := K)}
    (hp : IsNormalizedGradedMaximalFiniteSupportDivisor B p) :
    gradedNormalizedMaximalFiniteSupportDivisor B = p := by
  exact (gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B).eq hunits hp

/-- Representative form of LM24, Proposition 5.4.8: the product of the normalized maximal
finite-support divisors divides the normalized maximal finite-support divisor of the product. -/
theorem gradedNormalizedMaximalFiniteSupportDivisor_mul_dvd_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (B C : DegreeGraded K) :
    gradedNormalizedMaximalFiniteSupportDivisor B *
        gradedNormalizedMaximalFiniteSupportDivisor C ∣
      gradedNormalizedMaximalFiniteSupportDivisor (B * C) := by
  apply Associates.mk_le_mk_iff_dvd.mp
  rw [← Associates.mk_mul_mk,
    gradedNormalizedMaximalFiniteSupportDivisor_mk,
    gradedNormalizedMaximalFiniteSupportDivisor_mk,
    gradedNormalizedMaximalFiniteSupportDivisor_mk]
  exact gradedMaximalFiniteSupportDivisor_mul_le_of_exists_gcd hgcd B C

end

end Berarducci
