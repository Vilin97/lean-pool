/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof

/-!
# LM24 maximal finite-support divisor statements

This module gives representative-valued statements of LM24, Proposition 5.4.3 and Corollary
5.4.4. The proved core first constructs the maximal divisor intrinsically in the associates of
the finite-support ring. Here LM24, Fact 2.5.2 is used only to supply pairwise gcds and to identify
the units with nonzero constant series.

The proposition is stated in the multiplicative RV quotient, whereas the corollary is stated in
the full degree-graded ring. These two divisibility relations are not conflated.
The proofs use Berarducci ordinal-value multiplicativity. Degree multiplicativity is an explicit
hypothesis.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]

private theorem rv_representative_spec_and_uniqueness (B : HahnDegreeRV K)
    (p : FiniteSupportRing (K := K))
    (hp : IsRVMaximalFiniteSupportDivisor B (Associates.mk p)) :
    (∀ q : FiniteSupportRing (K := K),
        finiteSupportRVEmbedding K q ∣ B ↔ q ∣ p) ∧
      ∀ p' : FiniteSupportRing (K := K),
        (∀ q : FiniteSupportRing (K := K),
          finiteSupportRVEmbedding K q ∣ B ↔ q ∣ p') →
        ∃ k : K, k ≠ 0 ∧
          p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  have hpSpec :=
    (isRVMaximalFiniteSupportDivisor_mk_iff B p).mp hp
  refine ⟨hpSpec, ?_⟩
  intro p' hp'Spec
  have hp' :=
    (isRVMaximalFiniteSupportDivisor_mk_iff B p').mpr hp'Spec
  exact HahnSeries.Nonpositive.exists_nonzero_scalar_mul_of_mk_eq_mk
    (HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
      (G := ℝ) (K := K))
    (IsRVMaximalFiniteSupportDivisor.eq hp hp')

/-- LM24, Proposition 5.4.3: every RV class has a finite-support series with exactly the same
finite-support divisors. It is unique up to a nonzero scalar and can be chosen constant when the
RV class is principal. -/
theorem rv_maximal_finite_support_divisor (B : HahnDegreeRV K) :
    ∃ p : FiniteSupportRing (K := K),
      (∀ q : FiniteSupportRing (K := K),
        finiteSupportRVEmbedding K q ∣ B ↔ q ∣ p) ∧
      (∀ p' : FiniteSupportRing (K := K),
        (∀ q : FiniteSupportRing (K := K),
          finiteSupportRVEmbedding K q ∣ B ↔ q ∣ p') →
        ∃ k : K, k ≠ 0 ∧
          p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p) ∧
      (IsPrincipalRV B →
        ∃ k : K,
          p = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k) := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  by_cases hBPrincipal : IsPrincipalRV B
  · obtain ⟨k, hk⟩ :=
      exists_scalar_isRVMaximalFiniteSupportDivisor_of_isPrincipal B hBPrincipal
    obtain ⟨hkSpec, hkUnique⟩ :=
      rv_representative_spec_and_uniqueness B
        (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k) hk
    exact ⟨HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k,
      hkSpec, hkUnique, fun _ ↦ ⟨k, rfl⟩⟩
  · obtain ⟨a, ha, _⟩ :=
      existsUnique_isRVMaximalFiniteSupportDivisor_of_exists_gcd hgcd B
    induction a using Quotient.inductionOn with
    | _ p =>
        obtain ⟨hpSpec, hpUnique⟩ :=
          rv_representative_spec_and_uniqueness B p ha
        exact ⟨p, hpSpec, hpUnique, fun hB ↦ (hBPrincipal hB).elim⟩

omit [CharZero K] in
private theorem graded_representative_spec_and_uniqueness (B : DegreeGraded K)
    (p : FiniteSupportRing (K := K))
    (hp : IsGradedMaximalFiniteSupportDivisor B (Associates.mk p)) :
    (∀ q : FiniteSupportRing (K := K),
        finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p) ∧
      ∀ p' : FiniteSupportRing (K := K),
        (∀ q : FiniteSupportRing (K := K),
          finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p') →
        ∃ k : K, k ≠ 0 ∧
          p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  have hpSpec :=
    (isGradedMaximalFiniteSupportDivisor_mk_iff B p).mp hp
  refine ⟨hpSpec, ?_⟩
  intro p' hp'Spec
  have hp' :=
    (isGradedMaximalFiniteSupportDivisor_mk_iff B p').mpr hp'Spec
  exact HahnSeries.Nonpositive.exists_nonzero_scalar_mul_of_mk_eq_mk
    (HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
      (G := ℝ) (K := K))
    (IsGradedMaximalFiniteSupportDivisor.eq hp hp')

/-- LM24, Corollary 5.4.4: every element of the full associated graded ring has a finite-support
series with exactly the same finite-support divisors, unique up to a nonzero scalar. -/
theorem graded_maximal_finite_support_divisor (B : DegreeGraded K) :
    ∃ p : FiniteSupportRing (K := K),
      (∀ q : FiniteSupportRing (K := K),
        finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p) ∧
      ∀ p' : FiniteSupportRing (K := K),
        (∀ q : FiniteSupportRing (K := K),
          finiteSupportGradedEmbedding K q ∣ B ↔ q ∣ p') →
        ∃ k : K, k ≠ 0 ∧
          p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isGradedMaximalFiniteSupportDivisor_of_exists_gcd hgcd B
  induction a using Quotient.inductionOn with
  | _ p =>
      obtain ⟨hpSpec, hpUnique⟩ :=
        graded_representative_spec_and_uniqueness B p ha
      exact ⟨p, hpSpec, hpUnique⟩

/-- LM24, Notation 5.4.5: there is exactly one maximal finite-support divisor that is zero for
the zero graded element and monic for every nonzero graded element. -/
theorem existsUnique_normalized_maximal_finite_support_divisor (B : DegreeGraded K) :
    ∃! p : FiniteSupportRing (K := K),
      IsNormalizedGradedMaximalFiniteSupportDivisor B p := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  let hunits := HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar
    (G := ℝ) (K := K)
  refine ⟨gradedNormalizedMaximalFiniteSupportDivisor B, ?_, ?_⟩
  · exact gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B
  · intro p hp
    exact (gradedNormalizedMaximalFiniteSupportDivisor_eq_of_is hgcd hunits hp).symm

/-- The normalized maximal finite-support divisor satisfies its source-level defining
predicate. -/
theorem maximalFiniteSupportDivisor_is (B : DegreeGraded K) :
    IsNormalizedGradedMaximalFiniteSupportDivisor B
      (gradedNormalizedMaximalFiniteSupportDivisor B) := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  exact gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd B

/-- LM24, Remark 5.4.6: the maximal finite-support divisor embeds as a divisor of the graded
element. -/
theorem maximalFiniteSupportDivisor_dvd (B : DegreeGraded K) :
    finiteSupportGradedEmbedding K
        (gradedNormalizedMaximalFiniteSupportDivisor B) ∣ B := by
  have h := (isNormalizedGradedMaximalFiniteSupportDivisor_iff B
    (gradedNormalizedMaximalFiniteSupportDivisor B)).mp
      (maximalFiniteSupportDivisor_is B)
  exact (h.1 (gradedNormalizedMaximalFiniteSupportDivisor B)).mpr dvd_rfl

variable (K) in
/-- The maximal finite-support divisor of zero is zero. -/
@[simp]
theorem maximalFiniteSupportDivisor_zero :
    gradedNormalizedMaximalFiniteSupportDivisor
      (0 : DegreeGraded K) = 0 := by
  have hspec := (isNormalizedGradedMaximalFiniteSupportDivisor_iff (0 : DegreeGraded
    K)
    (gradedNormalizedMaximalFiniteSupportDivisor 0)).mp
      (maximalFiniteSupportDivisor_is 0)
  rcases hspec.2 with h | h
  · exact h.2
  · exact (h.1 rfl).elim

/-- The maximal finite-support divisor of a nonzero graded element is monic. -/
theorem maximalFiniteSupportDivisor_isMonic {B : DegreeGraded K} (hB : B ≠ 0) :
    HahnSeries.Nonpositive.IsMonicFiniteSupport
      (gradedNormalizedMaximalFiniteSupportDivisor B) := by
  have hspec := (isNormalizedGradedMaximalFiniteSupportDivisor_iff B
    (gradedNormalizedMaximalFiniteSupportDivisor B)).mp
      (maximalFiniteSupportDivisor_is B)
  rcases hspec.2 with h | h
  · exact (hB h.1).elim
  · exact h.2

/-- LM24, Proposition 5.4.8: the product of the two normalized maximal finite-support divisors
divides the normalized maximal finite-support divisor of the product. -/
theorem maximalFiniteSupportDivisor_mul_dvd (B C : DegreeGraded K) :
    gradedNormalizedMaximalFiniteSupportDivisor B *
        gradedNormalizedMaximalFiniteSupportDivisor C ∣
      gradedNormalizedMaximalFiniteSupportDivisor (B * C) := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  exact gradedNormalizedMaximalFiniteSupportDivisor_mul_dvd_of_exists_gcd hgcd B C

end Berarducci
