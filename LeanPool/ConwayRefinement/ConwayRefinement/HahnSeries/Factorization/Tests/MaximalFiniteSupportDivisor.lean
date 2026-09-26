/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite
public import Mathlib.Basic.Real.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

/-!
# API checks for normalized maximal finite-support divisors

The two-term fixture has support `{-1, 0}`, coefficient `2` at its least exponent, and coefficient
`1` at its greatest exponent. It is therefore monic in the precise sense used by LM24, Notation
5.4.5, while the nearby incorrect definition that normalizes at the least exponent rejects it.

The RV fixture is the class of that nonconstant series. Its checks use the actual multiplicative
RV quotient and freeze the orientation `q ∣ B ↔ q ∣ p` from LM24, Proposition 5.4.3. A second
fixture has independently nonzero components in degrees zero and one; it tests the full direct-sum
graded ring of Corollary 5.4.4 rather than a single homogeneous class. The final certificate states
only the one-sided divisibility of Proposition 5.4.8. Pairwise gcd existence and the unit
classification of the finite-support ring remain explicit parameters.
-/

open scoped DirectSum HahnSeries NatOrdinal

public noncomputable section

namespace Tests

/-- A two-term finite-support series whose coefficients distinguish greatest-endpoint
normalization from least-endpoint normalization. -/
def normalizationAsymmetricSeries : HahnSeries.Nonpositive ℝ ℚ :=
  HahnSeries.Nonpositive.C 1 +
    HahnSeries.Nonpositive.single (-1) 2 (by norm_num)

/-- The asymmetric series has finite support. -/
theorem normalizationAsymmetricSeries_mem :
    normalizationAsymmetricSeries ∈
      (HahnSeries.Nonpositive.finiteSupportSubring :
        Subring (HahnSeries.Nonpositive ℝ ℚ)) := by
  rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff]
  apply Set.Finite.subset
    ((Set.finite_singleton 0).union (Set.finite_singleton (-1)))
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with hx | hx
  · left
    rw [HahnSeries.Nonpositive.coe_C] at hx
    exact HahnSeries.support_single_subset hx
  · right
    rw [HahnSeries.Nonpositive.coe_single] at hx
    exact HahnSeries.support_single_subset hx

/-- The asymmetric fixture as an element of the finite-support subring. -/
def normalizationAsymmetric :
    HahnSeries.Nonpositive.finiteSupportSubring (G := ℝ) (K := ℚ) :=
  ⟨normalizationAsymmetricSeries, normalizationAsymmetricSeries_mem⟩

/-- The greatest exponent of the asymmetric fixture is zero. -/
theorem normalizationAsymmetric_greatest :
    IsGreatest
      (((normalizationAsymmetric : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).support) 0 := by
  constructor
  · rw [HahnSeries.mem_support]
    simp [normalizationAsymmetric, normalizationAsymmetricSeries]
  · intro x hx
    exact HahnSeries.Nonpositive.support_subset
      (normalizationAsymmetric : HahnSeries.Nonpositive ℝ ℚ) hx

/-- The least exponent of the asymmetric fixture is `-1`. -/
theorem normalizationAsymmetric_least :
    IsLeast
      (((normalizationAsymmetric : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).support)
      (-1) := by
  constructor
  · rw [HahnSeries.mem_support]
    simp [normalizationAsymmetric, normalizationAsymmetricSeries]
  · intro x hx
    have hx' : x ∈ (normalizationAsymmetricSeries : ℚ⟦ℝ⟧).support := by
      simpa [normalizationAsymmetric] using hx
    rcases HahnSeries.support_add_subset _ _ hx' with hxConstant | hxNegative
    · rw [HahnSeries.Nonpositive.coe_C] at hxConstant
      have hxZero : x = 0 := by
        simpa using HahnSeries.support_single_subset hxConstant
      rw [hxZero]
      norm_num
    · rw [HahnSeries.Nonpositive.coe_single] at hxNegative
      have hxNegOne : x = -1 := by
        simpa using HahnSeries.support_single_subset hxNegative
      rw [hxNegOne]

/-- The coefficient at the greatest exponent is one. -/
theorem normalizationAsymmetric_coeff_greatest :
    ((normalizationAsymmetric : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).coeff 0 = 1 := by
  simp [normalizationAsymmetric, normalizationAsymmetricSeries]

/-- The coefficient at the least exponent is two, not one. -/
theorem normalizationAsymmetric_coeff_least :
    ((normalizationAsymmetric : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).coeff (-1) = 2 := by
  simp [normalizationAsymmetric, normalizationAsymmetricSeries]

/-- The fixture satisfies the intended greatest-exponent normalization. -/
theorem normalizationAsymmetric_isMonic :
    HahnSeries.Nonpositive.IsMonicFiniteSupport normalizationAsymmetric := by
  rw [HahnSeries.Nonpositive.isMonicFiniteSupport_iff]
  exact ⟨0, normalizationAsymmetric_greatest,
    normalizationAsymmetric_coeff_greatest⟩

/-- The fixture rejects normalization at the least support exponent. -/
theorem normalizationAsymmetric_least_coeff_ne_one :
    ((normalizationAsymmetric : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).coeff
      (-1) ≠ 1 := by
  rw [normalizationAsymmetric_coeff_least]
  norm_num

/-- The nonconstant fixture is a normalized representative of its own associate class. -/
theorem normalizationAsymmetric_isNormalizedRepresentative :
    HahnSeries.Nonpositive.IsNormalizedAssociateRepresentative
      (Associates.mk normalizationAsymmetric) normalizationAsymmetric := by
  rw [HahnSeries.Nonpositive.isNormalizedAssociateRepresentative_iff]
  exact Or.inr
    ⟨Associates.mk_ne_zero.mpr normalizationAsymmetric_isMonic.ne_zero,
      rfl, normalizationAsymmetric_isMonic⟩

/-- The chosen normalized representative preserves the fixture's nonzero associate class. -/
theorem normalizationAsymmetric_chosen_mk :
    Associates.mk
        (HahnSeries.Nonpositive.normalizedAssociateRepresentative
          (Associates.mk normalizationAsymmetric)) =
      Associates.mk normalizationAsymmetric :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative_mk _

/-- The chosen representative of the fixture's associate class is monic. -/
theorem normalizationAsymmetric_chosen_isMonic :
    HahnSeries.Nonpositive.IsMonicFiniteSupport
      (HahnSeries.Nonpositive.normalizedAssociateRepresentative
        (Associates.mk normalizationAsymmetric)) :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative_isMonic_of_ne_zero
    (Associates.mk_ne_zero.mpr normalizationAsymmetric_isMonic.ne_zero)

/-- The normalized representative of the zero associate class is zero. -/
theorem normalization_zero_class :
    HahnSeries.Nonpositive.normalizedAssociateRepresentative
      (0 : Associates
        (HahnSeries.Nonpositive.finiteSupportSubring (G := ℝ) (K := ℚ))) = 0 := by
  rw [HahnSeries.Nonpositive.normalizedAssociateRepresentative_zero]

/-- The asymmetric fixture is not a coefficient scalar. -/
theorem normalizationAsymmetric_not_scalar (k : ℚ) :
    normalizationAsymmetric ≠
      HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k := by
  intro h
  have hcoeff := congrArg
    (fun p : HahnSeries.Nonpositive.finiteSupportSubring (G := ℝ) (K := ℚ) ↦
      (((p : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).coeff (-1))) h
  rw [normalizationAsymmetric_coeff_least] at hcoeff
  rw [HahnSeries.Nonpositive.coe_finiteSupportScalarHom] at hcoeff
  change 2 = (HahnSeries.C k).coeff (-1) at hcoeff
  rw [HahnSeries.C_apply,
    HahnSeries.coeff_single_of_ne (by norm_num : (-1 : ℝ) ≠ 0)] at hcoeff
  norm_num at hcoeff

/-- The actual degree-RV class of the nonconstant asymmetric finite-support series. -/
def maximalFiniteRVFixture : Berarducci.HahnDegreeRV ℚ :=
  Berarducci.finiteSupportRVEmbedding ℚ normalizationAsymmetric

/-- The nonconstant finite-support series gives a nonzero RV class. -/
theorem maximalFiniteRVFixture_ne_zero :
    maximalFiniteRVFixture ≠ 0 := by
  intro h
  apply normalizationAsymmetric_isMonic.ne_zero
  apply Berarducci.finiteSupportRVEmbedding_injective ℚ
  simpa [maximalFiniteRVFixture] using h

/-- The RV fixture has a representative satisfying the exact divisibility orientation of LM24,
Proposition 5.4.3. -/
theorem maximalFiniteRVFixture_exists_spec (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ),
          e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    ∃ p : Berarducci.FiniteSupportRing (K := ℚ),
      ∀ q : Berarducci.FiniteSupportRing (K := ℚ),
        Berarducci.finiteSupportRVEmbedding ℚ q ∣
            maximalFiniteRVFixture ↔
          q ∣ p := by
  obtain ⟨a, ha, _⟩ :=
    Berarducci.existsUnique_isRVMaximalFiniteSupportDivisor_of_exists_gcd hgcd
      maximalFiniteRVFixture
  induction a using Quotient.inductionOn with
  | _ p =>
      exact ⟨p,
        (Berarducci.isRVMaximalFiniteSupportDivisor_mk_iff maximalFiniteRVFixture p).mp ha⟩

/-- A nonzero element of the degree-zero component. -/
def maximalFiniteDegreeZero :
    (HahnSeries.Nonpositive.degreeValuation ℚ).Component 0 :=
  HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv ℚ 1

/-- The prescribed degree-zero component is nonzero. -/
theorem maximalFiniteDegreeZero_ne_zero :
    maximalFiniteDegreeZero ≠ 0 := by
  intro h
  let e := HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv ℚ
  change e 1 = 0 at h
  rw [← map_zero e] at h
  exact one_ne_zero (e.injective h)

/-- The degree-one component represented by the approach-zero principal series. -/
def maximalFiniteDegreeOne :
    (HahnSeries.Nonpositive.degreeValuation ℚ).Component 1 :=
  Berarducci.degreeLayerMk 1 approachZeroNonpositive
    approachZero_degree_eq_one.le

/-- The prescribed degree-one component is nonzero. -/
theorem maximalFiniteDegreeOne_ne_zero :
    maximalFiniteDegreeOne ≠ 0 := by
  rw [maximalFiniteDegreeOne, ne_eq,
    Berarducci.degreeLayerMk_eq_zero_iff, approachZero_degree_eq_one]
  exact lt_irrefl _

/-- An associated-graded element with independently nonzero components in degrees zero and one. -/
def maximalFiniteTwoComponentGraded :
    Berarducci.DegreeGraded ℚ :=
  DirectSum.of _ 0 maximalFiniteDegreeZero +
    DirectSum.of _ 1 maximalFiniteDegreeOne

/-- Both prescribed components survive in the direct sum. -/
theorem maximalFiniteTwoComponentGraded_components :
    maximalFiniteTwoComponentGraded 0 =
        maximalFiniteDegreeZero ∧
      maximalFiniteTwoComponentGraded 1 =
        maximalFiniteDegreeOne := by
  simp [maximalFiniteTwoComponentGraded, DirectSum.of_apply]

/-- The two-component graded fixture is nonzero. -/
theorem maximalFiniteTwoComponentGraded_ne_zero :
    maximalFiniteTwoComponentGraded ≠ 0 := by
  intro h
  apply maximalFiniteDegreeOne_ne_zero
  rw [← maximalFiniteTwoComponentGraded_components.2, h]
  rfl

/-- The two-component fixture has a representative satisfying the full-graded divisibility
characterization of LM24, Corollary 5.4.4. -/
theorem maximalFiniteTwoComponentGraded_exists_spec
    (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ),
          e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    ∃ p : Berarducci.FiniteSupportRing (K := ℚ),
      ∀ q : Berarducci.FiniteSupportRing (K := ℚ),
        Berarducci.finiteSupportGradedEmbedding ℚ q ∣
            maximalFiniteTwoComponentGraded ↔
          q ∣ p := by
  obtain ⟨a, ha, _⟩ :=
    Berarducci.existsUnique_isGradedMaximalFiniteSupportDivisor_of_exists_gcd hgcd
      maximalFiniteTwoComponentGraded
  induction a using Quotient.inductionOn with
  | _ p =>
      exact ⟨p,
        (Berarducci.isGradedMaximalFiniteSupportDivisor_mk_iff maximalFiniteTwoComponentGraded
          p).mp ha⟩

/-- The normalized maximal divisor of the nonzero two-component fixture is monic. -/
theorem maximalFiniteTwoComponentGraded_normalized_isMonic
    (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ),
          e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    HahnSeries.Nonpositive.IsMonicFiniteSupport
      (Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        maximalFiniteTwoComponentGraded) :=
  Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd
    maximalFiniteTwoComponentGraded_ne_zero

/-- LM24, Proposition 5.4.8, with its stated one-sided divisibility conclusion. -/
theorem maximalFiniteTwoComponentGraded_mul_dvd
    (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ),
          e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
          maximalFiniteTwoComponentGraded *
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
          maximalFiniteTwoComponentGraded ∣
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        (maximalFiniteTwoComponentGraded *
          maximalFiniteTwoComponentGraded) :=
  Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_mul_dvd_of_exists_gcd hgcd _ _

end Tests
