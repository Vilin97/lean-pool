/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.PrincipalMaximalFinite
import Mathlib.Tactic.NormNum

/-!
# API checks for principal-factor invariance

These checks exercise the field-generic cores of LM24, Lemmas 6.3.1--6.3.2. The finite-support
factor is the nonconstant monomial `t⁻¹`. The RV principal factor is represented by the
approach-zero series, so it is nonzero and nonconstant.

For the full graded result, the principal factor has independently nonzero components in degrees
zero and one. It therefore tests `P̂` rather than a single RV component. A final boundary check
shows that replacing the nonzero principal factor by zero changes the maximal divisor. Pairwise
gcd existence remains an explicit parameter in these generic checks.
-/

open scoped DirectSum HahnSeries NatOrdinal

namespace Tests

public noncomputable section

private theorem approachZero_ordinalValue_bound :
    Berarducci.ordinalValue approachZeroNonpositive < ω^ (1 + 1 : NatOrdinal) := by
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The nonzero class in `P_1` represented by the approach-zero series. -/
def principalInvariantApproachZeroLayer : Berarducci.PrincipalComponent ℚ 1 :=
  Berarducci.principalComponentMk 1 approachZeroNonpositive
    approachZero_ordinalValue_bound

/-- The approach-zero class survives in the degree-one principal quotient. -/
theorem principalInvariantApproachZeroLayer_ne_zero :
    principalInvariantApproachZeroLayer ≠ 0 := by
  rw [principalInvariantApproachZeroLayer, ne_eq,
    Berarducci.principalComponentMk_eq_zero_iff,
    Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
      approachZero_degree_eq_one]
  exact lt_irrefl _

/-- The grade-zero principal class of the coefficient one. -/
def principalInvariantScalarLayer : Berarducci.PrincipalComponent ℚ 0 :=
  Berarducci.principalComponentScalarHom ℚ 1

/-- The grade-zero class of one is nonzero. -/
theorem principalInvariantScalarLayer_ne_zero :
    principalInvariantScalarLayer ≠ 0 := by
  rw [principalInvariantScalarLayer,
    Berarducci.principalComponentScalarHom_apply, ne_eq,
    Berarducci.principalComponentMk_eq_zero_iff,
    Berarducci.ordinalValue_C_of_ne one_ne_zero]
  simpa only [NatOrdinal.wpow_zero] using (lt_irrefl (1 : NatOrdinal))

/-- An intrinsic principal graded element supported in degrees zero and one. -/
def principalInvariantTwoGrade : Berarducci.PrincipalSubring ℚ :=
  DirectSum.of _ 0 principalInvariantScalarLayer +
    DirectSum.of _ 1 principalInvariantApproachZeroLayer

/-- The two prescribed components of the intrinsic principal graded fixture are unchanged. -/
theorem principalInvariantTwoGrade_components :
    principalInvariantTwoGrade 0 = principalInvariantScalarLayer ∧
      principalInvariantTwoGrade 1 = principalInvariantApproachZeroLayer := by
  simp [principalInvariantTwoGrade, DirectSum.of_apply]

/-- The positive-degree component makes the intrinsic two-grade fixture nonzero. -/
theorem principalInvariantTwoGrade_ne_zero :
    principalInvariantTwoGrade ≠ 0 := by
  intro hzero
  apply principalInvariantApproachZeroLayer_ne_zero
  rw [← principalInvariantTwoGrade_components.2, hzero]
  rfl

/-- The two-degree example embedded in the degree-graded ring. -/
def principalInvariantGraded : Berarducci.DegreeGraded ℚ :=
  Berarducci.principalSubringEmbedding ℚ
    principalInvariantTwoGrade

/-- The embedded two-grade fixture satisfies the componentwise definition of `P̂`. -/
theorem principalInvariantGraded_isPrincipal :
    Berarducci.IsPrincipalGraded
      principalInvariantGraded := by
  rw [Berarducci.isPrincipalGraded_iff]
  intro α
  rw [principalInvariantGraded,
    Berarducci.principalSubringEmbedding_apply]
  exact Berarducci.principalComponentToHahnDegreeLayer_isPrincipal α (principalInvariantTwoGrade α)

/-- Injectivity of the canonical graded embedding preserves nonzeroness of the fixture. -/
theorem principalInvariantGraded_ne_zero :
    principalInvariantGraded ≠ 0 := by
  intro hzero
  rw [principalInvariantGraded] at hzero
  apply principalInvariantTwoGrade_ne_zero
  apply Berarducci.principalSubringEmbedding_injective ℚ
  simpa using hzero

/-- The full graded principal factor has independently nonzero components in degrees zero and
one. -/
theorem principalInvariantGraded_components_ne_zero :
    principalInvariantGraded 0 ≠ 0 ∧
      principalInvariantGraded 1 ≠ 0 := by
  constructor
  · rw [principalInvariantGraded, Berarducci.principalSubringEmbedding_apply,
      principalInvariantTwoGrade_components.1]
    intro hzero
    apply principalInvariantScalarLayer_ne_zero
    apply Berarducci.principalComponentToHahnDegreeLayer_injective ℚ 0
    simpa using hzero
  · rw [principalInvariantGraded, Berarducci.principalSubringEmbedding_apply,
      principalInvariantTwoGrade_components.2]
    intro hzero
    apply principalInvariantApproachZeroLayer_ne_zero
    apply Berarducci.principalComponentToHahnDegreeLayer_injective ℚ 1
    simpa using hzero

/-- The strictly negative exponent used by the nonconstant finite-support fixture. -/
def principalInvariantNegativeExponent :
    HahnSeries.Nonpositive.exponentMonoid ℝ :=
  ⟨-1, show (-1 : ℝ) ≤ 0 by norm_num⟩

/-- The nonconstant finite-support monomial `t⁻¹`. -/
def principalInvariantFiniteMonomial : Berarducci.FiniteSupportRing (K := ℚ) :=
  HahnSeries.Nonpositive.finiteSupportMonomial principalInvariantNegativeExponent

/-- The coefficient at exponent `-1` proves that the finite-support fixture is nonzero. -/
theorem principalInvariantFiniteMonomial_ne_zero :
    principalInvariantFiniteMonomial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun p : Berarducci.FiniteSupportRing (K := ℚ) ↦
      (((p : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).coeff (-1))) hzero
  simp [principalInvariantFiniteMonomial,
    principalInvariantNegativeExponent] at hcoeff

/-- The degree-RV class represented by the approach-zero principal series. -/
def principalInvariantRV : Berarducci.HahnDegreeRV ℚ :=
  (HahnSeries.Nonpositive.degreeValuation ℚ).rv
    approachZeroNonpositive

/-- The approach-zero RV fixture is principal in the exact sense of LM24, Definition 5.2.1. -/
theorem principalInvariantRV_isPrincipal :
    Berarducci.IsPrincipalRV principalInvariantRV :=
  (Berarducci.isPrincipalRV_iff _).mpr
    ⟨approachZeroNonpositive, approachZero_isPrincipal, rfl⟩

/-- Separatedness of the degree valuation proves that the approach-zero RV fixture is nonzero. -/
theorem principalInvariantRV_ne_zero : principalInvariantRV ≠ 0 := by
  intro hzero
  let w := HahnSeries.Nonpositive.degreeValuation ℚ
  have hbot : w approachZeroNonpositive = ⊥ := by
    exact w.rv_eq_zero_iff.mp hzero
  have hsep :=
    (MaxAddDegree.isSeparated_iff w).mp
      (HahnSeries.Nonpositive.degreeValuation_isSeparated ℚ)
  exact approachZero_ne_zero ((hsep approachZeroNonpositive).mp hbot)

/-- Multiplication by the nonhomogeneous two-grade principal fixture preserves the normalized
maximal finite-support divisor of the negative monomial. -/
theorem principalInvariant_fullGraded (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ),
          e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        (Berarducci.finiteSupportGradedEmbedding ℚ
            principalInvariantFiniteMonomial *
          principalInvariantGraded) =
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        (Berarducci.finiteSupportGradedEmbedding ℚ
          principalInvariantFiniteMonomial) := by
  exact
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_mul_principal_eq_of_exists_gcd hgcd _
      principalInvariantGraded_isPrincipal
        principalInvariantGraded_ne_zero

/-- The same nonzero graded input has a different normalized maximal divisor after multiplication
by zero, certifying the nonzero-factor boundary. -/
theorem principalInvariant_zero_factor_changes_divisor
    (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ),
          e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        (Berarducci.finiteSupportGradedEmbedding ℚ
            principalInvariantFiniteMonomial * 0) ≠
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        (Berarducci.finiteSupportGradedEmbedding ℚ
          principalInvariantFiniteMonomial) := by
  have hB : Berarducci.finiteSupportGradedEmbedding ℚ
      principalInvariantFiniteMonomial ≠ 0 := by
    intro hzero
    apply principalInvariantFiniteMonomial_ne_zero
    apply Berarducci.finiteSupportGradedEmbedding_injective ℚ
    simpa using hzero
  have hright :=
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hB |>.ne_zero
  have hleft :
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
          (Berarducci.finiteSupportGradedEmbedding ℚ
              principalInvariantFiniteMonomial * 0) = 0 := by
    rw [mul_zero]
    have hspec :=
      (Berarducci.isNormalizedGradedMaximalFiniteSupportDivisor_iff (0 :
        Berarducci.DegreeGraded ℚ) _).mp
          (Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd
              (0 : Berarducci.DegreeGraded ℚ))
    rcases hspec.2 with hzero | hnonzero
    · exact hzero.2
    · exact (hnonzero.1 rfl).elim
  rw [hleft]
  exact Ne.symm hright

/-- Multiplication by the nonconstant approach-zero principal RV class preserves the normalized
maximal finite-support divisor of the negative-monomial RV class. -/
theorem principalInvariant_rv (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ),
          e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        ((HahnSeries.Nonpositive.degreeValuation ℚ).rvInitialFormHom
          (Berarducci.finiteSupportRVEmbedding ℚ principalInvariantFiniteMonomial *
            principalInvariantRV)) =
      Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        ((HahnSeries.Nonpositive.degreeValuation ℚ).rvInitialFormHom
          (Berarducci.finiteSupportRVEmbedding ℚ
            principalInvariantFiniteMonomial)) := by
  exact
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_rv_mul_principal_eq_of_exists_gcd hgcd _
      principalInvariantRV_isPrincipal
        principalInvariantRV_ne_zero

end

end Tests
