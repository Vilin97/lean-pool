/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.MaximalFiniteMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.PrincipalSubringPrimality
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.SeriesMaximalMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.SeriesPrimality
import Mathlib.Tactic.NormNum

/-!
# API checks for LM24, Corollaries 6.3.6--6.3.9

These checks compose the reductions underlying the final four results of LM24,
Section 6.3. The factor-witness checks retain both factors in the finite-support ring; they would
not follow from the weaker bare `IsPrimal` conclusions. The three-factor checks require literal
multiplicativity of the normalized maximal finite-support divisor, rather than the previously
proved one-sided divisibility.

The zero test preserves the absence of a nonzero hypothesis in Corollary 6.3.9. The final fixture
uses two genuinely nonconstant finite-support series, each with a nonzero coefficient at exponent
`-1`, to exercise Proposition 6.3.8 away from the constant and zero cases. The unresolved
mathematical prerequisites (gcd existence, scalar redistribution, unit classification) are
explicit parameters; the coefficient field has characteristic zero.
-/

open scoped HahnSeries

universe v

namespace Tests

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]
variable (hgcdK : ∀ p q : Berarducci.FiniteSupportRing (K := K),
  ∃ d : Berarducci.FiniteSupportRing (K := K),
    ∀ e : Berarducci.FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
variable (hgcdL : ∀ p q : Berarducci.PrincipalSubringFractionFiniteSupportRing K,
  ∃ d : Berarducci.PrincipalSubringFractionFiniteSupportRing K,
    ∀ e : Berarducci.PrincipalSubringFractionFiniteSupportRing K,
      e ∣ p ∧ e ∣ q ↔ e ∣ d)
variable (hredistribute : Berarducci.PrincipalSubringFractionScalarRedistribution K)
variable (hunits : ∀ u : Berarducci.FiniteSupportRing (K := K),
  IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
    u = finiteSupportScalarHom (G := ℝ) k)

include hgcdK hgcdL hredistribute in
/-- The generic reduction for Corollary 6.3.6 retains both factors in the finite-support
ring, rather than merely producing factors in the ambient associated graded ring. -/
theorem sectionSixThree_gradedFactorWitness (p : Berarducci.FiniteSupportRing (K := K))
    (B C : Berarducci.DegreeGraded K)
    (hp : Berarducci.finiteSupportGradedEmbedding K p ∣ B * C) :
    ∃ p₁ p₂ : Berarducci.FiniteSupportRing (K := K),
      p = p₁ * p₂ ∧
        Berarducci.finiteSupportGradedEmbedding K p₁ ∣ B ∧
        Berarducci.finiteSupportGradedEmbedding K p₂ ∣ C :=
  Berarducci.finiteSupportGradedEmbedding_exists_factor_dvd_of_scalarRedistribution hgcdK hgcdL
    hredistribute p B C hp

include hgcdK hgcdL hredistribute hunits in
/-- Iterated multiplication verifies that Corollary 6.3.7 supplies an equality, not merely
one-sided divisibility. -/
theorem sectionSixThree_gradedMaximal_three_mul (B C D : Berarducci.DegreeGraded K) :
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor ((B * C) * D) =
      (Berarducci.gradedNormalizedMaximalFiniteSupportDivisor B *
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor C) *
        Berarducci.gradedNormalizedMaximalFiniteSupportDivisor D := by
  have hfactor := sectionSixThree_gradedFactorWitness hgcdK hgcdL hredistribute
  have hmax := Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_mul_of_factorization hgcdK
    hunits hfactor
  rw [hmax (B * C) D, hmax B C]

include hgcdK hgcdL hredistribute hunits in
/-- Iterated multiplication verifies the exact equality in Proposition 6.3.8 at the series
level. -/
theorem sectionSixThree_seriesMaximal_three_mul (b c d : Berarducci.Series K) :
    Berarducci.seriesNormalizedMaximalFiniteSupportDivisor ((b * c) * d) =
      (Berarducci.seriesNormalizedMaximalFiniteSupportDivisor b *
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor c) *
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor d := by
  have hfactor := sectionSixThree_gradedFactorWitness hgcdK hgcdL hredistribute
  have hgraded :=
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_mul_of_factorization hgcdK hunits hfactor
  have hseries := Berarducci.seriesNormalizedMaximalFiniteSupportDivisor_mul_of_graded hgcdK hunits
    hgraded
  rw [hseries (b * c) d, hseries b c]

include hgcdK hgcdL hredistribute hunits in
/-- The stronger form of Corollary 6.3.9 retains finite-support factors and asserts their
product equality in the ambient Hahn-series ring. -/
theorem sectionSixThree_seriesFactorWitness
    (p : Berarducci.FiniteSupportRing (K := K)) (b c : Berarducci.Series K)
    (hp : (p : Berarducci.Series K) ∣ b * c) :
    ∃ p₁ p₂ : Berarducci.FiniteSupportRing (K := K),
      (p : Berarducci.Series K) =
          (p₁ : Berarducci.Series K) * (p₂ : Berarducci.Series K) ∧
        (p₁ : Berarducci.Series K) ∣ b ∧
        (p₂ : Berarducci.Series K) ∣ c := by
  have hfactor := sectionSixThree_gradedFactorWitness hgcdK hgcdL hredistribute
  have hgraded :=
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_mul_of_factorization hgcdK hunits hfactor
  have hseries := Berarducci.seriesNormalizedMaximalFiniteSupportDivisor_mul_of_graded hgcdK hunits
    hgraded
  obtain ⟨p₁, p₂, hpFactor, hp₁, hp₂⟩ :=
    Berarducci.finiteSupportSeries_exists_factor_dvd_of_maximalMultiplicative hgcdK hseries p b c hp
  refine ⟨p₁, p₂, ?_, hp₁, hp₂⟩
  exact congrArg
    (finiteSupportSubring (G := ℝ) (K := K)).subtype hpFactor

include hgcdK hgcdL hredistribute hunits in
/-- The zero finite-support element is included in the witness theorem, so no hidden
nonzeroness hypothesis has entered the reduction. -/
theorem sectionSixThree_zeroSeriesFactorWitness (b c : Berarducci.Series K) (hbc : b * c = 0) :
    ∃ p₁ p₂ : Berarducci.FiniteSupportRing (K := K),
      (0 : Berarducci.Series K) =
          (p₁ : Berarducci.Series K) * (p₂ : Berarducci.Series K) ∧
        (p₁ : Berarducci.Series K) ∣ b ∧
        (p₂ : Berarducci.Series K) ∣ c := by
  apply sectionSixThree_seriesFactorWitness hgcdK hgcdL hredistribute hunits 0 b c
  rw [hbc]
  exact dvd_refl 0

/-- The finite-support monomial `t⁻¹` used in the nonconstant multiplicativity fixture. -/
def sectionSixThreeNegativeMonomial : Berarducci.FiniteSupportRing (K := ℚ) :=
  finiteSupportMonomial (K := ℚ) ⟨-1, show (-1 : ℝ) ≤ 0 by norm_num⟩

/-- The first nonconstant factor `t⁻¹ + 1`. -/
def sectionSixThreeLeftSeries : Berarducci.Series ℚ :=
  ((sectionSixThreeNegativeMonomial + 1 : Berarducci.FiniteSupportRing (K := ℚ)) :
    Berarducci.Series ℚ)

/-- The second nonconstant factor `t⁻¹ - 1`. -/
def sectionSixThreeRightSeries : Berarducci.Series ℚ :=
  ((sectionSixThreeNegativeMonomial - 1 : Berarducci.FiniteSupportRing (K := ℚ)) :
    Berarducci.Series ℚ)

/-- Both concrete factors have coefficient one at exponent `-1`; their constant coefficients
are respectively one and negative one. In particular, neither factor is zero or constant. -/
theorem sectionSixThree_nonconstantFactors_coefficients :
    (sectionSixThreeLeftSeries : ℚ⟦ℝ⟧).coeff (-1) = 1 ∧
      (sectionSixThreeRightSeries : ℚ⟦ℝ⟧).coeff (-1) = 1 ∧
      (sectionSixThreeLeftSeries : ℚ⟦ℝ⟧).coeff 0 = 1 ∧
      (sectionSixThreeRightSeries : ℚ⟦ℝ⟧).coeff 0 = -1 := by
  simp [sectionSixThreeLeftSeries, sectionSixThreeRightSeries,
    sectionSixThreeNegativeMonomial]

/-- Proposition 6.3.8 applies as a literal equality to two concrete nonzero, nonconstant
finite-support series. -/
theorem sectionSixThree_nonconstantSeriesMaximal_mul
    (hgcdK : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
      ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
        ∀ e : Berarducci.FiniteSupportRing (K := ℚ), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hgcdL : ∀ p q : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ,
      ∃ d : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ,
        ∀ e : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ,
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hredistribute : Berarducci.PrincipalSubringFractionScalarRedistribution ℚ)
    (hunits : ∀ u : Berarducci.FiniteSupportRing (K := ℚ),
      IsUnit u ↔ ∃ k : ℚ, k ≠ 0 ∧
        u = finiteSupportScalarHom (G := ℝ) k) :
    Berarducci.seriesNormalizedMaximalFiniteSupportDivisor
        (sectionSixThreeLeftSeries * sectionSixThreeRightSeries) =
      Berarducci.seriesNormalizedMaximalFiniteSupportDivisor sectionSixThreeLeftSeries *
        Berarducci.seriesNormalizedMaximalFiniteSupportDivisor
          sectionSixThreeRightSeries := by
  have hfactor := sectionSixThree_gradedFactorWitness hgcdK hgcdL hredistribute
  have hgraded :=
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_mul_of_factorization hgcdK hunits hfactor
  exact Berarducci.seriesNormalizedMaximalFiniteSupportDivisor_mul_of_graded hgcdK hunits hgraded _
    _

end

end Tests
