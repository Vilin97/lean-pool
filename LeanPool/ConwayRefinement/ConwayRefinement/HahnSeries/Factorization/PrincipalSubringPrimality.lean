/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.PrincipalSubringLocalization

/-!
# Primality of finite-support elements in the degree-graded ring

This module proves the field-generic core of LM24, Corollary 6.3.6. A factorisation supplied in
the localization of `RV̂` is scalar-redistributed to the original coefficient field. Clearing its
two principal denominators and applying LM24, Lemma 6.3.2, then recovers divisibility in `RV̂`.

The stronger theorem retains both factors as elements of the finite-support ring. Primality of the
embedded element is derived from that witness theorem.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- A finite-support divisor of a product in `RV̂` factors into finite-support divisors of the
two factors, assuming scalar redistribution and pairwise greatest-common-divisor existence over
both coefficient fields. -/
theorem finiteSupportGradedEmbedding_exists_factor_dvd_of_scalarRedistribution
    (hgcdK : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hgcdL : ∀ p q : PrincipalSubringFractionFiniteSupportRing K,
      ∃ d : PrincipalSubringFractionFiniteSupportRing K,
        ∀ e : PrincipalSubringFractionFiniteSupportRing K,
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hredistribute : PrincipalSubringFractionScalarRedistribution K)
    (p : FiniteSupportRing (K := K))
    (B C : DegreeGraded K)
    (hp : finiteSupportGradedEmbedding K p ∣ B * C) :
    ∃ p₁ p₂ : FiniteSupportRing (K := K),
      p = p₁ * p₂ ∧
        finiteSupportGradedEmbedding K p₁ ∣ B ∧
        finiteSupportGradedEmbedding K p₂ ∣ C := by
  have hpLocalized :=
    principalSubringLocalizationMap_finiteSupport_dvd_mul hp
  obtain ⟨p₁, p₂, hpFactors, hp₁, hp₂⟩ :=
    principalSubringFractionScalarExtension_exists_factor_dvd_of_scalarRedistribution hredistribute
      hgcdL p
        (principalSubringLocalizationMap K B)
        (principalSubringLocalizationMap K C) hpLocalized
  refine ⟨p₁, p₂, hpFactors, ?_, ?_⟩
  · exact
      (principalSubringLocalizationMap_finiteSupport_dvd_iff_of_exists_gcd hgcdK p₁ B).mp hp₁
  · exact
      (principalSubringLocalizationMap_finiteSupport_dvd_iff_of_exists_gcd hgcdK p₂ C).mp hp₂

/-- Every embedded finite-support element is primal in `RV̂` under the same explicit
prerequisites. -/
theorem finiteSupportGradedEmbedding_isPrimal_of_scalarRedistribution
    (hgcdK : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hgcdL : ∀ p q : PrincipalSubringFractionFiniteSupportRing K,
      ∃ d : PrincipalSubringFractionFiniteSupportRing K,
        ∀ e : PrincipalSubringFractionFiniteSupportRing K,
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hredistribute : PrincipalSubringFractionScalarRedistribution K)
    (p : FiniteSupportRing (K := K)) :
    IsPrimal (finiteSupportGradedEmbedding K p) := by
  intro B C hp
  obtain ⟨p₁, p₂, hpFactors, hp₁, hp₂⟩ :=
    finiteSupportGradedEmbedding_exists_factor_dvd_of_scalarRedistribution hgcdK hgcdL
      hredistribute p B C hp
  refine ⟨finiteSupportGradedEmbedding K p₁,
    finiteSupportGradedEmbedding K p₂, hp₁, hp₂, ?_⟩
  rw [hpFactors, map_mul]

end

end Berarducci
