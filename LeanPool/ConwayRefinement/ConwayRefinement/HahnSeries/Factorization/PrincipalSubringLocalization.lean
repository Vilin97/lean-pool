/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringLocalization

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.PrincipalMaximalFinite

/-!
# Finite-support divisibility and principal graded localization

The localization of `RV̂` at the nonzero elements of `P̂` does not create new divisibility
relations by finite-support series. For the nontrivial direction, clear a principal denominator
and then use the field-generic core of LM24, Lemma 6.3.2, to remove that denominator.

This is the precise localization step used in the proof of LM24, Corollary 6.3.6.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- Divisibility by an embedded finite-support series is reflected by localization at nonzero
principal graded factors. -/
theorem principalSubringLocalizationMap_finiteSupport_dvd_iff_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (p : FiniteSupportRing (K := K))
    (B : DegreeGraded K) :
    principalSubringFractionScalarExtension K p ∣
        principalSubringLocalizationMap K B ↔
      finiteSupportGradedEmbedding K p ∣ B := by
  constructor
  · intro hp
    obtain ⟨X, d, hd, hclear⟩ :=
      principalSubringLocalization_exists_finiteSupport_dvd_mul_principal hp
    have hdivPrincipal :
        finiteSupportGradedEmbedding K p ∣
          B * principalSubringEmbedding K d :=
      ⟨X, hclear⟩
    have hdPrincipal :
        IsPrincipalGraded
          (principalSubringEmbedding K d) :=
      principalSubringEmbedding_isPrincipal d
    have hdImage : principalSubringEmbedding K d ≠ 0 := by
      intro hzero
      apply hd
      apply principalSubringEmbedding_injective K
      simpa using hzero
    exact
      (finiteSupportGradedEmbedding_dvd_mul_principal_iff_of_exists_gcd hgcd p B hdPrincipal
        hdImage).mp hdivPrincipal
  · exact principalSubringLocalizationMap_finiteSupport_dvd

end

end Berarducci
