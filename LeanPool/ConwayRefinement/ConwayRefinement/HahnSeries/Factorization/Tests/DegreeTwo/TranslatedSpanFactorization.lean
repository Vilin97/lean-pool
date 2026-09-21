/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.TranslatedSpanFactorization

/-!
# Public-interface check for the PS06 translated-truncation-span irreducibility criterion

This separately compiled client exercises the dimension bound and PS06, Corollary 3.3 through
their public signatures, without unfolding the quotient or translated-truncation-span definitions.
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Tests

/-- The public Proposition 3.2 API bounds the translated-truncation span of a balanced product by
two. -/
theorem ps06_balancedProduct_translatedTruncationSpan_client
    {K : Type v} [Field K] {b c : Berarducci.Series K}
    (hbValue : Berarducci.ordinalValue b = ω^ (1 : NatOrdinal))
    (hcValue : Berarducci.ordinalValue c = ω^ (1 : NatOrdinal))
    (hbCritical : Berarducci.IsCriticalPoint b 0)
    (hcCritical : Berarducci.IsCriticalPoint c 0) :
    Module.finrank K (PommersheimShahriari.translatedTruncationSpan (b * c)) ≤ 2 :=
  PommersheimShahriari.finrank_translatedTruncationSpan_mul_le_two
    hbValue hcValue hbCritical hcCritical

/-- The public Corollary 3.3 API reproduces PS06's degree-two irreducibility criterion. -/
theorem ps06_degreeTwo_irreducibility_client
    {K : Type v} [Field K] [CharZero K] {a : Berarducci.Series K}
    (haNear : a ∉ Berarducci.nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ (2 : Ordinal) ∨
      (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1)
    (haDimension : 2 <
      Module.finrank K (PommersheimShahriari.translatedTruncationSpan a)) :
    Irreducible a :=
  PommersheimShahriari.irreducible_of_two_lt_finrank_translatedTruncationSpan
    haNear haType haDimension

end Tests
