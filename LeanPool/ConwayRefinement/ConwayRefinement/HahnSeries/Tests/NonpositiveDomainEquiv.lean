/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveDomainEquiv

/-!
# API checks for nonpositive Hahn-series exponent equivalences

The negative monomial below is nonconstant and has genuinely negative support. The checks show
that exponent reindexing preserves its selected coefficient and that the inverse recovers the
series. A polymorphic theorem separately exercises the cross-universe support-order-type API.
-/

public noncomputable section

open scoped HahnSeries

namespace Tests

open HahnSeries.Nonpositive

/-- The identity ordered additive equivalence of the integer exponent group. -/
def integerExponentEquiv : ℤ ≃+o ℤ :=
  OrderAddMonoidIso.refl ℤ

/-- The rational monomial `7t⁻²` used to check reindexing by an exponent equivalence. -/
def negativeIntegerMonomial : HahnSeries.Nonpositive ℤ ℚ :=
  single (-2) 7 (by omega)

theorem negativeIntegerMonomial_reindex_coeff :
    ((embDomainRingEquiv integerExponentEquiv negativeIntegerMonomial :
      HahnSeries.Nonpositive ℤ ℚ) : HahnSeries ℤ ℚ).coeff
        (integerExponentEquiv (-2)) = 7 := by
  rw [coe_embDomainRingEquiv, HahnSeries.embDomainRingEquiv_coeff]
  simp [negativeIntegerMonomial]

theorem negativeIntegerMonomial_reindex_roundtrip :
    (embDomainRingEquiv integerExponentEquiv).symm
        (embDomainRingEquiv integerExponentEquiv negativeIntegerMonomial) =
      negativeIntegerMonomial :=
  (embDomainRingEquiv integerExponentEquiv).symm_apply_apply negativeIntegerMonomial

universe u v w

theorem reindex_lift_supportOrderType
    {G : Type u} {H : Type v} {K : Type w}
    [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
    [LinearOrder H] [AddCommGroup H] [IsOrderedAddMonoid H] [CommRing K]
    (e : G ≃+o H) (x : HahnSeries.Nonpositive G K) :
    Ordinal.lift.{u, v}
        (HahnSeries.supportOrderType (embDomainRingEquiv e x : K⟦H⟧)) =
      Ordinal.lift.{v, u} (HahnSeries.supportOrderType (x : K⟦G⟧)) :=
  lift_supportOrderType_embDomainRingEquiv e x

end Tests
