/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial

/-!
# Irreducibility and support-cardinality bounds

Forgetting a support-cardinality bound embeds a bounded truncation integer part into its
unbounded counterpart. This embedding reflects units: an inverse in the unbounded ring is a
nonzero constant series, hence still has bounded support. It therefore also reflects
irreducibility.
-/

universe u v

public noncomputable section

open Cardinal

namespace HahnSeries.CardSuppLTTruncationIntegerPart

variable {G : Type u} {R : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field R]
variable [Fact (ℵ₀ < κ)]

/-- A bounded truncation-integer-part element is a unit whenever it becomes a unit after the
support-cardinality bound is forgotten. -/
theorem isUnit_of_isUnit_toTruncationIntegerPart
    (Z : Subring R)
    {x : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z}
    (hx : IsUnit (toTruncationIntegerPartRingHom Z x)) :
    IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  let y : HahnSeries.truncationIntegerPart G Z := ↑u⁻¹
  have hyUnit : IsUnit (y : HahnSeries.Nonpositive G R) := by
    exact (HahnSeries.truncationIntegerPart G Z).subtype.isUnit_map
      (show IsUnit y by exact (u⁻¹).isUnit)
  have hySupport : ((y : HahnSeries.Nonpositive G R) : R⟦G⟧).support = {0} :=
    HahnSeries.Nonpositive.support_eq_singleton_zero_of_isUnit hyUnit
  have hyCard : ((y : HahnSeries.Nonpositive G R) : R⟦G⟧).cardSupp < κ := by
    rw [HahnSeries.cardSupp, hySupport, Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans (Fact.out : ℵ₀ < κ)
  let yBounded : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z :=
    ⟨⟨(y : HahnSeries.Nonpositive G R), hyCard⟩, by
      rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
      exact ⟨HahnSeries.Nonpositive.support_subset (y : HahnSeries.Nonpositive G R),
        (HahnSeries.mem_truncationIntegerPart (R := R) (Γ := G)).mp y.2⟩⟩
  have hyForget : toTruncationIntegerPartRingHom Z yBounded = y := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_toTruncationIntegerPartRingHom, coe_toNonpositiveRingHom]
  apply isUnit_iff_exists.mpr
  refine ⟨yBounded, ?_, ?_⟩
  · apply toTruncationIntegerPartRingHom_injective Z
    rw [map_mul, map_one, hyForget]
    change toTruncationIntegerPartRingHom Z x * y = 1
    rw [← hu]
    simp [y]
  · apply toTruncationIntegerPartRingHom_injective Z
    rw [map_mul, map_one, hyForget]
    change y * toTruncationIntegerPartRingHom Z x = 1
    rw [← hu]
    simp [y]

/-- Irreducibility after forgetting a support-cardinality bound implies irreducibility before
forgetting it. -/
theorem irreducible_of_irreducible_toTruncationIntegerPart
    (Z : Subring R)
    {x : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z}
    (hx : Irreducible (toTruncationIntegerPartRingHom Z x)) :
    Irreducible x := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hunit
    exact hx.not_isUnit (hunit.map (toTruncationIntegerPartRingHom Z))
  · intro c d hfactor
    have hfactor' : toTruncationIntegerPartRingHom Z x =
        toTruncationIntegerPartRingHom Z c *
          toTruncationIntegerPartRingHom Z d := by
      rw [← map_mul, hfactor]
    rcases hx.isUnit_or_isUnit hfactor' with hc | hd
    · exact Or.inl (isUnit_of_isUnit_toTruncationIntegerPart Z hc)
    · exact Or.inr (isUnit_of_isUnit_toTruncationIntegerPart Z hd)

end HahnSeries.CardSuppLTTruncationIntegerPart
