/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEquiv

/-!
# Exponent reindexing for cardinal-bounded Hahn integer parts

An ordered additive equivalence of exponent groups preserves support cardinality, nonpositive
support, and the coefficient at zero. It therefore reindexes both the cardinal-bounded Hahn field
and its truncation integer part.
-/

universe u v

public noncomputable section

namespace HahnSeries

open Cardinal

variable {G H : Type u} {R : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
variable [Field R] [Fact (ℵ₀ < κ)]

/-- Reindex a cardinal-bounded Hahn field along an ordered additive equivalence. -/
def cardSuppLTFieldRingEquiv (e : G ≃+o H) :
    CardSuppLTField (G := G) (R := R) (κ := κ) ≃+*
      CardSuppLTField (G := H) (R := R) (κ := κ) where
  toFun x := ⟨embDomainRingEquiv e x, by
    rw [mem_cardSuppLTSubfield, cardSupp_embDomainRingEquiv]
    exact x.2⟩
  invFun x := ⟨embDomainRingEquiv e.symm x, by
    rw [mem_cardSuppLTSubfield, cardSupp_embDomainRingEquiv]
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    ext g
    have houter := embDomainRingEquiv_coeff e.symm
      (embDomainRingEquiv e (x : R⟦G⟧)) (e g)
    rw [e.symm_apply_apply, embDomainRingEquiv_coeff] at houter
    exact houter
  right_inv x := by
    apply Subtype.ext
    ext h
    have houter := embDomainRingEquiv_coeff e
      (embDomainRingEquiv e.symm (x : R⟦H⟧)) (e.symm h)
    rw [e.apply_symm_apply, embDomainRingEquiv_coeff] at houter
    exact houter
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (embDomainRingEquiv e) (x : R⟦G⟧) y
  map_add' x y := by
    apply Subtype.ext
    exact map_add (embDomainRingEquiv e) (x : R⟦G⟧) y

/-- Coercing a reindexed bounded series gives unrestricted exponent reindexing. -/
@[simp]
theorem coe_cardSuppLTFieldRingEquiv (e : G ≃+o H)
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    (cardSuppLTFieldRingEquiv e x : R⟦H⟧) = embDomainRingEquiv e x :=
  (rfl)

/-- Reindex a cardinal-bounded truncation integer part along an ordered additive equivalence. -/
def cardSuppLTTruncationIntegerPartRingEquiv (e : G ≃+o H) (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z ≃+*
      cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z where
  toFun x := ⟨cardSuppLTFieldRingEquiv e x, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    have hx := (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
    constructor
    · intro h hh
      rw [coe_cardSuppLTFieldRingEquiv, support_embDomainRingEquiv] at hh
      obtain ⟨g, hg, rfl⟩ := hh
      change e g ≤ 0
      calc
        e g ≤ e 0 := e.map_le_map_iff'.mpr (hx.1 hg)
        _ = 0 := map_zero e
    · change (embDomainRingEquiv e (x : R⟦G⟧)).coeff 0 ∈ Z
      rw [← map_zero e, embDomainRingEquiv_coeff]
      exact hx.2⟩
  invFun x := ⟨cardSuppLTFieldRingEquiv e.symm x, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    have hx := (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
    constructor
    · intro g hg
      rw [coe_cardSuppLTFieldRingEquiv, support_embDomainRingEquiv] at hg
      obtain ⟨h, hh, rfl⟩ := hg
      change e.symm h ≤ 0
      calc
        e.symm h ≤ e.symm 0 := e.symm.map_le_map_iff'.mpr (hx.1 hh)
        _ = 0 := map_zero e.symm
    · change (embDomainRingEquiv e.symm (x : R⟦H⟧)).coeff 0 ∈ Z
      rw [← map_zero e.symm, embDomainRingEquiv_coeff]
      exact hx.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    ext g
    have houter := embDomainRingEquiv_coeff e.symm
      (embDomainRingEquiv e (x : R⟦G⟧)) (e g)
    rw [e.symm_apply_apply, embDomainRingEquiv_coeff] at houter
    exact houter
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    ext h
    have houter := embDomainRingEquiv_coeff e
      (embDomainRingEquiv e.symm (x : R⟦H⟧)) (e.symm h)
    rw [e.apply_symm_apply, embDomainRingEquiv_coeff] at houter
    exact houter
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (cardSuppLTFieldRingEquiv e) x.1 y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (cardSuppLTFieldRingEquiv e) x.1 y.1

/-- The bounded integer-part equivalence applies through the bounded field equivalence. -/
@[simp]
theorem coe_cardSuppLTTruncationIntegerPartRingEquiv
    (e : G ≃+o H) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    ((cardSuppLTTruncationIntegerPartRingEquiv e Z x :
      CardSuppLTField (G := H) (R := R) (κ := κ)) : R⟦H⟧) =
      embDomainRingEquiv e (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :=
  (rfl)

end HahnSeries
