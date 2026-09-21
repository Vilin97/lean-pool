/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.CriticalPointExistence

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# Factorisations of series of ordinal value omega squared

This module begins the proof of Pommersheim--Shahriari, Lemma 3.1. If a product has Berarducci
ordinal value `ω²`, the values of its ordered factors are either `1` and `ω²`, or `ω` and
`ω`. For a degree-two series whose negative translated truncations all have value below `ω²`,
Berarducci's critical-product formula then forces the two critical points to be zero.

The remaining support-theoretic step—turning critical point zero into the precise factor order
types printed in PS06—is kept separate rather than hidden in the ordinal calculation.

## References

* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace PommersheimShahriari

open Berarducci HahnSeries Ordinal

variable {K : Type v} [Field K] [CharZero K]

omit [CharZero K] in
private theorem ordinalValue_ne_zero_of_mul_eq_wpow_two_left
    {b c : Series K} (h : ordinalValue b * ordinalValue c = ω^ (2 : NatOrdinal)) :
    ordinalValue b ≠ 0 := by
  intro hb
  rw [hb, zero_mul] at h
  exact (NatOrdinal.wpow_ne_zero 2) h.symm

omit [CharZero K] in
/-- PS06, Lemma 3.1, ordinal factorisation step: an ordered factorisation of value `ω²`
has factor values `1` and `ω²`, or two factor values `ω`. -/
theorem ordinalValue_factors_of_mul_eq_wpow_two
    {b c : Series K}
    (hmul : ordinalValue b * ordinalValue c = ω^ (2 : NatOrdinal))
    (hle : ordinalValue b ≤ ordinalValue c) :
    (ordinalValue b = 1 ∧ ordinalValue c = ω^ (2 : NatOrdinal)) ∨
      (ordinalValue b = ω^ (1 : NatOrdinal) ∧
        ordinalValue c = ω^ (1 : NatOrdinal)) := by
  have hbNe := ordinalValue_ne_zero_of_mul_eq_wpow_two_left hmul
  have hcNe : ordinalValue c ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hmul
    exact (NatOrdinal.wpow_ne_zero 2) hmul.symm
  have hbDegreeNe : ordinalValueDegree b ≠ ⊥ := fun hbot ↦
    hbNe (ordinalValue_eq_zero_iff.mpr (ordinalValueDegree_eq_bot_iff.mp hbot))
  have hcDegreeNe : ordinalValueDegree c ≠ ⊥ := fun hbot ↦
    hcNe (ordinalValue_eq_zero_iff.mpr (ordinalValueDegree_eq_bot_iff.mp hbot))
  let d := (ordinalValueDegree b).unbot hbDegreeNe
  let e := (ordinalValueDegree c).unbot hcDegreeNe
  have hdDegree : ordinalValueDegree b = (d : WithBot NatOrdinal) :=
    (WithBot.coe_unbot _ hbDegreeNe).symm
  have heDegree : ordinalValueDegree c = (e : WithBot NatOrdinal) :=
    (WithBot.coe_unbot _ hcDegreeNe).symm
  have hbValue : ordinalValue b = ω^ d :=
    (ordinalValueDegree_eq_coe_iff b d).mp hdDegree
  have hcValue : ordinalValue c = ω^ e :=
    (ordinalValueDegree_eq_coe_iff c e).mp heDegree
  have hde : d + e = 2 := by
    rw [hbValue, hcValue, ← NatOrdinal.wpow_add] at hmul
    exact NatOrdinal.wpow_inj.mp hmul
  have hdele : d ≤ e := by
    rw [hbValue, hcValue, NatOrdinal.wpow_le_wpow] at hle
    exact hle
  rcases eq_or_ne d 0 with hd | hd
  · left
    have he : e = 2 := by simpa [hd] using hde
    rw [hd] at hbValue
    rw [he] at hcValue
    exact ⟨by simpa only [NatOrdinal.wpow_zero] using hbValue, hcValue⟩
  · right
    have hdOne : 1 ≤ d := Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hd)
    have heOne : 1 ≤ e := hdOne.trans hdele
    have heLe : e ≤ 1 := by
      apply (add_le_add_iff_left (a := (1 : NatOrdinal))).mp
      calc
        1 + e ≤ d + e := add_le_add hdOne le_rfl
        _ = 1 + 1 := hde.trans (one_add_one_eq_two (R := NatOrdinal)).symm
    have he : e = 1 := le_antisymm heLe heOne
    have hdLe : d ≤ 1 := hdele.trans heLe
    have hdEq : d = 1 := le_antisymm hdLe hdOne
    rw [hdEq] at hbValue
    rw [he] at hcValue
    simpa using ⟨hbValue, hcValue⟩

/-- In the PS06 degree-two situation, critical points of both factors must be zero once negative
translated truncations of the product all have value below `ω²`. -/
theorem criticalPoints_eq_zero_of_product_wpow_two
    {a b c : Series K} {x y : ℝ}
    (habc : a = b * c)
    (haValue : ordinalValue a = ω^ (2 : NatOrdinal))
    (haNegative : ∀ u : ℝ, u < 0 →
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ω^ (2 : NatOrdinal))
    (hx : IsCriticalPoint b x) (hy : IsCriticalPoint c y) :
    x = 0 ∧ y = 0 := by
  have hbLe : ordinalValue b ≤
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) := by
    simpa using hx.value_le 0 le_rfl
  have hcLe : ordinalValue c ≤
      ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) := by
    simpa using hy.value_le 0 le_rfl
  have hcriticalLower : ω^ (2 : NatOrdinal) ≤
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) (x + y)) := by
    calc
      ω^ (2 : NatOrdinal) = ordinalValue a := haValue.symm
      _ = ordinalValue b * ordinalValue c := by rw [habc, ordinalValue_mul]
      _ ≤ ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) *
          ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) :=
        mul_le_mul hbLe hcLe bot_le bot_le
      _ = ordinalValue (translatedTruncation (a : K⟦ℝ⟧) (x + y)) := by
        rw [habc, criticalPoint_product_value hx hy]
  have hsumNonnegative : 0 ≤ x + y := by
    apply le_of_not_gt
    intro hnegative
    exact (not_lt_of_ge hcriticalLower) (by
      simpa [habc] using haNegative (x + y) hnegative)
  have hsum : x + y = 0 := le_antisymm (add_nonpos hx.nonpositive hy.nonpositive)
    hsumNonnegative
  have hx0 := hx.nonpositive
  have hy0 := hy.nonpositive
  constructor <;> linarith

end PommersheimShahriari
