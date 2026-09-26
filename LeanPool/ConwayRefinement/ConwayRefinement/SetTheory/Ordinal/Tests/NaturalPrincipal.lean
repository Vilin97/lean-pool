/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal

/-!
# API checks for principality of the natural operations

These certificates separate Berarducci, Fact 3.7 from two weaker readings: the multiplicative case
with only additive principality assumed, and either case read with the ordinary ordinal operations
in place of the natural ones.
-/

universe u

open scoped NatOrdinal

public noncomputable section

namespace Tests

/-- `ω ^ ω` is multiplicative principal, so it is closed under natural products. -/
theorem naturalMul_lt_omega0_opow_omega0 {b c : Ordinal}
    (hb : b < Ordinal.omega0 ^ Ordinal.omega0)
    (hc : c < Ordinal.omega0 ^ Ordinal.omega0) :
    (NatOrdinal.of b * NatOrdinal.of c).val < Ordinal.omega0 ^ Ordinal.omega0 := by
  have hmp := Ordinal.isMultiplicativelyPrincipal_omega0_opow_opow 1
  rw [Ordinal.opow_one] at hmp
  exact hmp.naturalMul_lt hb hc

/-- Additive principality alone does not give closure under natural products, since
`ω ⊙ ω = ω ^ 2`. -/
theorem naturalMul_lt_needs_multiplicativelyPrincipal :
    ∃ o a : Ordinal,
      Ordinal.IsAdditivelyPrincipal o ∧ a < o ∧
        ¬(NatOrdinal.of a * NatOrdinal.of a).val < o := by
  refine ⟨Ordinal.omega0 ^ (2 : Ordinal), Ordinal.omega0,
    Ordinal.isAdditivelyPrincipal_omega0_opow 2, ?_, ?_⟩
  · calc Ordinal.omega0 = Ordinal.omega0 ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
      _ < Ordinal.omega0 ^ (2 : Ordinal) :=
        (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr one_lt_two
  · have hval : (NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0).val =
        Ordinal.omega0 ^ (2 : Ordinal) := by
      have hof : NatOrdinal.of Ordinal.omega0 = ω^ (1 : NatOrdinal) := by
        rw [← Ordinal.opow_one Ordinal.omega0, NatOrdinal.of_omega0_opow]
        simp
      rw [hof, ← NatOrdinal.wpow_add, NatOrdinal.val_wpow]
      congr 1
      rw [one_add_one_eq_two]
      rfl
    rw [hval]
    exact lt_irrefl _

/-- Fact 3.7 is stated for the natural sum, which differs from the ordinary ordinal sum on the
same arguments: `1 ⊕ ω = ω + 1` while `1 + ω = ω`. -/
theorem naturalAdd_ne_ordinalAdd :
    ∃ b c : Ordinal, (NatOrdinal.of b + NatOrdinal.of c).val ≠ b + c := by
  refine ⟨1, Ordinal.omega0, ?_⟩
  rw [Ordinal.one_add_omega0]
  have hlt : NatOrdinal.of Ordinal.omega0 <
      NatOrdinal.of 1 + NatOrdinal.of Ordinal.omega0 := by
    refine lt_add_of_pos_left _ ?_
    simp
  exact (NatOrdinal.val.lt_iff_lt.mpr hlt).ne'

end Tests
