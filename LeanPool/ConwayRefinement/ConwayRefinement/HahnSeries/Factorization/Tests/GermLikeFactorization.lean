/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.GermLike
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.DegreeTwoExample

/-!
# Checks for germ-like factorisation

The PS06 degree-two series with constant coefficient one exercises the second branch of the
LM17 germ-like definition: its support order type is `ω² + 1` and its ordinal value is `ω²`.
Thus this certificate distinguishes the intended definition from the nearby wrong definition
that retains only the equality `ot(a) = v_J(a)`.
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Tests.LM17

open Berarducci PommersheimShahriari PommersheimShahriari.DegreeTwoExample

variable {K : Type v} [Field K]

/-- The degree-two series with constant coefficient one is germ-like by the nontrivial
`ot(a) = v_J(a) + 1` branch. -/
theorem degreeTwoWithConstant_isGermLike :
    LM17.IsGermLike (degreeTwoWithConstant (K := K)) := by
  rw [LM17.isGermLike_iff]
  right
  have hvalue : ordinalValue (degreeTwoWithConstant (K := K)) = ω^ (2 : NatOrdinal) :=
    ordinalValue_eq_wpow_two
      (degreeTwoWithConstant_not_mem_nearConstantSubgroup (K := K))
      (Or.inr (degreeTwoWithConstant_supportOrderType (K := K)))
  refine ⟨?_, ?_⟩
  · rw [hvalue, ← NatOrdinal.val.lt_iff_lt]
    simp only [NatOrdinal.val_one, NatOrdinal.val_wpow]
    rw [Ordinal.one_lt_opow]
    exact ⟨Ordinal.one_lt_omega0, by norm_num⟩
  · rw [hvalue, NatOrdinal.val_wpow]
    have h2 : (2 : NatOrdinal).val = (2 : Ordinal) := rfl
    rw [h2]
    exact degreeTwoWithConstant_supportOrderType (K := K)

/-- The degree-two germ-like series with constant coefficient one admits an irreducible
factorisation. -/
theorem degreeTwoWithConstant_exists_factorization [CharZero K] :
    ∃ f : Multiset (Series K),
      (∀ b ∈ f, Irreducible b) ∧
        Associated f.prod (degreeTwoWithConstant (K := K)) :=
  degreeTwoWithConstant_isGermLike.exists_factorization
    (degreeTwoWithConstant_irreducible (K := K)).ne_zero

end Tests.LM17
