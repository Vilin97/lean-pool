/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative

/-!
# The exponent-valued order valuation

The leading Cantor exponent of Berarducci's ordinal value `v_J` is a max-additive degree on
`K((ℝ^{≤0}))` over every coefficient field, with kernel `J`: the max-form inequality for sums is
Berarducci, Lemma 5.5(1), and the bound `v_J(bc) ≤ v_J(b) ⊙ v_J(c)` of Berarducci, Lemma 5.5(2)
gives the product inequality for the exponent. This module fixes that degree once, as
`ordinalValueDegreeValuation K`. The spaces
`P_α = J_{ω^(α+1)} / J_{ω^α}` are its homogeneous components and `P̂` is its
associated graded ring, so both exist, with their graded multiplication, over every field.

Exact multiplicativity `v_J(bc) = v_J(b) ⊙ v_J(c)` is Berarducci, Theorem 9.7, proved for a field
of characteristic zero; it is recorded separately as the instance
`(ordinalValueDegreeValuation K).IsMultiplicative` in
`ConwayRefinement.HahnSeries.OrdinalValue.Statements.OrdinalValueDegree`, and it is what makes
the ring `P̂` a domain.
-/

universe v

public noncomputable section

namespace Berarducci

variable (K : Type v) [Field K]

/-- The exponent-valued order valuation of `K((ℝ^{≤0}))`, as a degree function: its value on `b`
is the leading Cantor exponent of Berarducci's ordinal value `v_J(b)`, with bottom value on `J`.
It is a max-additive degree by Berarducci, Lemma 5.5. -/
def ordinalValueDegreeValuation : MaxAddDegree (Series K) NatOrdinal where
  toFun := ordinalValueDegree
  map_zero' := ordinalValueDegree_zero
  map_one_le_zero' := ordinalValueDegree_one.le
  map_neg' := ordinalValueDegree_neg
  map_add_le_max' := ordinalValueDegree_add_le_max
  map_mul_le_add' := ordinalValueDegree_mul_le_add

variable {K}

@[simp]
theorem ordinalValueDegreeValuation_apply (b : Series K) :
    ordinalValueDegreeValuation K b = ordinalValueDegree b :=
  (rfl)

/-- The kernel of the exponent-valued order valuation is exactly Berarducci's `J`. -/
theorem ordinalValueDegreeValuation_eq_bot_iff (b : Series K) :
    ordinalValueDegreeValuation K b = ⊥ ↔ b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  rw [ordinalValueDegreeValuation_apply, ordinalValueDegree_eq_bot_iff]

theorem mem_ordinalValueDegreeValuation_filtrationLE_iff (b : Series K) (α : NatOrdinal) :
    b ∈ (ordinalValueDegreeValuation K).filtrationLE α ↔ ordinalValue b < ω^ (α + 1) := by
  rw [MaxAddDegree.mem_filtrationLE_iff, ordinalValueDegreeValuation_apply,
    ordinalValueDegree_le_coe_iff]

theorem mem_ordinalValueDegreeValuation_filtrationLT_iff (b : Series K) (α : NatOrdinal) :
    b ∈ (ordinalValueDegreeValuation K).filtrationLT α ↔ ordinalValue b < ω^ α := by
  rw [MaxAddDegree.mem_filtrationLT_iff, ordinalValueDegreeValuation_apply,
    ordinalValueDegree_lt_coe_iff]

end Berarducci
