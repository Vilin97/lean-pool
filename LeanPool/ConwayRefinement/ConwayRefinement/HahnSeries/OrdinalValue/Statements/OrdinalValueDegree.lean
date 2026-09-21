/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueValuation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# The ordinal-value degree in characteristic zero

Over a field of characteristic zero, Berarducci's ordinal value is multiplicative (Berarducci,
Theorem 9.7, proved as `ordinalValueMultiplicative` and imported by LM24 as Fact 2.7.1(2)). The
exponent-valued order valuation `ordinalValueDegreeValuation K`, defined over every field from the
submultiplicative bound of Berarducci, Lemma 5.5, is then exactly multiplicative: a multiplicative
semi-valuation in the sense of LM24 with kernel `J`. This module records that multiplicativity as
an instance, which is what makes `P̂` a domain, together with the existence
statement in the form LM24 uses.
-/

universe v

public noncomputable section

namespace Berarducci

open scoped NatOrdinal

variable {K : Type v} [Field K] [CharZero K]

/-- Berarducci, Theorem 9.7: the exponent-valued order valuation is multiplicative. -/
instance ordinalValueDegreeValuation_isMultiplicative :
    (ordinalValueDegreeValuation K).IsMultiplicative :=
  ⟨fun b c ↦ by
    simp only [ordinalValueDegreeValuation_apply]
    exact ordinalValueMultiplicative.ordinalValueDegree_mul b c⟩

/-- There exists an exponent-valued multiplicative Berarducci semi-valuation whose value is the
leading Cantor exponent of `v_J` and whose kernel is exactly `J`, as in LM24, Fact 2.7.1(2). -/
theorem exists_ordinalValueDegreeValuation :
    ∃ w : MaxAddDegree (Series K) NatOrdinal, w.IsMultiplicative ∧
      (∀ b : Series K, w b = ordinalValueDegree b) ∧
        ∀ b : Series K, w b = ⊥ ↔ b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  exact ⟨ordinalValueDegreeValuation K, inferInstance, ordinalValueDegreeValuation_apply,
    ordinalValueDegreeValuation_eq_bot_iff⟩

end Berarducci
