/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveCoefficientMap

/-!
# Support-determined monotonicity of the ordinal value

The ordinal value of a nonpositive series depends only on its support, so it is monotone under
inclusion of supports. The two series need not have the same coefficient field: the three regimes
that define the ordinal value — a support bounded strictly below zero, a support meeting zero only
in the constant term, and the general case measured by the order types of the negative support
tails — are each phrased in terms of the support alone.
-/

universe v w

open scoped HahnSeries NatOrdinal

namespace Berarducci

open HahnSeries.Nonpositive

public noncomputable section

/-- Order-value monotonicity under support deletion, across coefficient fields. -/
theorem ordinalValue_le_of_support_subset
    {K₁ : Type v} {K₂ : Type w} [Field K₁] [Field K₂]
    (u : HahnSeries.Nonpositive ℝ K₁) (v : HahnSeries.Nonpositive ℝ K₂)
    (h : (u : K₁⟦ℝ⟧).support ⊆ (v : K₂⟦ℝ⟧).support) :
    ordinalValue u ≤ ordinalValue v := by
  by_cases hvJ : v ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K₂
  · have huJ : u ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K₁ := by
      rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero] at hvJ ⊢
      exact lt_of_le_of_lt (supportSup_mono h) hvJ
    rw [ordinalValue_of_mem_negativeMonomialIdeal huJ,
      ordinalValue_of_mem_negativeMonomialIdeal hvJ]
  · by_cases hvN : v ∈ nearConstantSubgroup K₂
    · have huN : u ∈ nearConstantSubgroup K₁ := by
        rw [mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem,
          HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero] at hvN ⊢
        refine lt_of_le_of_lt (supportSup_mono ?_) hvN
        rw [support_sub_C_constantCoeff, support_sub_C_constantCoeff]
        exact Set.sdiff_subset_sdiff_left h
      have h1 : ordinalValue u ≤ 1 :=
        not_lt.mp fun hc ↦ (one_lt_ordinalValue_iff.mp hc) huN
      have h2 : (1 : NatOrdinal) ≤ ordinalValue v :=
        (ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
          hvN hvJ).ge
      exact h1.trans h2
    · have hv1 : 1 < ordinalValue v := one_lt_ordinalValue_iff.mpr hvN
      by_cases hu1 : ordinalValue u ≤ 1
      · exact hu1.trans hv1.le
      · replace hu1 : 1 < ordinalValue u := not_le.mp hu1
        obtain ⟨ηu, hηu, hstu⟩ :=
          exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue u hu1
        obtain ⟨ηv, hηv, hstv⟩ :=
          exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue v hv1
        set ξ : ℝ := max ηu ηv / 2 with hξdef
        have hmaxneg : max ηu ηv < 0 := max_lt hηu hηv
        have hξ0 : ξ < 0 := by rw [hξdef]; linarith
        have hξu : ηu < ξ := by
          rw [hξdef]; have := le_max_left ηu ηv; linarith
        have hξv : ηv < ξ := by
          rw [hξdef]; have := le_max_right ηu ηv; linarith
        have hsub : negativeSupportTail u ξ ⊆ negativeSupportTail v ξ := by
          intro x hx
          obtain ⟨hxs, hη, h0⟩ := mem_negativeSupportTail_iff.mp hx
          exact mem_negativeSupportTail_iff.mpr ⟨h hxs, hη, h0⟩
        have hmono := Set.IsPWO.orderType_mono
          ((u : K₁⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support u ξ))
          ((v : K₂⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support v ξ)) hsub
        rw [hstu ξ hξu hξ0, hstv ξ hξv hξ0] at hmono
        exact hmono

end

end Berarducci
