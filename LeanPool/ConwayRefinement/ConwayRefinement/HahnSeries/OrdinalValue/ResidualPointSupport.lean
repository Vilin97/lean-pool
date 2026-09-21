/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointTail

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import Mathlib.Tactic.Linarith

/-!
# Support families along Berarducci residual points

This module proves the support-family construction in Berarducci, Lemma 6.9. A final segment of a
residual-point tail still has the full principal order type. This permits a strictly increasing
reindexing by `v_J^p(b)`. Congruence modulo `J + K` then transports the translated-truncation
value bound from the given series to every representative used in the definition of `v_J`.

For the support blocks there is an essential boundary distinction. When `ρ = 1`, a block retains
the cutoff exponent and uses closed lower support. When `1 < ρ`, a block uses strict lower support;
excluding the cutoff prevents a constant endpoint from forming a final segment of order type one.
The final-segment estimate in
`ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment` supplies the required lower
bound in the latter case.

This expands the source's terse application of Lemma 4.7 and makes the residual-value-one
endpoint case explicit.
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open Ordinal

variable {K : Type v} [Field K]

/-- A residual-point tail contains a strictly increasing copy of its full principal order type on
which the translated-truncation lower bound holds for any fixed representative modulo `J + K`. -/
theorem exists_strictMono_cutoff_of_residualPointTail
    (b : SeriesWithOrdinalValueAboveOne K) (c : Series K) {ρ : Ordinal} {η : ℝ}
    (htail : (residualPointTail b η).IsPWO)
    (htailType : htail.orderType = b.principalValue.val)
    (htailLUB : IsLUB (residualPointTail b η) 0)
    (hc : ∀ γ ∈ residualPointTail b η,
      NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation (c : K⟦ℝ⟧) γ))
    (d : Series K) (hcd : c - d ∈ nearConstantSubgroup K) :
    ∃ γ : b.principalValue.val.ToType → ℝ,
      StrictMono γ ∧
        (∀ i, γ i ∈ residualPointTail b η) ∧
        ∀ i, NatOrdinal.of ρ ≤
          ordinalValue (translatedTruncation (d : K⟦ℝ⟧) (γ i)) := by
  obtain ⟨θ, hθ, hvalueEq⟩ :=
    exists_ordinalValue_translatedTruncation_eq_of_sub_mem_nearConstantSubgroup hcd
  let finalTail : Set ℝ := residualPointTail b η ∩ Set.Ioi θ
  let hfinalTail : finalTail.IsPWO := htail.mono Set.inter_subset_left
  obtain ⟨x, hxTail, hθx, _⟩ := htailLUB.exists_between hθ
  have hfinalTailType : hfinalTail.orderType = b.principalValue.val := by
    calc
      hfinalTail.orderType = htail.orderType := by
        apply htail.orderType_inter_Ioi_eq_of_isPrincipal
        · rw [htailType]
          exact
            (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
              b.principalValue_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal).2
        · exact ⟨x, hxTail, hθx⟩
      _ = b.principalValue.val := htailType
  letI : WellFoundedLT finalTail := ⟨hfinalTail.isWF⟩
  have htypes : typeLT b.principalValue.val.ToType = typeLT finalTail := by
    calc
      typeLT b.principalValue.val.ToType = b.principalValue.val :=
        type_toType b.principalValue.val
      _ = hfinalTail.orderType := hfinalTailType.symm
      _ = typeLT finalTail :=
        hfinalTail.orderType_eq_typeLT_of_orderIso (OrderIso.refl finalTail)
  let e : b.principalValue.val.ToType ≃o finalTail :=
    OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htypes))
  let γ : b.principalValue.val.ToType → ℝ := fun i ↦ (e i).1
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.strictMono hij
  · intro i
    exact (e i).2.1
  · intro i
    have hθγ : θ < γ i := (e i).2.2
    have hγTail : γ i ∈ residualPointTail b η := (e i).2.1
    have hγ0 : γ i < 0 :=
      residualPointSet_subset_Iio b
        (residualPointTail_subset_residualPointSet b η hγTail)
    rw [← hvalueEq (γ i) hθγ hγ0]
    exact hc (γ i) hγTail

/-- A residual-point tail yields a well-ordered family of subsets of the support of `d`, strictly
separated between indices and with every nonempty upper subset of each member having order type
at least `ρ`. -/
theorem exists_supportFamily_of_residualPointTail
    (b : SeriesWithOrdinalValueAboveOne K) (c : Series K) {ρ : Ordinal} {η : ℝ}
    (hρ0 : ρ ≠ 0)
    (htail : (residualPointTail b η).IsPWO)
    (htailType : htail.orderType = b.principalValue.val)
    (htailLUB : IsLUB (residualPointTail b η) 0)
    (hc : ∀ γ ∈ residualPointTail b η,
      NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation (c : K⟦ℝ⟧) γ))
    (d : Series K) (hcd : c - d ∈ nearConstantSubgroup K) :
    ∃ B : b.principalValue.val.ToType → Set ℝ,
      ∃ hB : ∀ i, (B i).IsPWO,
        (∀ {i j}, i < j → ∃ y ∈ B j, ∀ x ∈ B i, x < y) ∧
        (∀ (i : b.principalValue.val.ToType) (C : Set ℝ)
          (hC : IsRelUpperSet C (· ∈ B i)), C.Nonempty →
            ρ ≤ ((hB i).mono fun _ hx ↦ (hC hx).1).orderType) ∧
        ∃ _ : (⋃ i, B i).IsPWO,
          (⋃ i, B i) ⊆ (d : K⟦ℝ⟧).support := by
  obtain ⟨γ, hγmono, _, hγvalue⟩ :=
    exists_strictMono_cutoff_of_residualPointTail b c htail htailType htailLUB hc d hcd
  by_cases hρ1 : ρ = 1
  · subst ρ
    let B : b.principalValue.val.ToType → Set ℝ :=
      fun i ↦ (d : K⟦ℝ⟧).support ∩ Set.Iic (γ i)
    let hB : ∀ i, (B i).IsPWO :=
      fun _ ↦ (d : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
    refine ⟨B, hB, ?_, ?_, ?_⟩
    · intro i j hij
      have hvalueNe : ordinalValue (translatedTruncation (d : K⟦ℝ⟧) (γ j)) ≠ 0 := by
        intro hzero
        have hle := hγvalue j
        rw [hzero] at hle
        exact (not_le_of_gt zero_lt_one) hle
      have hLUB := isLUB_support_zero_of_ordinalValue_ne_zero hvalueNe
      have hcutoff : γ i - γ j < 0 := sub_neg.mpr (hγmono hij)
      obtain ⟨δ, hδSupport, hδAbove, _⟩ := hLUB.exists_between hcutoff
      rw [support_translatedTruncation] at hδSupport
      obtain ⟨y, hy, hδ⟩ := hδSupport
      refine ⟨y, ⟨hy.1, hy.2⟩, fun x hx ↦ ?_⟩
      rw [← hδ] at hδAbove
      exact hx.2.trans_lt (by linarith)
    · intro i C hC hCne
      apply Order.one_le_iff_ne_zero.mpr
      intro hzero
      have hCempty := ((hB i).mono fun _ hx ↦ (hC hx).1).orderType_eq_zero.mp hzero
      obtain ⟨x, hx⟩ := hCne
      simp [hCempty] at hx
    · let hUnion : (⋃ i, B i).IsPWO :=
        (d : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          exact hi.1
      exact ⟨hUnion, fun _ hx ↦ by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact hi.1⟩
  · have h1ρ : 1 < ρ :=
      lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr hρ0) (Ne.symm hρ1)
    let B : b.principalValue.val.ToType → Set ℝ :=
      fun i ↦ (d : K⟦ℝ⟧).support ∩ Set.Iio (γ i)
    let hB : ∀ i, (B i).IsPWO :=
      fun _ ↦ (d : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
    have hvalueOneLt (i : b.principalValue.val.ToType) :
        1 < ordinalValue (translatedTruncation (d : K⟦ℝ⟧) (γ i)) := by
      apply (show (1 : NatOrdinal) < NatOrdinal.of ρ by
        exact NatOrdinal.of.lt_iff_lt.mpr h1ρ).trans_le
      exact hγvalue i
    refine ⟨B, hB, ?_, ?_, ?_⟩
    · intro i j hij
      have hLUB := isLUB_negativeSupport_zero_of_one_lt_ordinalValue (hvalueOneLt j)
      have hcutoff : γ i - γ j < 0 := sub_neg.mpr (hγmono hij)
      obtain ⟨δ, hδSupport, hδAbove, _⟩ := hLUB.exists_between hcutoff
      rw [support_translatedTruncation] at hδSupport
      obtain ⟨⟨y, hy, hδ⟩, hδ0⟩ := hδSupport
      refine ⟨y, ⟨hy.1, ?_⟩, fun x hx ↦ ?_⟩
      · rw [← hδ] at hδ0
        change -γ j + y < 0 at hδ0
        change y < γ j
        linarith
      · rw [← hδ] at hδAbove
        exact hx.2.trans (by linarith)
    · intro i C hC hCne
      exact le_orderType_of_le_ordinalValue_translatedTruncation_of_isRelUpperSet_supportBelow
        (d : K⟦ℝ⟧) (γ i) (hγvalue i) hC hCne
    · let hUnion : (⋃ i, B i).IsPWO :=
        (d : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          exact hi.1
      exact ⟨hUnion, fun _ hx ↦ by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact hi.1⟩

end Berarducci
