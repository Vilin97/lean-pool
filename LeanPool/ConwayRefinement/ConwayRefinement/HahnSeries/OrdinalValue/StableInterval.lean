/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Stable support intervals for Berarducci's ordinal value

Berarducci's discussion after Definition 5.2 describes the ordinal value through sufficiently
short open intervals immediately below zero. For a nonpositive series `b`, the set
`negativeSupportTail b η` is its support in the open interval `(η, 0)`. If the ordinal value is
greater than one, some such tail has ordinary order type exactly `v_J(b)`, and every shorter
nonempty tail has the same order type. These are the stable intervals used in Lemma 6.8.

The endpoint zero is excluded because the third clause of the ordinal value works modulo `J + K`,
not merely modulo `J`. The proofs first choose a representative of minimum support order type and
then use eventual equality of negative coefficients modulo `J + K`.

-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- The support of a nonpositive series in the open interval `(η, 0)`. -/
def negativeSupportTail (b : Series K) (η : ℝ) : Set ℝ :=
  (b : K⟦ℝ⟧).support ∩ Set.Ioo η 0

/-- Membership in a negative support tail records both strict endpoints. -/
theorem mem_negativeSupportTail_iff {b : Series K} {η x : ℝ} :
    x ∈ negativeSupportTail b η ↔
      x ∈ (b : K⟦ℝ⟧).support ∧ η < x ∧ x < 0 :=
  (Iff.rfl)

/-- A negative support tail is contained in the support of the original series. -/
theorem negativeSupportTail_subset_support (b : Series K) (η : ℝ) :
    negativeSupportTail b η ⊆ (b : K⟦ℝ⟧).support :=
  fun _ hx ↦ (mem_negativeSupportTail_iff.mp hx).1

private def negativeSupportTailSeries (b : Series K) (η : ℝ) : Series K :=
  ⟨HahnSeries.filter (fun x ↦ η < x ∧ x < 0) (b : K⟦ℝ⟧), by
    rw [HahnSeries.mem_nonpositiveSubring]
    intro x hx
    rw [HahnSeries.support_filter] at hx
    exact hx.2.2.le⟩

private theorem support_negativeSupportTailSeries (b : Series K) (η : ℝ) :
    ((negativeSupportTailSeries b η : Series K) : K⟦ℝ⟧).support =
      negativeSupportTail b η := by
  change (HahnSeries.filter (fun x ↦ η < x ∧ x < 0) (b : K⟦ℝ⟧)).support = _
  rw [HahnSeries.support_filter]
  rfl

private theorem negativeSupportTailSeries_sub_mem_nearConstantSubgroup
    (b : Series K) (η : ℝ) (hη : η < 0) :
    b - negativeSupportTailSeries b η ∈ nearConstantSubgroup K := by
  rw [mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem]
  rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero]
  let q := b - negativeSupportTailSeries b η -
    HahnSeries.Nonpositive.C
      (HahnSeries.Nonpositive.constantCoeff (b - negativeSupportTailSeries b η))
  change HahnSeries.Nonpositive.supportSup q < 0
  by_cases hq : q = 0
  · simp [hq]
  · rw [HahnSeries.Nonpositive.supportSup_of_ne hq]
    apply WithBot.coe_lt_coe.mpr
    refine (csSup_le (HahnSeries.support_nonempty_iff.mpr ?_) ?_).trans_lt hη
    · simpa using hq
    · intro x hx
      apply le_of_not_gt
      intro hηx
      have hx0 : x ≤ 0 := HahnSeries.Nonpositive.support_subset q hx
      rcases hx0.eq_or_lt with rfl | hx0
      · have hcoeff : (q : K⟦ℝ⟧).coeff 0 = 0 := by
          simp [q]
        exact (HahnSeries.mem_support _ _).mp hx hcoeff
      · have htailCoeff :
            ((negativeSupportTailSeries b η : Series K) : K⟦ℝ⟧).coeff x =
              (b : K⟦ℝ⟧).coeff x := by
          simp [negativeSupportTailSeries, hηx, hx0]
        have hcoeff : (q : K⟦ℝ⟧).coeff x = 0 := by
          simp [q, htailCoeff, hx0.ne]
        exact (HahnSeries.mem_support _ _).mp hx hcoeff

/-- A series of ordinal value greater than one has an open negative support tail whose ordinary
order type is exactly its ordinal value. -/
@[blueprint "fact:ordinal-value-support-tail"
  (phase := "Ordinal value and degree")
  (title := "Support-tail characterization of the ordinal value \
    (Ber00, Definition 5.2)")
  (statement := /--
    Let $K$ be a field and let $b\in K((\mathbb R^{\le0}))$. If
    $1<v_J(b)$, then there is $\eta<0$ such that
    \[
      \operatorname{ot}(\operatorname{supp}(b)\cap(\eta,0))=v_J(b).
    \]
  -/)
  (proof := /--
  By the definition of $v_J$, choose $c\equiv b\pmod{J+K}$ whose support has
  order type $v_J(b)$. The negative coefficients of $b$ and $c$ agree on some
  interval $(\eta,0)$, so their support tails there coincide. Minimality of
  $v_J(b)$ bounds the order type of this tail from below, while its inclusion
  in $\operatorname{supp}(c)$ bounds it from above. Hence both bounds are
  equalities.
  -/)]
theorem exists_negativeSupportTail_orderType_eq_ordinalValue
    (b : Series K) (hb : 1 < ordinalValue b) :
    ∃ η < (0 : ℝ),
      ((b : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b η)).orderType =
          (ordinalValue b).val := by
  have hbNear := one_lt_ordinalValue_iff.mp hb
  have hleast := ordinalValue_isLeast_representativeOrderTypes hbNear
  obtain ⟨c, hbc, hcType⟩ := mem_representativeOrderTypes_iff.mp hleast.1
  obtain ⟨η, hη, hcoeff⟩ :=
    exists_coeff_eq_of_sub_mem_nearConstantSubgroup hbc
  refine ⟨η, hη, ?_⟩
  have hsupport : negativeSupportTail b η = negativeSupportTail c η := by
    ext x
    simp only [mem_negativeSupportTail_iff]
    constructor
    · rintro ⟨hxb, hηx, hx0⟩
      refine ⟨?_, hηx, hx0⟩
      rw [HahnSeries.mem_support, ← hcoeff x hηx hx0]
      exact (HahnSeries.mem_support _ _).mp hxb
    · rintro ⟨hxc, hηx, hx0⟩
      refine ⟨?_, hηx, hx0⟩
      rw [HahnSeries.mem_support, hcoeff x hηx hx0]
      exact (HahnSeries.mem_support _ _).mp hxc
  let hbTail : (negativeSupportTail b η).IsPWO :=
    (b : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support b η)
  let hcTail : (negativeSupportTail c η).IsPWO :=
    (c : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support c η)
  have hlower : (ordinalValue b).val ≤ hbTail.orderType := by
    rw [← NatOrdinal.of.le_iff_le]
    apply hleast.2
    apply mem_representativeOrderTypes_iff.mpr
    refine ⟨negativeSupportTailSeries b η,
      negativeSupportTailSeries_sub_mem_nearConstantSubgroup b η hη, ?_⟩
    apply congrArg NatOrdinal.of
    rw [HahnSeries.supportOrderType_eq_setOrderType]
    exact
      ((negativeSupportTailSeries b η : Series K) : K⟦ℝ⟧).isPWO_support.orderType_congr
        hbTail (support_negativeSupportTailSeries b η)
  have hupper : hbTail.orderType ≤ (ordinalValue b).val := by
    calc
      hbTail.orderType = hcTail.orderType := hbTail.orderType_congr hcTail hsupport
      _ ≤ (c : K⟦ℝ⟧).isPWO_support.orderType :=
        hcTail.orderType_mono (c : K⟦ℝ⟧).isPWO_support
          (negativeSupportTail_subset_support c η)
      _ = (c : K⟦ℝ⟧).supportOrderType :=
        (HahnSeries.supportOrderType_eq_setOrderType _).symm
      _ = (ordinalValue b).val := by
        have h := congrArg NatOrdinal.val hcType
        simpa using h
  exact le_antisymm hupper hlower

/-- Every open negative support tail of a series of value greater than one has zero as its least
upper bound. -/
theorem isLUB_negativeSupportTail_zero_of_one_lt_ordinalValue
    (b : Series K) (hb : 1 < ordinalValue b) {η : ℝ} (hη : η < 0) :
    IsLUB (negativeSupportTail b η) 0 := by
  have hnegative := isLUB_negativeSupport_zero_of_one_lt_ordinalValue hb
  obtain ⟨x, hxSupport, hηx, _⟩ := hnegative.exists_between hη
  have hxTail : x ∈ negativeSupportTail b η :=
    mem_negativeSupportTail_iff.mpr ⟨hxSupport.1, hηx, hxSupport.2⟩
  refine ⟨?_, ?_⟩
  · intro y hy
    exact (mem_negativeSupportTail_iff.mp hy).2.2.le
  · intro a ha
    apply hnegative.2
    intro y hy
    by_cases hηy : η < y
    · exact ha (mem_negativeSupportTail_iff.mpr ⟨hy.1, hηy, hy.2⟩)
    · exact (le_of_not_gt hηy).trans (hηx.le.trans (ha hxTail))

/-- Once an open negative support tail computes the ordinal value, every later tail does too. -/
theorem exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue
    (b : Series K) (hb : 1 < ordinalValue b) :
    ∃ η < (0 : ℝ), ∀ ξ : ℝ, η < ξ → ξ < 0 →
      ((b : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b ξ)).orderType =
          (ordinalValue b).val := by
  obtain ⟨η, hη, hstable⟩ :=
    exists_negativeSupportTail_orderType_eq_ordinalValue b hb
  refine ⟨η, hη, fun ξ hηξ hξ ↦ ?_⟩
  let hηTail : (negativeSupportTail b η).IsPWO :=
    (b : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support b η)
  let hξTail : (negativeSupportTail b ξ).IsPWO :=
    (b : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support b ξ)
  have htailEq : negativeSupportTail b η ∩ Set.Ioi ξ =
      negativeSupportTail b ξ := by
    ext x
    simp only [mem_negativeSupportTail_iff, Set.mem_inter_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨hxb, _, hx0⟩, hξx⟩
      exact ⟨hxb, hξx, hx0⟩
    · rintro ⟨hxb, hξx, hx0⟩
      exact ⟨⟨hxb, hηξ.trans hξx, hx0⟩, hξx⟩
  have htailLUB := isLUB_negativeSupportTail_zero_of_one_lt_ordinalValue b hb hη
  obtain ⟨x, hxTail, hξx, _⟩ := htailLUB.exists_between hξ
  have hprincipal : Ordinal.IsPrincipal (· + ·) hηTail.orderType := by
    rw [hstable]
    exact
      (Ordinal.isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
        (ordinalValue_isAdditivelyPrincipal_of_one_lt hb)).2
  have hfinal := hηTail.orderType_inter_Ioi_eq_of_isPrincipal hprincipal
    ⟨x, hxTail, hξx⟩
  calc
    hξTail.orderType =
        (hηTail.mono (s := negativeSupportTail b η ∩ Set.Ioi ξ)
          Set.inter_subset_left).orderType := by
      exact hξTail.orderType_congr _ htailEq.symm
    _ = hηTail.orderType := hfinal
    _ = (ordinalValue b).val := hstable

/-- A nonpositive series whose strictly negative support has least upper bound zero has ordinal
value greater than one. -/
theorem one_lt_ordinalValue_of_isLUB_negativeSupport
    {b : Series K}
    (hLUB : IsLUB ((b : K⟦ℝ⟧).support ∩ Set.Iio 0) 0) :
    1 < ordinalValue b := by
  rw [one_lt_ordinalValue_iff]
  intro hnear
  obtain ⟨η, hη, hcoeff⟩ :=
    exists_coeff_eq_of_sub_mem_nearConstantSubgroup (b := b) (c := 0) (by simpa)
  obtain ⟨δ, hδSupport, hηδ, _⟩ := hLUB.exists_between hη
  have hδCoeff : (b : K⟦ℝ⟧).coeff δ ≠ 0 :=
    (HahnSeries.mem_support _ _).mp hδSupport.1
  apply hδCoeff
  simpa using hcoeff δ hηδ hδSupport.2

end Berarducci
