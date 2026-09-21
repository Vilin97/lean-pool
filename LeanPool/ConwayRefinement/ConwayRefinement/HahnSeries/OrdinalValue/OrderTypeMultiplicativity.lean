/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Multiplicativity
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Sumset
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# Multiplicativity of the support order type

Berarducci, Corollary 9.9, imported by LM24 as Fact 3.4.1: the support order type is
multiplicative for the Hessenberg product on series whose order types are additively principal.

The ordinal value is bounded above by the support order type, and on a series outside `J` whose
order type is additively principal the two agree: a representative modulo `J + K` shares a final
segment of the support, and a nonempty final segment of an additively principal order type has
the full order type. The order type of a product is bounded above by the Hessenberg product of
the order types, because the support of a product lies in the sumset of the supports. Theorem 9.7
supplies the matching lower bound, and the two squeeze.
-/

universe v

public noncomputable section

open HahnSeries Ordinal

namespace Berarducci

variable {K : Type v} [Field K]

/-- Berarducci, Remark 5.4: the support order type of a product is at most the Hessenberg product
of the support order types. -/
theorem supportOrderType_mul_le_naturalMul (b c : K⟦ℝ⟧) :
    (b * c).supportOrderType
      ≤ (NatOrdinal.of b.supportOrderType * NatOrdinal.of c.supportOrderType).val := by
  rw [supportOrderType_eq_setOrderType, supportOrderType_eq_setOrderType,
    supportOrderType_eq_setOrderType]
  exact ((b * c).isPWO_support.orderType_mono (b.isPWO_support.add c.isPWO_support)
    HahnSeries.support_mul_subset).trans
    (Set.IsPWO.orderType_add_le_naturalMul b.isPWO_support c.isPWO_support)

/-- A series outside `J` has support points arbitrarily close to zero. -/
private theorem exists_mem_support_gt {b : Series K}
    (hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K) {η : ℝ} (hη : η < 0) :
    ∃ y ∈ (b : K⟦ℝ⟧).support, η < y := by
  have hlub := isLUB_support_zero_of_ordinalValue_ne_zero
    (b := b) (fun h ↦ hbJ (ordinalValue_eq_zero_iff.mp h))
  by_contra hcon
  exact absurd (hlub.2 fun y hy ↦ le_of_not_gt fun hgt ↦ hcon ⟨y, hy, hgt⟩) (not_le.mpr hη)

/-- Above order type one an additively principal order type is a limit, so the support has no
maximum and in particular misses the origin. -/
private theorem notMem_support_zero_of_ne_one {b : Series K}
    (hb : IsWeaklyPrincipal (b : K⟦ℝ⟧)) (h1 : (b : K⟦ℝ⟧).supportOrderType ≠ 1) :
    (0 : ℝ) ∉ (b : K⟦ℝ⟧).support := by
  obtain ⟨e, he⟩ := isAdditivelyPrincipal_iff.mp (isWeaklyPrincipal_iff.mp hb)
  have hene : e ≠ 0 := by
    rintro rfl
    exact h1 (by simpa using he)
  have hlim : Order.IsSuccLimit (b : K⟦ℝ⟧).supportOrderType := by
    rw [he]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hene
  intro h0
  obtain ⟨y, hy, hy0⟩ := (b : K⟦ℝ⟧).isPWO_support.exists_gt_of_isSuccLimit_orderType
    (by rwa [← supportOrderType_eq_setOrderType]) h0
  exact absurd ((HahnSeries.mem_nonpositiveSubring (Γ := ℝ) (R := K)).mp b.2 hy) (not_le.mpr hy0)

/-- A representative modulo `J + K` of a series outside `J` whose order type is additively
principal has at least that order type. Above one the order type is a limit, so the support has no
maximum and in particular misses the origin, where a constant summand could have changed it; the
two supports then share a final segment, which carries the whole order type. -/
private theorem supportOrderType_le_of_sub_mem_nearConstantSubgroup {b c : Series K}
    (hb : IsWeaklyPrincipal (b : K⟦ℝ⟧))
    (hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K)
    (hbc : b - c ∈ nearConstantSubgroup K) (hc : c ≠ 0) :
    (b : K⟦ℝ⟧).supportOrderType ≤ (c : K⟦ℝ⟧).supportOrderType := by
  have hbsupp : (b : K⟦ℝ⟧).support ⊆ Set.Iic (0 : ℝ) :=
    (HahnSeries.mem_nonpositiveSubring (Γ := ℝ) (R := K)).mp b.2
  rcases eq_or_ne (b : K⟦ℝ⟧).supportOrderType 1 with h1 | h1
  · rw [h1]
    refine Order.one_le_iff_ne_zero.mpr fun h0 ↦ hc ?_
    rw [supportOrderType_eq_setOrderType, Set.IsPWO.orderType_eq_zero] at h0
    exact Subtype.ext (HahnSeries.support_eq_empty_iff.mp h0)
  · have hzero := notMem_support_zero_of_ne_one hb h1
    obtain ⟨η, hη, hcoeff⟩ := exists_coeff_eq_of_sub_mem_nearConstantSubgroup hbc
    have hprin :
        Ordinal.IsPrincipal (fun a b ↦ a + b) (b : K⟦ℝ⟧).isPWO_support.orderType := by
      rw [← supportOrderType_eq_setOrderType]
      exact (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
        (isWeaklyPrincipal_iff.mp hb)).2
    have hseg := (b : K⟦ℝ⟧).isPWO_support.orderType_inter_Ioi_eq_of_isPrincipal hprin
      (exists_mem_support_gt hbJ hη)
    have hsub : (b : K⟦ℝ⟧).support ∩ Set.Ioi η ⊆ (c : K⟦ℝ⟧).support := by
      intro y hy
      have hy0 : y < 0 := lt_of_le_of_ne (hbsupp hy.1) fun h ↦ hzero (h ▸ hy.1)
      rw [HahnSeries.mem_support, ← hcoeff y hy.2 hy0]
      exact (HahnSeries.mem_support _ _).mp hy.1
    rw [supportOrderType_eq_setOrderType, ← hseg, supportOrderType_eq_setOrderType]
    exact Set.IsPWO.orderType_mono _ _ hsub

/-- On a series outside `J` whose order type is additively principal, the support order type and
the ordinal value agree. -/
theorem supportOrderType_eq_ordinalValue_of_isWeaklyPrincipal {b : Series K}
    (hb : IsWeaklyPrincipal (b : K⟦ℝ⟧))
    (hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    (b : K⟦ℝ⟧).supportOrderType = (ordinalValue b).val := by
  refine le_antisymm ?_ (NatOrdinal.val.monotone (ordinalValue_le_supportOrderType b))
  by_cases hbNear : b ∈ nearConstantSubgroup K
  · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal hbNear hbJ]
    rcases eq_or_ne (b : K⟦ℝ⟧).supportOrderType 1 with h1 | h1
    · rw [h1]
      simp
    · refine absurd ?_ hbJ
      have hcc : HahnSeries.Nonpositive.constantCoeff b = 0 := by
        by_contra hne
        exact notMem_support_zero_of_ne_one hb h1 ((HahnSeries.mem_support _ _).mpr
          (by rwa [HahnSeries.Nonpositive.constantCoeff_apply] at hne))
      have hsub := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hbNear
      rwa [hcc, map_zero, _root_.sub_zero] at hsub
  · obtain ⟨hmem, -⟩ := ordinalValue_isLeast_representativeOrderTypes hbNear
    obtain ⟨d, hd, hdeq⟩ := mem_representativeOrderTypes_iff.mp hmem
    have hdne : d ≠ 0 := by
      rintro rfl
      rw [_root_.sub_zero] at hd
      exact hbNear hd
    rw [← hdeq, NatOrdinal.val_of]
    exact supportOrderType_le_of_sub_mem_nearConstantSubgroup hb hbJ hd hdne

/-- Berarducci, Corollary 9.9 for series outside `J`: the ordinal value and the support order
type coincide there, and Theorem 9.7 supplies the lower bound that meets Remark 5.4. -/
private theorem supportOrderType_mul_of_notMem_negativeMonomialIdeal [CharZero K] {b c : Series K}
    (hb : IsWeaklyPrincipal (b : K⟦ℝ⟧)) (hc : IsWeaklyPrincipal (c : K⟦ℝ⟧))
    (hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K)
    (hcJ : c ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    ((b * c : Series K) : K⟦ℝ⟧).supportOrderType
      = (NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType *
          NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType).val := by
  refine le_antisymm ?_ ?_
  · rw [show ((b * c : Series K) : K⟦ℝ⟧) = (b : K⟦ℝ⟧) * (c : K⟦ℝ⟧) from rfl]
    exact supportOrderType_mul_le_naturalMul _ _
  · rw [supportOrderType_eq_ordinalValue_of_isWeaklyPrincipal hb hbJ,
      supportOrderType_eq_ordinalValue_of_isWeaklyPrincipal hc hcJ, NatOrdinal.of_val,
      NatOrdinal.of_val, ← ordinalValue_mul b c]
    exact NatOrdinal.val.monotone (ordinalValue_le_supportOrderType (b * c))

end Berarducci

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-- Berarducci, Corollary 9.9, imported by LM24 as Fact 3.4.1. Normalizing each factor moves it
out of `J` without changing any order type, since translation is an order isomorphism of the
exponents and the product of two translates is a translate of the product. -/
@[blueprint "fact:weakly-principal-order-type-multiplicativity"
  (phase := "Ordinal value and degree")
  (title := "Multiplicativity of order type for weakly principal series \
    (Ber00, Corollary 9.9; LM24, Fact 3.4.1)")
  (statement := /--
    Let $K$ be a field of characteristic zero. If
    $b,c\in K((\mathbb R^{\le 0}))$ are weakly principal, then
    \[
      \operatorname{ot}(bc)=
      \operatorname{ot}(b)\odot\operatorname{ot}(c).
    \]
  -/)
  (proof := /--
  Translate each factor so that the supremum of its support is zero.  Translation
  preserves the three support order types and places both factors outside $J$.
  For a weakly principal series outside $J$, its support order type equals its
  ordinal value.  \ref{fact:ordinal-value-multiplicativity} gives the lower bound for
  the product, while containment of its support in the sum of the two supports
  gives the reverse bound.
  -/)]
theorem orderTypeMultiplicativeOnWeaklyPrincipal [CharZero K] :
    OrderTypeMultiplicativeOnWeaklyPrincipal K := by
  refine orderTypeMultiplicativeOnWeaklyPrincipal_iff.mpr fun b c hb hc ↦ ?_
  have hne : ∀ x : Berarducci.Series K, IsWeaklyPrincipal (x : K⟦ℝ⟧) → x ≠ 0 := by
    rintro x hx rfl
    exact (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
      (isWeaklyPrincipal_iff.mp hx)).1 (by
        rw [HahnSeries.supportOrderType_eq_setOrderType, Set.IsPWO.orderType_eq_zero]
        simp)
  set sb := sSup (b : K⟦ℝ⟧).support with hsb
  set sc := sSup (c : K⟦ℝ⟧).support with hsc
  have hbot : (normalize b : K⟦ℝ⟧).supportOrderType = (b : K⟦ℝ⟧).supportOrderType :=
    supportOrderType_normalize b
  have hcot : (normalize c : K⟦ℝ⟧).supportOrderType = (c : K⟦ℝ⟧).supportOrderType :=
    supportOrderType_normalize c
  have hmul : (b : K⟦ℝ⟧) * (c : K⟦ℝ⟧)
      = HahnSeries.translate (sb + sc)
        ((normalize b : K⟦ℝ⟧) * (normalize c : K⟦ℝ⟧)) := by
    have h := HahnSeries.translate_mul_translate sb sc
      (normalize b : K⟦ℝ⟧) (normalize c : K⟦ℝ⟧)
    rwa [translate_csSup_normalize b, translate_csSup_normalize c] at h
  rw [show ((b * c : Berarducci.Series K) : K⟦ℝ⟧) =
      (b : K⟦ℝ⟧) * (c : K⟦ℝ⟧) from rfl,
    hmul, HahnSeries.supportOrderType_translate, ← hbot, ← hcot]
  exact Berarducci.supportOrderType_mul_of_notMem_negativeMonomialIdeal
    (by rwa [isWeaklyPrincipal_iff, hbot, ← isWeaklyPrincipal_iff])
    (by rwa [isWeaklyPrincipal_iff, hcot, ← isWeaklyPrincipal_iff])
    (not_mem_negativeMonomialIdeal_of_supportSup_eq_zero (supportSup_normalize (hne b hb)))
    (not_mem_negativeMonomialIdeal_of_supportSup_eq_zero (supportSup_normalize (hne c hc)))

end HahnSeries.Nonpositive
