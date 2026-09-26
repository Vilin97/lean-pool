/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.CriticalPointExistence

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.FactorizationClassification
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import Mathlib.Tactic.Linarith

/-!
# Factorisation of germ-like series

L'Innocente--Mantova define a series `a` to be germ-like when its support order type is either
`v_J(a)` or, for `v_J(a) > 1`, `v_J(a) + 1`. Their Lemmas 4.4 and 4.5 identify this condition
with critical point zero and show that it passes to nonzero factors. Well-founded induction on
the ordinal value then gives their Theorem 4.8: every nonzero germ-like series factors into
irreducibles.

The critical-point proof below uses the two defining support-order alternatives directly. In the
second alternative, the strictly negative support has order type exactly `v_J(a)`; every proper
negative translated truncation therefore has smaller ordinal value.

## References

* S. L'Innocente, V. Mantova, *Factorisation of germ-like series*, J. Log. Anal. 9 (2017),
  paper no. 3, cited as [LM17].
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace LM17

open Berarducci HahnSeries Ordinal

variable {K : Type v} [Field K]

/-- LM17, Definition 4.1: a series is germ-like when its support order type is its ordinal value,
or is its ordinal value plus one when that value is greater than one. -/
def IsGermLike (a : Series K) : Prop :=
  (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val ∨
    (1 < ordinalValue a ∧
      (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val + 1)

/-- Characterisation of the germ-like predicate. -/
theorem isGermLike_iff {a : Series K} :
    IsGermLike a ↔
      (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val ∨
        (1 < ordinalValue a ∧
          (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val + 1) :=
  (Iff.rfl)

/-- A germ-like series satisfies one of its two defining support-order identities. -/
theorem IsGermLike.elim {a : Series K} (ha : IsGermLike a) :
    (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val ∨
      (1 < ordinalValue a ∧
        (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val + 1) :=
  ha

private theorem truncGE_zero_eq_single (a : Series K) :
    HahnSeries.truncGE 0 (a : K⟦ℝ⟧) =
      HahnSeries.single 0 ((a : K⟦ℝ⟧).coeff 0) := by
  ext x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [HahnSeries.coeff_truncGE, not_le_of_gt hx, hx.ne]
  · simp
  · have hcoeff : (a : K⟦ℝ⟧).coeff x = 0 := by
      apply not_ne_iff.mp
      rw [← HahnSeries.mem_support]
      exact fun hmem ↦ (not_le_of_gt hx)
        (HahnSeries.Nonpositive.support_subset a hmem)
    simp [HahnSeries.coeff_truncGE, hx.le, hcoeff, hx.ne']

private theorem supportOrderType_truncGE_zero_eq_zero_or_one (a : Series K) :
    (HahnSeries.truncGE 0 (a : K⟦ℝ⟧)).supportOrderType = 0 ∨
      (HahnSeries.truncGE 0 (a : K⟦ℝ⟧)).supportOrderType = 1 := by
  rw [truncGE_zero_eq_single]
  by_cases hcoeff : (a : K⟦ℝ⟧).coeff 0 = 0
  · left
    simp [hcoeff]
  · right
    exact HahnSeries.supportOrderType_single hcoeff

private theorem negativeSupport_orderType_eq_ordinalValue
    {a : Series K} (haOne : 1 < ordinalValue a)
    (haType : (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val + 1) :
    ((a : K⟦ℝ⟧).isPWO_support.mono
      (s := (a : K⟦ℝ⟧).support ∩ Set.Iio 0)
        Set.inter_subset_left).orderType = (ordinalValue a).val := by
  let S : Set ℝ := (a : K⟦ℝ⟧).support ∩ Set.Iio 0
  let hS : S.IsPWO := (a : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have hSLUB : IsLUB S 0 := isLUB_negativeSupport_zero_of_one_lt_ordinalValue haOne
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, -, -⟩ := hSLUB.exists_between (show (-1 : ℝ) < 0 by norm_num)
    exact ⟨x, hx⟩
  have hSgt : ∀ x ∈ S, ∃ y ∈ S, x < y := by
    intro x hx
    obtain ⟨y, hy, hxy, -⟩ := hSLUB.exists_between hx.2
    exact ⟨y, hy, hxy⟩
  have hSlimit : Order.IsSuccLimit hS.orderType :=
    Set.IsPWO.isSuccLimit_orderType_of_forall_exists_gt hS hSne hSgt
  have htruncSupport :
      (HahnSeries.truncLT 0 (a : K⟦ℝ⟧)).support = S := by
    rw [HahnSeries.support_truncLT]
    rfl
  have htruncType :
      (HahnSeries.truncLT 0 (a : K⟦ℝ⟧)).supportOrderType = hS.orderType := by
    rw [HahnSeries.supportOrderType_eq_setOrderType]
    exact (HahnSeries.truncLT 0 (a : K⟦ℝ⟧)).isPWO_support.orderType_congr
      hS htruncSupport
  have hsplit := HahnSeries.supportOrderType_eq_truncLT_add_truncGE
    0 (a : K⟦ℝ⟧)
  rcases supportOrderType_truncGE_zero_eq_zero_or_one a with hz | hz
  · rw [hz, add_zero, htruncType] at hsplit
    have hbad : hS.orderType = (ordinalValue a).val + 1 :=
      hsplit.symm.trans haType
    rw [hbad, ← Order.succ_eq_add_one] at hSlimit
    exact (Order.not_isSuccLimit_succ _ hSlimit).elim
  · rw [hz, htruncType] at hsplit
    have heq : (ordinalValue a).val + 1 = hS.orderType + 1 :=
      haType.symm.trans hsplit
    exact (Ordinal.add_right_cancel 1).mp (by simpa using heq) |>.symm

private theorem ordinalValue_translatedTruncation_lt_of_supportOrderType_eq
    {a : Series K}
    (haValue : (a : K⟦ℝ⟧).supportOrderType = (ordinalValue a).val)
    (haZero : ordinalValue a ≠ 0) {u : ℝ} (hu : u < 0) :
    ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ordinalValue a := by
  have hLUB := isLUB_support_zero_of_ordinalValue_ne_zero haZero
  obtain ⟨gamma, hgammaSupport, hugamma, -⟩ := hLUB.exists_between hu
  have htruncNe : HahnSeries.truncLE u (a : K⟦ℝ⟧) ≠ (a : K⟦ℝ⟧) := by
    intro htrunc
    have hgammaTrunc : gamma ∈ (HahnSeries.truncLE u (a : K⟦ℝ⟧)).support := by
      rw [htrunc]
      exact hgammaSupport
    rw [HahnSeries.support_truncLE] at hgammaTrunc
    exact (not_le_of_gt hugamma) hgammaTrunc.2
  calc
    ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) ≤
        NatOrdinal.of
          ((translatedTruncation (a : K⟦ℝ⟧) u : Series K) : K⟦ℝ⟧).supportOrderType :=
      ordinalValue_le_supportOrderType _
    _ = NatOrdinal.of (HahnSeries.truncLE u (a : K⟦ℝ⟧)).supportOrderType := by
      rw [coe_translatedTruncation, HahnSeries.supportOrderType_translate]
    _ < NatOrdinal.of (a : K⟦ℝ⟧).supportOrderType :=
      NatOrdinal.of.lt_iff_lt.mpr (HahnSeries.supportOrderType_truncLE_lt u htruncNe)
    _ = ordinalValue a := by rw [haValue, NatOrdinal.of_val]

private theorem ordinalValue_translatedTruncation_lt_of_negativeSupport_orderType_eq
    {a : Series K} (haOne : 1 < ordinalValue a)
    (hSType : ((a : K⟦ℝ⟧).isPWO_support.mono
      (s := (a : K⟦ℝ⟧).support ∩ Set.Iio 0)
        Set.inter_subset_left).orderType = (ordinalValue a).val)
    {u : ℝ} (hu : u < 0) :
    ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ordinalValue a := by
  let S : Set ℝ := (a : K⟦ℝ⟧).support ∩ Set.Iio 0
  let hS : S.IsPWO := (a : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have hSLUB : IsLUB S 0 := isLUB_negativeSupport_zero_of_one_lt_ordinalValue haOne
  obtain ⟨y, hy, huy, -⟩ := hSLUB.exists_between hu
  let T : Set ℝ := (HahnSeries.truncLE u (a : K⟦ℝ⟧)).support
  let hT : T.IsPWO := (HahnSeries.truncLE u (a : K⟦ℝ⟧)).isPWO_support
  have hTsub : T ⊆ S ∩ Set.Iio y := by
    intro x hx
    change x ∈ (HahnSeries.truncLE u (a : K⟦ℝ⟧)).support at hx
    rw [HahnSeries.support_truncLE] at hx
    exact ⟨⟨hx.1, hx.2.trans_lt hu⟩, hx.2.trans_lt huy⟩
  have hTlt : hT.orderType < hS.orderType :=
    (hT.orderType_mono
      (hS.mono (s := S ∩ Set.Iio y) Set.inter_subset_left) hTsub).trans_lt
        (hS.orderType_inter_Iio_lt hy)
  calc
    ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) ≤
        NatOrdinal.of
          ((translatedTruncation (a : K⟦ℝ⟧) u : Series K) : K⟦ℝ⟧).supportOrderType :=
      ordinalValue_le_supportOrderType _
    _ = NatOrdinal.of hT.orderType := by
      rw [coe_translatedTruncation, HahnSeries.supportOrderType_translate,
        HahnSeries.supportOrderType_eq_setOrderType]
    _ < NatOrdinal.of (ordinalValue a).val := by
      apply NatOrdinal.of.lt_iff_lt.mpr
      rwa [hSType] at hTlt
    _ = ordinalValue a := by rw [NatOrdinal.of_val]

private theorem ordinalValue_translatedTruncation_lt {a : Series K}
    (ha : IsGermLike a) (ha0 : a ≠ 0) {u : ℝ} (hu : u < 0) :
    ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ordinalValue a := by
  rcases ha.elim with haType | ⟨haOne, haType⟩
  · exact ordinalValue_translatedTruncation_lt_of_supportOrderType_eq haType
      (fun hzero ↦ ha0 (Subtype.ext (HahnSeries.supportOrderType_eq_zero.mp (by
        simpa [hzero] using haType)))) hu
  · exact ordinalValue_translatedTruncation_lt_of_negativeSupport_orderType_eq
      haOne (negativeSupport_orderType_eq_ordinalValue haOne haType) hu

/-- LM17, Lemma 4.4, forward direction: a nonzero germ-like series has critical point zero. -/
theorem IsGermLike.isCriticalPoint_zero {a : Series K}
    (ha : IsGermLike a) (ha0 : a ≠ 0) :
    IsCriticalPoint a 0 := by
  rw [isCriticalPoint_iff]
  refine ⟨ha0, le_rfl, ?_, ?_⟩
  · intro y hy
    rcases hy.eq_or_lt with rfl | hy
    · exact le_rfl
    · simpa using (ordinalValue_translatedTruncation_lt ha ha0 hy).le
  · intro y _ hvalue
    by_contra hnot
    have hylt : y < 0 := lt_of_not_ge hnot
    exact (ordinalValue_translatedTruncation_lt ha ha0 hylt).ne (by simpa using hvalue)

/-- LM17, Lemma 4.5 and Corollary 4.6: if a series with critical point zero is a product of
two nonzero series, then both factors have critical point zero. -/
theorem factors_isCriticalPoint_zero [CharZero K]
    {a b c : Series K} (ha : IsCriticalPoint a 0)
    (habc : a = b * c) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    IsCriticalPoint b 0 ∧ IsCriticalPoint c 0 := by
  obtain ⟨x, hx⟩ := exists_isCriticalPoint hb0
  obtain ⟨y, hy⟩ := exists_isCriticalPoint hc0
  have hxy0 : x + y ≤ 0 := add_nonpos hx.nonpositive hy.nonpositive
  have hbLe :
      ordinalValue b ≤ ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) := by
    simpa using hx.value_le 0 le_rfl
  have hcLe :
      ordinalValue c ≤ ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) := by
    simpa using hy.value_le 0 le_rfl
  have hcriticalEq :
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) (x + y)) =
        ordinalValue a := by
    apply le_antisymm
    · simpa using ha.value_le (x + y) hxy0
    · calc
        ordinalValue a = ordinalValue b * ordinalValue c := by
          rw [habc, ordinalValue_mul]
        _ ≤ ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) *
              ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) :=
          mul_le_mul hbLe hcLe bot_le bot_le
        _ = ordinalValue
              (translatedTruncation (((b * c : Series K) : K⟦ℝ⟧)) (x + y)) :=
          (criticalPoint_product_value hx hy).symm
        _ = ordinalValue (translatedTruncation (a : K⟦ℝ⟧) (x + y)) := by
          rw [habc]
  have hzeroLe : 0 ≤ x + y :=
    ha.le_of_value_eq (x + y) hxy0 (by simpa using hcriticalEq)
  have hx0 : x = 0 :=
    le_antisymm hx.nonpositive (by linarith [hzeroLe, hy.nonpositive])
  have hy0 : y = 0 :=
    le_antisymm hy.nonpositive (by linarith [hzeroLe, hx.nonpositive])
  exact ⟨hx0 ▸ hx, hy0 ▸ hy⟩

private theorem isUnit_of_ordinalValue_eq_one_of_isCriticalPoint_zero
    {a : Series K} (haValue : ordinalValue a = 1)
    (haCritical : IsCriticalPoint a 0) : IsUnit a := by
  have haConstant :=
    PommersheimShahriari.mem_constantSubgroup_of_ordinalValue_one_of_criticalPoint_zero
      haValue haCritical
  obtain ⟨k, hk⟩ := Berarducci.mem_constantSubgroup_iff.mp haConstant
  have hk0 : k ≠ 0 := by
    intro hzero
    apply haCritical.ne_zero
    rw [← hk, hzero, map_zero]
  rw [← hk]
  exact (isUnit_iff_ne_zero.mpr hk0).map HahnSeries.Nonpositive.C

private theorem one_lt_ordinalValue_of_not_isUnit_of_isCriticalPoint_zero
    {a : Series K} (haUnit : ¬IsUnit a)
    (haCritical : IsCriticalPoint a 0) : 1 < ordinalValue a := by
  have hpos : 0 < ordinalValue a := by
    simpa using haCritical.value_pos
  have hone : ordinalValue a ≠ 1 := fun hvalue ↦
    haUnit (isUnit_of_ordinalValue_eq_one_of_isCriticalPoint_zero hvalue haCritical)
  exact lt_of_le_of_ne (Order.one_le_iff_pos.mpr hpos) (Ne.symm hone)

/-- LM17, Theorem 4.8: every nonzero series with critical point zero admits a finite
factorisation into irreducibles. The theorem is stated through association so that unit factors
are absorbed rather than chosen. -/
theorem exists_factorization_of_isCriticalPoint_zero [CharZero K]
    {a : Series K} (haCritical : IsCriticalPoint a 0) :
    ∃ f : Multiset (Series K),
      (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a := by
  let wf : WellFounded (Function.onFun (fun x y : NatOrdinal ↦ x < y)
      (fun b : Series K ↦ ordinalValue b)) := wellFounded_lt.onFun
  refine wf.induction (C := fun a ↦ IsCriticalPoint a 0 →
      ∃ f : Multiset (Series K),
        (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a) a ?_ haCritical
  intro a ih haCritical
  by_cases haUnit : IsUnit a
  · refine ⟨0, by simp, ?_⟩
    simpa using (associated_one_iff_isUnit.mpr haUnit).symm
  by_cases haIrreducible : Irreducible a
  · exact ⟨{a}, by simpa using haIrreducible, by simp⟩
  obtain ⟨b, c, hbUnit, hcUnit, habc⟩ :=
    (irreducible_or_factor haUnit).resolve_left haIrreducible
  have hb0 : b ≠ 0 := by
    intro hzero
    apply haCritical.ne_zero
    rw [habc, hzero, zero_mul]
  have hc0 : c ≠ 0 := by
    intro hzero
    apply haCritical.ne_zero
    rw [habc, hzero, mul_zero]
  obtain ⟨hbCritical, hcCritical⟩ :=
    factors_isCriticalPoint_zero haCritical habc hb0 hc0
  have hbOne :=
    one_lt_ordinalValue_of_not_isUnit_of_isCriticalPoint_zero hbUnit hbCritical
  have hcOne :=
    one_lt_ordinalValue_of_not_isUnit_of_isCriticalPoint_zero hcUnit hcCritical
  have hbPos : 0 < ordinalValue b := zero_lt_one.trans hbOne
  have hcPos : 0 < ordinalValue c := zero_lt_one.trans hcOne
  have hbLt : ordinalValue b < ordinalValue a := by
    rw [habc, ordinalValue_mul]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hcOne hbPos
  have hcLt : ordinalValue c < ordinalValue a := by
    rw [habc, ordinalValue_mul]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hbOne hcPos
  obtain ⟨fb, hfbIrr, hfb⟩ := ih b hbLt hbCritical
  obtain ⟨fc, hfcIrr, hfc⟩ := ih c hcLt hcCritical
  refine ⟨fb + fc, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · exact hfbIrr x hx
    · exact hfcIrr x hx
  · rw [Multiset.prod_add]
    simpa [habc] using hfb.mul_mul hfc

/-- LM17, Theorem 4.8: every nonzero germ-like series admits a finite factorisation into
irreducibles. -/
theorem IsGermLike.exists_factorization [CharZero K]
    {a : Series K} (ha : IsGermLike a) (ha0 : a ≠ 0) :
    ∃ f : Multiset (Series K),
      (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a :=
  exists_factorization_of_isCriticalPoint_zero (ha.isCriticalPoint_zero ha0)

end LM17
