/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.Factorization

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.GermDegree
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType

/-!
# Support and ordinal value in PS06 degree two

This module supplies the support-theoretic input to Pommersheim--Shahriari, Lemma 3.1. A series
outside `J + K` whose support has order type `ω²` or `ω² + 1` has negative support of
order type exactly `ω²`. Its value is therefore `ω²`, while every translated truncation at
a strictly negative cutoff has smaller value.

These conclusions precede the factorisation argument: they derive Berarducci's value hypotheses
directly from the two visible support-order alternatives used in PS06.

## References

* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace PommersheimShahriari

open Berarducci HahnSeries Ordinal

variable {K : Type v} [Field K]

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

/-- A series outside `J + K`, of support order type `ω²` or `ω² + 1`, has strictly
negative support of order type exactly `ω²`. -/
theorem negativeSupport_orderType_eq_wpow_two
    {a : Series K} (haNear : a ∉ nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType =
        (Ordinal.omega0 ^ (2 : Ordinal)) ∨
      (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ (2 : Ordinal) + 1) :
    ((a : K⟦ℝ⟧).isPWO_support.mono
      (s := (a : K⟦ℝ⟧).support ∩ Set.Iio 0)
        Set.inter_subset_left).orderType = Ordinal.omega0 ^ (2 : Ordinal) := by
  let S : Set ℝ := (a : K⟦ℝ⟧).support ∩ Set.Iio 0
  let hS : S.IsPWO := (a : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have haOne : 1 < ordinalValue a := one_lt_ordinalValue_iff.mpr haNear
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
    rcases haType with haType | haType
    · exact hsplit.symm.trans haType
    · have hbad : hS.orderType = Ordinal.omega0 ^ (2 : Ordinal) + 1 :=
        hsplit.symm.trans haType
      rw [hbad, ← Order.succ_eq_add_one] at hSlimit
      exact (Order.not_isSuccLimit_succ _ hSlimit).elim
  · rw [hz, htruncType] at hsplit
    rcases haType with haType | haType
    · have hbad : Ordinal.omega0 ^ (2 : Ordinal) = hS.orderType + 1 :=
        haType.symm.trans hsplit
      have homegaLimit : Order.IsSuccLimit (Ordinal.omega0 ^ (2 : Ordinal)) :=
        Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (by norm_num)
      rw [hbad, ← Order.succ_eq_add_one] at homegaLimit
      exact (Order.not_isSuccLimit_succ _ homegaLimit).elim
    · have heq : Ordinal.omega0 ^ (2 : Ordinal) + 1 = hS.orderType + 1 :=
        haType.symm.trans hsplit
      exact (Ordinal.add_right_cancel 1).mp (by simpa using heq) |>.symm

/-- Every translated truncation at a strictly negative cutoff has ordinal value below `ω²`
under the degree-two PS06 hypotheses. -/
theorem ordinalValue_translatedTruncation_lt_wpow_two
    {a : Series K} (haNear : a ∉ nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType =
        (Ordinal.omega0 ^ (2 : Ordinal)) ∨
      (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ (2 : Ordinal) + 1)
    {u : ℝ} (hu : u < 0) :
    ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ω^ (2 : NatOrdinal) := by
  let S : Set ℝ := (a : K⟦ℝ⟧).support ∩ Set.Iio 0
  let hS : S.IsPWO := (a : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have hSType : hS.orderType = Ordinal.omega0 ^ (2 : Ordinal) :=
    negativeSupport_orderType_eq_wpow_two haNear haType
  have haOne : 1 < ordinalValue a := one_lt_ordinalValue_iff.mpr haNear
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
    _ < NatOrdinal.of (Ordinal.omega0 ^ (2 : Ordinal)) := by
      apply NatOrdinal.of.lt_iff_lt.mpr
      rwa [hSType] at hTlt
    _ = ω^ (2 : NatOrdinal) := by
      rw [NatOrdinal.of_omega0_opow]
      congr 1

private theorem degree_eq_two
    {a : Series K} (haNear : a ∉ nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType =
        (Ordinal.omega0 ^ (2 : Ordinal)) ∨
      (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ (2 : Ordinal) + 1) :
    (a : K⟦ℝ⟧).degree = (2 : WithBot NatOrdinal) := by
  change (a : K⟦ℝ⟧).degree =
    ((NatOrdinal.of (2 : Ordinal)) : WithBot NatOrdinal)
  have haNe : (a : K⟦ℝ⟧) ≠ 0 := by
    intro ha
    apply haNear
    have haSeries : a = 0 := Subtype.ext ha
    rw [haSeries]
    exact (nearConstantSubgroup K).zero_mem
  apply le_antisymm
  · rw [← Order.lt_succ_iff]
    change (a : K⟦ℝ⟧).degree <
      Order.succ ((NatOrdinal.of (2 : Ordinal)) : WithBot NatOrdinal)
    rw [WithBot.orderSucc_coe, Order.succ_eq_add_one]
    apply (HahnSeries.degree_lt_coe_iff_supportOrderType_lt_wpow
      (a : K⟦ℝ⟧) (NatOrdinal.of (2 : Ordinal) + 1)).mpr
    simp only [NatOrdinal.val_wpow, NatOrdinal.val_add_one, NatOrdinal.val_of]
    rcases haType with haType | haType
    · rw [haType]
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
        (Order.lt_succ (2 : Ordinal))
    · rw [haType]
      simpa [Ordinal.opow_add] using
        (Ordinal.opow_mul_add_lt_opow_mul
          (b := Ordinal.omega0) (u := 2) (w := 1) (v := 1) (x := Ordinal.omega0)
          (by norm_num) Ordinal.one_lt_omega0)
  · have hlow := (HahnSeries.coe_le_degree_iff
      (x := (a : K⟦ℝ⟧)) (a := (2 : Ordinal)) haNe).mpr (by
        rcases haType with haType | haType
        · exact haType.ge
        · rw [haType]
          exact le_self_add)
    exact hlow

/-- A non-near-constant series of support order type `ω²` or `ω² + 1` has
Berarducci ordinal value exactly `ω²`. -/
theorem ordinalValue_eq_wpow_two
    {a : Series K} (haNear : a ∉ nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType =
        (Ordinal.omega0 ^ (2 : Ordinal)) ∨
      (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ (2 : Ordinal) + 1) :
    ordinalValue a = ω^ (2 : NatOrdinal) := by
  let S : Set ℝ := (a : K⟦ℝ⟧).support ∩ Set.Iio 0
  let hS : S.IsPWO := (a : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have hSType : hS.orderType = Ordinal.omega0 ^ (2 : Ordinal) :=
    negativeSupport_orderType_eq_wpow_two haNear haType
  have hSLUB : IsLUB S 0 :=
    isLUB_negativeSupport_zero_of_one_lt_ordinalValue (one_lt_ordinalValue_iff.mpr haNear)
  have hvalueLower : ω^ (2 : NatOrdinal) ≤ ordinalValue a := by
    have hordinary : NatOrdinal.of (Ordinal.omega0 ^ (2 : Ordinal)) ≤
        ordinalValue (translatedTruncation (a : K⟦ℝ⟧) 0) := by
      apply le_ordinalValue_translatedTruncation_of_forall_le_orderType
      intro θ hθ
      obtain ⟨y, hy, hθy, -⟩ := hSLUB.exists_between hθ
      let U : Set ℝ := S ∩ Set.Ioi θ
      let hU : U.IsPWO := hS.mono Set.inter_subset_left
      let W : Set ℝ := (a : K⟦ℝ⟧).support ∩ Set.Ioo θ 0
      let hW : W.IsPWO := (a : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
      have hprincipal : IsPrincipal (fun x y : Ordinal ↦ x + y) hS.orderType := by
        rw [hSType]
        exact Ordinal.isPrincipal_add_omega0_opow 2
      have hUType : hU.orderType = hS.orderType :=
        hS.orderType_inter_Ioi_eq_of_isPrincipal hprincipal ⟨y, hy, hθy⟩
      have hUW : U = W := by
        ext x
        simp only [U, W, S, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi,
          Set.mem_Ioo]
        tauto
      have hwindowType : Ordinal.omega0 ^ (2 : Ordinal) =
          ((a : K⟦ℝ⟧).isPWO_support.mono
            (s := (a : K⟦ℝ⟧).support ∩ Set.Ioo θ 0)
              Set.inter_subset_left).orderType := by
        calc
          Ordinal.omega0 ^ (2 : Ordinal) = hS.orderType := hSType.symm
          _ = hU.orderType := hUType.symm
          _ = ((a : K⟦ℝ⟧).isPWO_support.mono
              (s := (a : K⟦ℝ⟧).support ∩ Set.Ioo θ 0)
                Set.inter_subset_left).orderType := by
            simpa only [hW, W] using hU.orderType_congr hW hUW
      exact hwindowType.le
    rw [translatedTruncation_zero] at hordinary
    rw [NatOrdinal.of_omega0_opow] at hordinary
    convert hordinary using 1
  have hdegree : (a : K⟦ℝ⟧).degree = (2 : WithBot NatOrdinal) :=
    degree_eq_two haNear haType
  have hvalueDegreeGe : (2 : WithBot NatOrdinal) ≤ ordinalValueDegree a := by
    rw [← not_lt]
    intro hlt
    exact (not_lt_of_ge hvalueLower) ((ordinalValueDegree_lt_coe_iff a 2).mp hlt)
  have hvalueDegreeLe : ordinalValueDegree a ≤ (2 : WithBot NatOrdinal) :=
    (ordinalValueDegree_le_degree a).trans_eq hdegree
  exact (ordinalValueDegree_eq_coe_iff a 2).mp
    (le_antisymm hvalueDegreeLe hvalueDegreeGe)

end PommersheimShahriari
