/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.DegreeTwo

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueConstantMul
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# The degree-two factorisation classification

This module proves Pommersheim--Shahriari, Lemma 3.1. For an ordered factorisation of a series
outside `J + K` whose support has order type `ω²` or `ω² + 1`, either the first factor is a
nonzero constant, or both factors have value `ω` and support order type `ω` or `ω + 1`.

The final support step is topological. Critical point zero makes every negative translated
truncation of a value-`ω` factor constant modulo `J`. Thus the support is locally finite below
zero; compactness makes each closed negative initial segment finite, forcing order type `ω` with
an optional constant term.

## References

* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
-/

universe v

open scoped HahnSeries NatOrdinal Topology

public noncomputable section

namespace PommersheimShahriari

open Berarducci HahnSeries Ordinal

variable {K : Type v} [Field K]

private theorem not_accPt_support_of_translatedTruncation_mem_nearConstantSubgroup
    {b : Series K} {z : ℝ}
    (hzNear : translatedTruncation (b : K⟦ℝ⟧) z ∈ nearConstantSubgroup K) :
    ¬ AccPt z (Filter.principal (b : K⟦ℝ⟧).support) := by
  have hsub : translatedTruncation (b : K⟦ℝ⟧) z - 0 ∈ nearConstantSubgroup K := by
    simpa using hzNear
  obtain ⟨η, hη0, hcoeff⟩ :=
    exists_coeff_eq_of_sub_mem_nearConstantSubgroup hsub
  let T : Set ℝ := (b : K⟦ℝ⟧).support ∩ Set.Ioi z
  let hT : T.IsWF := (b : K⟦ℝ⟧).isPWO_support.isWF.mono Set.inter_subset_left
  have hright : ∃ r : ℝ, z < r ∧
      ∀ w ∈ (b : K⟦ℝ⟧).support, z < w → r ≤ w := by
    by_cases hTne : T.Nonempty
    · let r := hT.min hTne
      have hrT : r ∈ T := hT.min_mem hTne
      refine ⟨r, hrT.2, ?_⟩
      intro w hw hzw
      exact hT.min_le hTne ⟨hw, hzw⟩
    · refine ⟨z + 1, by linarith, ?_⟩
      intro w hw hzw
      exact (hTne ⟨w, hw, hzw⟩).elim
  intro hzAcc
  rw [accPt_iff_nhds] at hzAcc
  obtain ⟨r, hzr, hright⟩ := hright
  have hnhds : Set.Ioo (z + η) r ∈ nhds z := Ioo_mem_nhds (by linarith) hzr
  obtain ⟨w, ⟨⟨hwLeft, hwRight⟩, hwSupport⟩, hwNe⟩ := hzAcc _ hnhds
  rcases lt_or_gt_of_ne hwNe with hwz | hzw
  · let δ : ℝ := w - z
    have hη0 : η < δ := by dsimp [δ]; linarith
    have hδ0 : δ < 0 := by dsimp [δ]; linarith
    have hzero := hcoeff δ hη0 hδ0
    rw [coeff_translatedTruncation, ite_eq_left hδ0.le] at hzero
    have hcoeffZero : (b : K⟦ℝ⟧).coeff w = 0 := by
      simpa [δ] using hzero
    exact (HahnSeries.mem_support _ _).mp hwSupport hcoeffZero
  · exact (not_lt_of_ge (hright w hwSupport hzw)) hwRight

/-- A negative translated truncation of a value-`ω` series lies in `J + K` when the series has
critical point zero. -/
theorem translatedTruncation_mem_nearConstantSubgroup_of_criticalPoint_zero_of_value_omega
    {b : Series K} (hbCritical : IsCriticalPoint b 0)
    (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
    {z : ℝ} (hz : z < 0) :
    translatedTruncation (b : K⟦ℝ⟧) z ∈ nearConstantSubgroup K := by
  have hcriticalValue :
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) 0) = ω^ (1 : NatOrdinal) := by
    simpa using hbValue
  have hvalueLt : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z) <
      ω^ (1 : NatOrdinal) := by
    rw [← hcriticalValue]
    apply lt_of_le_of_ne (hbCritical.value_le z hz.le)
    intro heq
    exact (not_le_of_gt hz) (hbCritical.le_of_value_eq z hz.le heq)
  by_contra hnear
  have hone : 1 < ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z) :=
    one_lt_ordinalValue_iff.mpr hnear
  have honeVal : (1 : Ordinal) <
      (ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z)).val :=
    NatOrdinal.of_lt_iff.mp hone
  have homegaVal : Ordinal.omega0 ≤
      (ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z)).val :=
    (ordinalValue_isAdditivelyPrincipal_of_one_lt hone).omega0_le_of_one_lt honeVal
  have homega : NatOrdinal.of Ordinal.omega0 ≤
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z) :=
    NatOrdinal.of_le_iff.mpr homegaVal
  have homega' : ω^ (1 : NatOrdinal) ≤
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z) := by
    convert homega using 1
    apply NatOrdinal.val.injective
    simp only [NatOrdinal.val_wpow, NatOrdinal.val_one, NatOrdinal.val_of,
      Ordinal.opow_one]
  exact (not_lt_of_ge homega') hvalueLt

/-- If a factor has value one and critical point zero, it is a constant series. -/
theorem mem_constantSubgroup_of_ordinalValue_one_of_criticalPoint_zero
    {b : Series K} (hbValue : ordinalValue b = 1)
    (hbCritical : IsCriticalPoint b 0) :
    b ∈ constantSubgroup K := by
  have hsupport : (b : K⟦ℝ⟧).support ⊆ {0} := by
    intro z hz
    have hz0 := HahnSeries.Nonpositive.support_subset b hz
    by_cases hzero : z = 0
    · simp [hzero]
    · have hzNeg : z < 0 := lt_of_le_of_ne hz0 hzero
      have hcriticalValue :
          ordinalValue (translatedTruncation (b : K⟦ℝ⟧) 0) = 1 := by
        simpa using hbValue
      have hvalueLt : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z) < 1 := by
        rw [← hcriticalValue]
        apply lt_of_le_of_ne (hbCritical.value_le z hz0)
        intro heq
        exact (not_le_of_gt hzNeg) (hbCritical.le_of_value_eq z hz0 heq)
      have hvalueZero : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) z) = 0 := by
        rwa [Order.lt_one_iff] at hvalueLt
      exact (ne_of_gt (ordinalValue_translatedTruncation_pos_of_mem_support hz) hvalueZero).elim
  apply mem_constantSubgroup_iff.mpr
  refine ⟨HahnSeries.Nonpositive.constantCoeff b, ?_⟩
  apply Subtype.ext
  ext z
  by_cases hz : z = 0
  · subst z
    simp [HahnSeries.Nonpositive.constantCoeff_apply]
  · have hzSupport : z ∉ (b : K⟦ℝ⟧).support := fun hmem ↦
      hz (Set.mem_singleton_iff.mp (hsupport hmem))
    rw [HahnSeries.mem_support] at hzSupport
    rw [not_ne_iff.mp hzSupport]
    simp [hz]

private theorem supportOrderType_eq_omega_or_omega_add_one_of_ordinalValue_omega_criticalPoint_zero
    {b : Series K} (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
    (hbCritical : IsCriticalPoint b 0) :
    (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
      (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1 := by
  let S : Set ℝ := (b : K⟦ℝ⟧).support ∩ Set.Iio 0
  let hS : S.IsPWO := (b : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have hIicFinite : ∀ x ∈ S, (S ∩ Set.Iic x).Finite := by
    intro x hx
    let I : Set ℝ := S ∩ Set.Iic x
    let hI : I.IsPWO := hS.mono Set.inter_subset_left
    by_cases hIne : I.Nonempty
    · let m := hI.isWF.min hIne
      have hmI : m ∈ I := hI.isWF.min_mem hIne
      by_contra hIfinite
      have hIsub : I ⊆ Set.Icc m x := by
        intro y hy
        exact ⟨hI.isWF.min_le hIne hy, hy.2⟩
      obtain ⟨z, hzIcc, hzAcc⟩ :=
        (show I.Infinite from hIfinite).exists_accPt_of_subset_isCompact
          isCompact_Icc hIsub
      have hzNeg : z < 0 := hzIcc.2.trans_lt hx.2
      have hzNear :=
        translatedTruncation_mem_nearConstantSubgroup_of_criticalPoint_zero_of_value_omega
          hbCritical hbValue hzNeg
      apply not_accPt_support_of_translatedTruncation_mem_nearConstantSubgroup hzNear
      exact hzAcc.mono (Filter.principal_mono.mpr fun y hy ↦ hy.1.1)
    · change I.Finite
      rw [Set.not_nonempty_iff_eq_empty.mp hIne]
      exact Set.finite_empty
  have hSle : hS.orderType ≤ Ordinal.omega0 := by
    apply hS.orderType_le_of_forall_inter_Iic_lt
    intro x hx
    exact Set.IsPWO.finite_iff_orderType_lt_omega
      (hS.mono (s := S ∩ Set.Iic x) Set.inter_subset_left) |>.mp (hIicFinite x hx)
  have hSLUB : IsLUB S 0 := by
    apply isLUB_negativeSupport_zero_of_one_lt_ordinalValue
    rw [hbValue]
    apply NatOrdinal.val.lt_iff_lt.mpr
    simp only [NatOrdinal.val_one, Ordinal.opow_one]
    exact Ordinal.one_lt_omega0
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, -, -⟩ := hSLUB.exists_between (show (-1 : ℝ) < 0 by norm_num)
    exact ⟨x, hx⟩
  have hSgt : ∀ x ∈ S, ∃ y ∈ S, x < y := by
    intro x hx
    obtain ⟨y, hy, hxy, -⟩ := hSLUB.exists_between hx.2
    exact ⟨y, hy, hxy⟩
  have hSlimit : Order.IsSuccLimit hS.orderType :=
    hS.isSuccLimit_orderType_of_forall_exists_gt hSne hSgt
  have hSType : hS.orderType = Ordinal.omega0 :=
    le_antisymm hSle (Ordinal.omega0_le_of_isSuccLimit hSlimit)
  have htruncSupport :
      (HahnSeries.truncLT 0 (b : K⟦ℝ⟧)).support = S := by
    rw [HahnSeries.support_truncLT]
    rfl
  have htruncType :
      (HahnSeries.truncLT 0 (b : K⟦ℝ⟧)).supportOrderType = Ordinal.omega0 := by
    rw [HahnSeries.supportOrderType_eq_setOrderType]
    exact ((HahnSeries.truncLT 0 (b : K⟦ℝ⟧)).isPWO_support.orderType_congr
      hS htruncSupport).trans hSType
  have hge : HahnSeries.truncGE 0 (b : K⟦ℝ⟧) =
      HahnSeries.single 0 ((b : K⟦ℝ⟧).coeff 0) := by
    ext x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · simp [HahnSeries.coeff_truncGE, not_le_of_gt hx, hx.ne]
    · simp
    · have hcoeff : (b : K⟦ℝ⟧).coeff x = 0 := by
        apply not_ne_iff.mp
        rw [← HahnSeries.mem_support]
        exact fun hmem ↦ (not_le_of_gt hx)
          (HahnSeries.Nonpositive.support_subset b hmem)
      simp [HahnSeries.coeff_truncGE, hx.le, hcoeff, hx.ne']
  have hsplit := HahnSeries.supportOrderType_eq_truncLT_add_truncGE
    0 (b : K⟦ℝ⟧)
  by_cases hzero : 0 ∈ (b : K⟦ℝ⟧).support
  · right
    have hcoeff : (b : K⟦ℝ⟧).coeff 0 ≠ 0 :=
      (HahnSeries.mem_support _ _).mp hzero
    have hgeType :
        (HahnSeries.truncGE 0 (b : K⟦ℝ⟧)).supportOrderType = 1 := by
      rw [hge]
      exact HahnSeries.supportOrderType_single hcoeff
    rw [htruncType, hgeType] at hsplit
    exact hsplit
  · left
    have hcoeff : (b : K⟦ℝ⟧).coeff 0 = 0 := by
      rw [HahnSeries.mem_support] at hzero
      exact not_ne_iff.mp hzero
    have hgeType :
        (HahnSeries.truncGE 0 (b : K⟦ℝ⟧)).supportOrderType = 0 := by
      rw [hge]
      simp [hcoeff]
    rw [htruncType, hgeType, add_zero] at hsplit
    exact hsplit

/-- PS06, Lemma 3.1: an ordered factorisation of a degree-two series has either a nonzero
constant first factor, or two factors of value `ω` and support order type `ω` or `ω + 1`. -/
theorem factorization_cases_of_supportOrderType_wpow_two
    [CharZero K] {a b c : Series K}
    (haNear : a ∉ nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType =
        (Ordinal.omega0 ^ (2 : Ordinal)) ∨
      (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ (2 : Ordinal) + 1)
    (habc : a = b * c) (hle : ordinalValue b ≤ ordinalValue c) :
    (∃ k : K, k ≠ 0 ∧ b = HahnSeries.Nonpositive.C k ∧
      c = HahnSeries.Nonpositive.C k⁻¹ * a ∧
      (c : K⟦ℝ⟧).supportOrderType = (a : K⟦ℝ⟧).supportOrderType) ∨
      (((b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
          (b : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
        ((c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
          (c : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1) ∧
        ordinalValue b = ω^ (1 : NatOrdinal) ∧
        ordinalValue c = ω^ (1 : NatOrdinal)) := by
  have haNe : a ≠ 0 := by
    intro ha
    apply haNear
    rw [ha]
    exact (nearConstantSubgroup K).zero_mem
  have hbNe : b ≠ 0 := by
    intro hb
    apply haNe
    rw [habc, hb, zero_mul]
  have hcNe : c ≠ 0 := by
    intro hc
    apply haNe
    rw [habc, hc, mul_zero]
  obtain ⟨x, hx⟩ := exists_isCriticalPoint hbNe
  obtain ⟨y, hy⟩ := exists_isCriticalPoint hcNe
  have haValue : ordinalValue a = ω^ (2 : NatOrdinal) :=
    ordinalValue_eq_wpow_two haNear haType
  have haNegative : ∀ u : ℝ, u < 0 →
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ω^ (2 : NatOrdinal) :=
    fun _ hu ↦ ordinalValue_translatedTruncation_lt_wpow_two haNear haType hu
  have hmulValue : ordinalValue b * ordinalValue c = ω^ (2 : NatOrdinal) := by
    rw [← ordinalValue_mul, ← habc, haValue]
  have hcritical := criticalPoints_eq_zero_of_product_wpow_two
    habc haValue haNegative hx hy
  obtain ⟨rfl, rfl⟩ := hcritical
  rcases ordinalValue_factors_of_mul_eq_wpow_two hmulValue hle with
    hconstant | hbalanced
  · left
    have hbConstant :=
      mem_constantSubgroup_of_ordinalValue_one_of_criticalPoint_zero hconstant.1 hx
    obtain ⟨k, hk⟩ := mem_constantSubgroup_iff.mp hbConstant
    have hkNe : k ≠ 0 := by
      intro hkZero
      apply hbNe
      rw [← hk, hkZero]
      simp
    have hbc : b = HahnSeries.Nonpositive.C k := hk.symm
    have hc : c = HahnSeries.Nonpositive.C k⁻¹ * a := by
      rw [habc, hbc]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hkNe, map_one, one_mul]
    refine ⟨k, hkNe, hbc, hc, ?_⟩
    rw [habc, hbc, supportOrderType_C_mul_of_ne_zero hkNe]
  · right
    exact ⟨supportOrderType_eq_omega_or_omega_add_one_of_ordinalValue_omega_criticalPoint_zero
        hbalanced.1 hx,
      supportOrderType_eq_omega_or_omega_add_one_of_ordinalValue_omega_criticalPoint_zero
        hbalanced.2 hy,
      hbalanced⟩

end PommersheimShahriari
