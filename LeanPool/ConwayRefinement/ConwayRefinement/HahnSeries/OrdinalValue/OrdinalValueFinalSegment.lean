/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Negative
import Mathlib.Tactic.Linarith

/-!
# Final support segments and Berarducci's ordinal value

This module proves the support consequence of Berarducci's three-clause ordinal value used in the
proof of Lemma 6.9. Every nonempty final segment of the strictly negative support of a
nonpositive series has ordinary order type at least the series' ordinal value. The exponent zero
must be excluded: a nonzero constant coefficient would otherwise give the singleton final segment
`{0}`, independently of the third-branch value.

Translation gives the corresponding theorem for a final segment of a Hahn-series support strictly
below an arbitrary cutoff `γ`. A separate theorem proves that representatives congruent modulo
`J + K` have equal values after truncation and translation at every sufficiently large negative
cutoff. Together these results isolate the value-theoretic part of Berarducci, Lemma 6.9 from its
remaining cofinal reindexing argument.

-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries Ordinal

variable {K : Type v} [Field K]

/-- The ordinal value is bounded above by the ordinary order type of every nonempty final segment
of the strictly negative support. -/
theorem ordinalValue_le_orderType_of_isRelUpperSet_negativeSupport
    {b : Series K} {C : Set ℝ}
    (hC : IsRelUpperSet C (· ∈ (b : K⟦ℝ⟧).support ∩ Set.Iio 0))
    (hCne : C.Nonempty) :
    (ordinalValue b).val ≤
      ((b : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType := by
  classical
  let c : Series K :=
    ⟨HahnSeries.filter (· ∈ C) (b : K⟦ℝ⟧), by
      rw [HahnSeries.mem_nonpositiveSubring]
      exact (HahnSeries.support_filter_subset (· ∈ C) (b : K⟦ℝ⟧)).trans
        (HahnSeries.Nonpositive.support_subset b)⟩
  have hcSupport : (c : K⟦ℝ⟧).support = C := by
    change (HahnSeries.filter (· ∈ C) (b : K⟦ℝ⟧)).support = C
    rw [HahnSeries.support_filter]
    ext x
    constructor
    · exact fun hx ↦ hx.2
    · intro hx
      exact ⟨(hC hx).1.1, hx⟩
  obtain ⟨a, haC⟩ := hCne
  have ha := (hC haC).1
  have hbc : b - c ∈ nearConstantSubgroup K := by
    rw [mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem]
    rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero]
    let q := b - c - HahnSeries.Nonpositive.C
      (HahnSeries.Nonpositive.constantCoeff (b - c))
    change HahnSeries.Nonpositive.supportSup q < 0
    by_cases hq : q = 0
    · simp [hq]
    · rw [HahnSeries.Nonpositive.supportSup_of_ne hq]
      apply WithBot.coe_lt_coe.mpr
      refine (csSup_le (HahnSeries.support_nonempty_iff.mpr ?_) ?_).trans_lt ha.2
      · simpa using hq
      · intro x hx
        apply le_of_not_gt
        intro hax
        have hx0 : x ≤ 0 := HahnSeries.Nonpositive.support_subset q hx
        rcases hx0.eq_or_lt with rfl | hx0
        · have hcoeff : (q : K⟦ℝ⟧).coeff 0 = 0 := by
            simp [q]
          exact (HahnSeries.mem_support _ _).mp hx hcoeff
        · by_cases hxb : x ∈ (b : K⟦ℝ⟧).support
          · have hxC : x ∈ C := (hC haC).2 hax.le ⟨hxb, hx0⟩
            have hcCoeff : (c : K⟦ℝ⟧).coeff x = (b : K⟦ℝ⟧).coeff x := by
              simp [c, hxC]
            have hcoeff : (q : K⟦ℝ⟧).coeff x = 0 := by
              simp [q, hcCoeff, hx0.ne]
            exact (HahnSeries.mem_support _ _).mp hx hcoeff
          · have hbCoeff : (b : K⟦ℝ⟧).coeff x = 0 := by
              rwa [← not_ne_iff, ← HahnSeries.mem_support]
            have hcoeff : (q : K⟦ℝ⟧).coeff x = 0 := by
              simp [q, c, hbCoeff, hx0.ne]
            exact (HahnSeries.mem_support _ _).mp hx hcoeff
  rw [NatOrdinal.val_le_iff]
  by_cases hb : 1 < ordinalValue b
  · have hcCandidate :
        NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType ∈ representativeOrderTypes b :=
      mem_representativeOrderTypes_iff.mpr ⟨c, hbc, rfl⟩
    have hvalue := (ordinalValue_isLeast_representativeOrderTypes
      (one_lt_ordinalValue_iff.mp hb)).2 hcCandidate
    calc
      ordinalValue b ≤ NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType := hvalue
      _ = NatOrdinal.of
          (((b : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType) := by
        apply congrArg NatOrdinal.of
        rw [HahnSeries.supportOrderType_eq_setOrderType]
        exact (c : K⟦ℝ⟧).isPWO_support.orderType_congr
          ((b : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hC hx).1.1) hcSupport
  · apply (le_of_not_gt hb).trans
    rw [Order.one_le_iff_pos]
    apply NatOrdinal.of.lt_iff_lt.mpr
    apply bot_lt_iff_ne_bot.mpr
    intro htypeZero
    have hCempty :=
      (((b : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType_eq_zero).mp
        htypeZero
    simp [hCempty] at haC

/-- A series with nonzero ordinal value has support with least upper bound zero. -/
theorem isLUB_support_zero_of_ordinalValue_ne_zero
    {b : Series K} (hb : ordinalValue b ≠ 0) :
    IsLUB (b : K⟦ℝ⟧).support 0 := by
  have hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    rwa [← ordinalValue_eq_zero_iff]
  have hbne : b ≠ 0 := by
    intro hbzero
    apply hbJ
    rw [hbzero]
    exact (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem
  have hsup : HahnSeries.Nonpositive.supportSup b = 0 := by
    apply le_antisymm (HahnSeries.Nonpositive.supportSup_le_zero b)
    apply le_of_not_gt
    intro hlt
    exact hbJ
      (HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mpr hlt)
  exact (HahnSeries.Nonpositive.supportSup_eq_coe_iff.mp hsup).2

/-- A series of ordinal value greater than one has strictly negative support with least upper
bound zero. -/
theorem isLUB_negativeSupport_zero_of_one_lt_ordinalValue
    {b : Series K} (hb : 1 < ordinalValue b) :
    IsLUB ((b : K⟦ℝ⟧).support ∩ Set.Iio 0) 0 := by
  let n : HahnSeries.Negative ℝ K := HahnSeries.Nonpositive.negativePart ℝ K b
  have hnJ : (n : Series K) ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    intro hnJ
    apply (one_lt_ordinalValue_iff.mp hb)
    apply mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mpr
    simpa only [n, HahnSeries.Nonpositive.coe_negativePart] using hnJ
  have hn : (n : Series K) ≠ 0 := by
    intro hn
    apply hnJ
    rw [hn]
    exact (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem
  have hsup : HahnSeries.Nonpositive.supportSup (n : Series K) = 0 := by
    apply le_antisymm (HahnSeries.Nonpositive.supportSup_le_zero (n : Series K))
    apply le_of_not_gt
    intro hlt
    exact hnJ
      (HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mpr hlt)
  have hLUB :=
    (HahnSeries.Nonpositive.supportSup_eq_coe_iff.mp hsup).2
  simpa only [n, HahnSeries.Nonpositive.support_negativePart] using hLUB

/-- After translating a cutoff to zero, the ordinal value is bounded above by the ordinary order
type of every nonempty final segment of the support strictly below that cutoff. -/
theorem ordinalValue_translatedTruncation_le_orderType_of_isRelUpperSet_supportBelow
    (b : K⟦ℝ⟧) (γ : ℝ) {C : Set ℝ}
    (hC : IsRelUpperSet C (· ∈ b.support ∩ Set.Iio γ))
    (hCne : C.Nonempty) :
    (ordinalValue (translatedTruncation b γ)).val ≤
      (b.isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType := by
  let shifted : Set ℝ := (-γ + ·) '' C
  have hshifted : IsRelUpperSet shifted
      (· ∈ ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).support ∩ Set.Iio 0) := by
    rintro _ ⟨x, hxC, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [support_translatedTruncation]
      exact ⟨x, ⟨(hC hxC).1.1, (hC hxC).1.2.le⟩, rfl⟩
    · have hxγ := (hC hxC).1.2
      change x < γ at hxγ
      change -γ + x < 0
      linarith
    · intro y hxy hy
      rw [support_translatedTruncation] at hy
      obtain ⟨⟨z, hz, hzEq⟩, hy0⟩ := hy
      subst y
      refine ⟨z, ?_, rfl⟩
      apply (hC hxC).2
      · linarith
      · refine ⟨hz.1, ?_⟩
        change -γ + z < 0 at hy0
        change z < γ
        linarith
  have hshiftedNonempty : shifted.Nonempty := hCne.image _
  have hbound := ordinalValue_le_orderType_of_isRelUpperSet_negativeSupport
    hshifted hshiftedNonempty
  let hCPWO : C.IsPWO := b.isPWO_support.mono fun _ hx ↦ (hC hx).1.1
  let hshiftedPWO : shifted.IsPWO :=
    ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).isPWO_support.mono
      fun _ hx ↦ (hshifted hx).1.1
  letI : WellFoundedLT C := ⟨hCPWO.isWF⟩
  letI : WellFoundedLT shifted := ⟨hshiftedPWO.isWF⟩
  let f : C → shifted := fun x ↦ ⟨-γ + x.1, x.1, x.2, rfl⟩
  have hf : StrictMono f := by
    intro x y hxy
    change x.1 < y.1 at hxy
    change -γ + x.1 < -γ + y.1
    linarith
  have hsurjective : Function.Surjective f := by
    rintro ⟨_, x, hxC, rfl⟩
    exact ⟨⟨x, hxC⟩, rfl⟩
  let e : C ≃o shifted := hf.orderIsoOfSurjective f hsurjective
  have htype : hshiftedPWO.orderType = hCPWO.orderType := by
    calc
      hshiftedPWO.orderType = typeLT C :=
        hshiftedPWO.orderType_eq_typeLT_of_orderIso e.symm
      _ = hCPWO.orderType :=
        (hCPWO.orderType_eq_typeLT_of_orderIso (OrderIso.refl C)).symm
  exact hbound.trans_eq htype

/-- A lower bound on a translated-truncation value is a lower bound on every nonempty final
segment of the support strictly below the cutoff. -/
theorem le_orderType_of_le_ordinalValue_translatedTruncation_of_isRelUpperSet_supportBelow
    (b : K⟦ℝ⟧) (γ : ℝ) {C : Set ℝ} {ρ : Ordinal}
    (hρ : NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation b γ))
    (hC : IsRelUpperSet C (· ∈ b.support ∩ Set.Iio γ))
    (hCne : C.Nonempty) :
    ρ ≤ (b.isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType := by
  apply (NatOrdinal.of.le_iff_le.mp ?_).trans
    (ordinalValue_translatedTruncation_le_orderType_of_isRelUpperSet_supportBelow b γ hC hCne)
  simpa only [NatOrdinal.of_val] using hρ

/-- A uniform lower bound on the ordinary order types of the support windows immediately below
`γ` is a lower bound on the value of the translated truncation at `γ`. This is the converse of
`Berarducci.ordinalValue_translatedTruncation_le_orderType_of_isRelUpperSet_supportBelow`. -/
theorem le_ordinalValue_translatedTruncation_of_forall_le_orderType
    (b : K⟦ℝ⟧) (γ : ℝ) {ρ : Ordinal}
    (h : ∀ θ, θ < γ → ρ ≤ (b.isPWO_support.mono
        (s := b.support ∩ Set.Ioo θ γ) Set.inter_subset_left).orderType) :
    NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation b γ) := by
  apply le_ordinalValue_of_forall_mem_representativeOrderTypes
  intro p hp
  obtain ⟨d, hd, rfl⟩ := mem_representativeOrderTypes_iff.mp hp
  rw [NatOrdinal.of.le_iff_le]
  obtain ⟨θ, hθ, hcoeff⟩ := exists_coeff_eq_of_sub_mem_nearConstantSubgroup hd
  set A : Set ℝ := b.support ∩ Set.Ioo (γ + θ) γ with hA
  have hAPWO : A.IsPWO := b.isPWO_support.mono Set.inter_subset_left
  have hmono : StrictMonoOn (fun x ↦ -γ + x) A := fun _ _ _ _ hxy ↦ by simpa using hxy
  have himage : (fun x ↦ -γ + x) '' A ⊆ (d : K⟦ℝ⟧).support := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxsupp, hxlow, hxhigh⟩ := hx
    have hδ0 : -γ + x ≤ 0 := by linarith
    have hδθ : θ < -γ + x := by linarith
    have hδneg : -γ + x < 0 := by linarith
    have hgerm : ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).coeff (-γ + x) = b.coeff x := by
      rw [coeff_translatedTruncation, ite_eq_left hδ0]
      congr 1
      ring
    rw [HahnSeries.mem_support, ← hcoeff (-γ + x) hδθ hδneg, hgerm]
    exact (HahnSeries.mem_support _ _).mp hxsupp
  calc ρ ≤ hAPWO.orderType := h (γ + θ) (by linarith)
    _ = (hAPWO.image_of_monotoneOn hmono.monotoneOn).orderType :=
        (hAPWO.orderType_image_of_strictMonoOn hmono).symm
    _ ≤ (d : K⟦ℝ⟧).isPWO_support.orderType :=
        (hAPWO.image_of_monotoneOn hmono.monotoneOn).orderType_mono _ himage
    _ = (d : K⟦ℝ⟧).supportOrderType :=
        (HahnSeries.supportOrderType_eq_setOrderType _).symm

/-- Series congruent modulo `J + K` have equal translated-truncation values at every sufficiently
large negative cutoff. -/
theorem exists_ordinalValue_translatedTruncation_eq_of_sub_mem_nearConstantSubgroup
    {b c : Series K} (hbc : b - c ∈ nearConstantSubgroup K) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) γ) =
        ordinalValue (translatedTruncation (c : K⟦ℝ⟧) γ) := by
  obtain ⟨j, hj, k, hjk⟩ := mem_nearConstantSubgroup_iff.mp hbc
  have hjGerm : toGerm j = toGerm 0 := by
    rw [toGerm_eq_toGerm_iff]
    simpa using hj
  obtain ⟨η, hη, hjCoeff⟩ :=
    toGerm_eq_toGerm_iff_exists_coeff_eq.mp hjGerm
  refine ⟨η, hη, fun γ hηγ hγ ↦ ?_⟩
  apply ordinalValue_eq_of_sub_mem_negativeMonomialIdeal
  rw [← toGerm_eq_toGerm_iff]
  apply toGerm_eq_toGerm_iff_exists_coeff_eq.mpr
  refine ⟨η - γ, sub_neg.mpr hηγ, fun δ hδ hδ0 ↦ ?_⟩
  rw [coeff_translatedTruncation, coeff_translatedTruncation, ite_eq_left hδ0, ite_eq_left hδ0]
  have hnear : η < γ + δ := by linarith
  have hnegative : γ + δ < 0 := by linarith
  have hjZero : (j : K⟦ℝ⟧).coeff (γ + δ) = 0 := by
    simpa using hjCoeff (γ + δ) hnear hnegative.le
  have hjkCoeff := congrArg
    (fun q : Series K ↦ (q : K⟦ℝ⟧).coeff (γ + δ)) hjk
  simp only [Subring.coe_add, HahnSeries.coeff_add, HahnSeries.Nonpositive.coe_C,
    HahnSeries.C_apply] at hjkCoeff
  rw [HahnSeries.coeff_single_of_ne hnegative.ne] at hjkCoeff
  simp only [add_zero] at hjkCoeff
  exact sub_eq_zero.mp (hjkCoeff.symm.trans hjZero)

end Berarducci
