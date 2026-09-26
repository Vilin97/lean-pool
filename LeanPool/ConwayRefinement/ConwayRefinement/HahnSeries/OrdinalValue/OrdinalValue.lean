/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Basic

import Mathlib.Tactic.Abel

/-!
# Berarducci's ordinal value

This module defines the ordinal value `Berarducci.ordinalValue` by the three disjoint clauses in
Berarducci, Definition 5.2 and LM24, Section 2.7:

* it is zero on the negative-monomial ideal `J`;
* it is one on `(J + K) \ J`;
* otherwise it is the least support order type among representatives congruent modulo `J + K`.

`NatOrdinal` is a type synonym for ordinals equipped with Hessenberg addition and multiplication;
its underlying order is the ordinary ordinal order. Using it here preserves the source value while
making the later multiplicative statement type-correct without introducing parallel operations.

The third branch is not postulated to have a minimum. Its candidate set contains the original
series, and the well-order of `NatOrdinal` proves that its infimum is a member and is least. The
characteristic theorems prove the exact zero and one fibers, invariance modulo `J`, and the induced
separated value on the germ quotient. No additive or multiplicative law is asserted in this file.

The definition and these order-theoretic properties make sense over any field. Berarducci's
additive and multiplicative theorems retain the source's characteristic-zero hypothesis.
-/

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- The support order types of series congruent to `b` modulo Berarducci's subgroup `J + K`. -/
def representativeOrderTypes (b : Series K) : Set NatOrdinal :=
  {o | ∃ c : Series K,
    b - c ∈ nearConstantSubgroup K ∧
      NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType = o}

/-- Membership in the set of support order types of representatives congruent to `b`. -/
theorem mem_representativeOrderTypes_iff {b : Series K} {o : NatOrdinal} :
    o ∈ representativeOrderTypes b ↔
      ∃ c : Series K,
        b - c ∈ nearConstantSubgroup K ∧
          NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType = o := by
  rfl

/-- The candidate set for the third branch of the ordinal value is nonempty. -/
theorem representativeOrderTypes_nonempty (b : Series K) :
    (representativeOrderTypes b).Nonempty := by
  refine ⟨NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType, b, ?_, rfl⟩
  simp

/-- Berarducci's ordinal value on nonpositive real Hahn series. -/
noncomputable def ordinalValue (b : Series K) : NatOrdinal := by
  classical
  exact if b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K then 0
    else if b ∈ nearConstantSubgroup K then 1
    else sInf (representativeOrderTypes b)

/-- The first defining clause of the ordinal value. -/
theorem ordinalValue_of_mem_negativeMonomialIdeal {b : Series K}
    (hb : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    ordinalValue b = 0 := by
  simp [ordinalValue, hb]

/-- The second defining clause of the ordinal value. -/
theorem ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
    {b : Series K} (hbNear : b ∈ nearConstantSubgroup K)
    (hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    ordinalValue b = 1 := by
  simp [ordinalValue, hbJ, hbNear]

/-- The third defining clause of the ordinal value. -/
theorem ordinalValue_of_not_mem_nearConstantSubgroup {b : Series K}
    (hb : b ∉ nearConstantSubgroup K) :
    ordinalValue b = sInf (representativeOrderTypes b) := by
  have hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K :=
    fun hbJ ↦ hb (negativeMonomialIdeal_le_nearConstantSubgroup hbJ)
  simp [ordinalValue, hbJ, hb]

/-- Outside `J + K`, the ordinal value is attained by a congruent representative. -/
theorem ordinalValue_mem_representativeOrderTypes_of_not_mem_nearConstantSubgroup
    {b : Series K}
    (hb : b ∉ nearConstantSubgroup K) :
    ordinalValue b ∈ representativeOrderTypes b := by
  rw [ordinalValue_of_not_mem_nearConstantSubgroup hb]
  exact csInf_mem (representativeOrderTypes_nonempty b)

/-- The support order type of a nonzero constant series is one. -/
private theorem supportOrderType_C_eq_one {k : K} (hk : k ≠ 0) :
    ((HahnSeries.Nonpositive.C k : Series K) : K⟦ℝ⟧).supportOrderType = 1 := by
  rw [HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply]
  exact HahnSeries.supportOrderType_single hk

/-- In every branch of its definition, the ordinal value is attained by a representative
congruent modulo `J + K`. -/
theorem ordinalValue_mem_representativeOrderTypes (b : Series K) :
    ordinalValue b ∈ representativeOrderTypes b := by
  by_cases hbJ : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
  · rw [ordinalValue_of_mem_negativeMonomialIdeal hbJ]
    apply mem_representativeOrderTypes_iff.mpr
    refine ⟨0, ?_, by simp⟩
    exact negativeMonomialIdeal_le_nearConstantSubgroup (by simpa using hbJ)
  by_cases hbNear : b ∈ nearConstantSubgroup K
  · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
      hbNear hbJ]
    let k := HahnSeries.Nonpositive.constantCoeff b
    have hk : k ≠ 0 := by
      intro hk
      apply hbJ
      have hsub := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hbNear
      simpa [k, hk] using hsub
    apply mem_representativeOrderTypes_iff.mpr
    refine ⟨HahnSeries.Nonpositive.C k, ?_, ?_⟩
    · exact negativeMonomialIdeal_le_nearConstantSubgroup
        (mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hbNear)
    · rw [supportOrderType_C_eq_one hk]
      simp
  · exact ordinalValue_mem_representativeOrderTypes_of_not_mem_nearConstantSubgroup hbNear

/-- A common lower bound for all representative support order types is a lower bound for the
ordinal value. -/
theorem le_ordinalValue_of_forall_mem_representativeOrderTypes
    {b : Series K} {o : NatOrdinal}
    (h : ∀ p ∈ representativeOrderTypes b, o ≤ p) :
    o ≤ ordinalValue b :=
  h _ (ordinalValue_mem_representativeOrderTypes b)

/-- Outside `J + K`, the ordinal value is the least candidate support order type. -/
theorem ordinalValue_isLeast_representativeOrderTypes {b : Series K}
    (hb : b ∉ nearConstantSubgroup K) :
    IsLeast (representativeOrderTypes b) (ordinalValue b) := by
  refine ⟨ordinalValue_mem_representativeOrderTypes b, ?_⟩
  intro o ho
  rw [ordinalValue_of_not_mem_nearConstantSubgroup hb]
  exact csInf_le' ho

private theorem mem_nearConstantSubgroup_of_supportOrderType_le_one
    {b : Series K}
    (hbType : NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType ≤ 1) :
    b ∈ nearConstantSubgroup K := by
  rcases Order.le_one_iff.mp hbType with hbZero | hbOne
  · have hbTypeZero : (b : K⟦ℝ⟧).supportOrderType = 0 := by
      simpa using hbZero
    have hb : b = 0 := by
      apply Subtype.ext
      exact HahnSeries.supportOrderType_eq_zero.mp hbTypeZero
    subst b
    exact (nearConstantSubgroup K).zero_mem
  · have hbTypeOne : (b : K⟦ℝ⟧).supportOrderType = 1 := by
      simpa using hbOne
    let : WellFoundedLT (b : K⟦ℝ⟧).support :=
      (b : K⟦ℝ⟧).isWF_support
    have htype : Ordinal.type
        (fun x y : (b : K⟦ℝ⟧).support ↦ x < y) = 1 := by
      rw [← HahnSeries.supportOrderType_eq_typeLT (x := (b : K⟦ℝ⟧))
        (OrderIso.refl (b : K⟦ℝ⟧).support)]
      exact hbTypeOne
    obtain ⟨hUnique⟩ := Ordinal.type_eq_one_iff_unique.mp htype
    let : Unique (b : K⟦ℝ⟧).support := hUnique
    let g : (b : K⟦ℝ⟧).support := default
    have hsupport : (b : K⟦ℝ⟧).support = {(g : ℝ)} := by
      ext x
      constructor
      · intro hx
        have heq : (⟨x, hx⟩ : (b : K⟦ℝ⟧).support) = g :=
          Subsingleton.elim _ _
        exact Set.mem_singleton_iff.mpr (congrArg Subtype.val heq)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact g.2
    have hbSingle : (b : K⟦ℝ⟧) =
        HahnSeries.single (g : ℝ) ((b : K⟦ℝ⟧).coeff g) := by
      ext x
      by_cases hx : x = (g : ℝ)
      · subst x
        simp
      · have hxSupport : x ∉ (b : K⟦ℝ⟧).support := by
          rw [hsupport]
          simpa using hx
        have hxCoeff : (b : K⟦ℝ⟧).coeff x = 0 := by
          rw [HahnSeries.mem_support] at hxSupport
          exact not_ne_iff.mp hxSupport
        simp [hx, hxCoeff]
    have hgNonpositive : (g : ℝ) ≤ 0 :=
      HahnSeries.Nonpositive.support_subset b g.2
    rcases hgNonpositive.eq_or_lt with hgZero | hgNegative
    · apply mem_nearConstantSubgroup_iff.mpr
      refine ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem,
        (b : K⟦ℝ⟧).coeff g, ?_⟩
      apply Subtype.ext
      simp only [zero_add, HahnSeries.Nonpositive.coe_C]
      calc
        HahnSeries.C ((b : K⟦ℝ⟧).coeff g) =
            HahnSeries.single 0 ((b : K⟦ℝ⟧).coeff g) := rfl
        _ = HahnSeries.single (g : ℝ) ((b : K⟦ℝ⟧).coeff g) := by
          rw [hgZero]
        _ = (b : K⟦ℝ⟧) := hbSingle.symm
    · apply negativeMonomialIdeal_le_nearConstantSubgroup
      have hgen := HahnSeries.Nonpositive.single_one_mem_negativeMonomialIdeal
        (K := K) hgNegative
      have hmul := Ideal.mul_mem_left
        (HahnSeries.Nonpositive.negativeMonomialIdeal K)
        (HahnSeries.Nonpositive.C ((b : K⟦ℝ⟧).coeff g)) hgen
      have hproduct : HahnSeries.Nonpositive.C ((b : K⟦ℝ⟧).coeff g) *
          HahnSeries.Nonpositive.single (g : ℝ) 1 hgNegative.le = b := by
        apply Subtype.ext
        simp only [Subring.coe_mul, HahnSeries.Nonpositive.coe_C,
          HahnSeries.Nonpositive.coe_single]
        change HahnSeries.single 0 ((b : K⟦ℝ⟧).coeff g) *
          HahnSeries.single (g : ℝ) 1 = (b : K⟦ℝ⟧)
        rw [HahnSeries.single_mul_single, zero_add, mul_one]
        exact hbSingle.symm
      rwa [hproduct] at hmul

/-- The zero fiber of the ordinal value is exactly the negative-monomial ideal. -/
theorem ordinalValue_eq_zero_iff {b : Series K} :
    ordinalValue b = 0 ↔
      b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  constructor
  · intro hvalue
    by_contra hbJ
    by_cases hbNear : b ∈ nearConstantSubgroup K
    · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
        hbNear hbJ] at hvalue
      exact one_ne_zero hvalue
    · obtain ⟨c, hcb, hcType⟩ :=
        ordinalValue_mem_representativeOrderTypes_of_not_mem_nearConstantSubgroup hbNear
      rw [hvalue] at hcType
      have hcTypeZero : (c : K⟦ℝ⟧).supportOrderType = 0 := by
        simpa using hcType
      have hc : c = 0 := by
        apply Subtype.ext
        exact HahnSeries.supportOrderType_eq_zero.mp hcTypeZero
      subst c
      exact hbNear (by simpa using hcb)
  · exact ordinalValue_of_mem_negativeMonomialIdeal

/-- The one fiber of the ordinal value is exactly `(J + K) \ J`. -/
theorem ordinalValue_eq_one_iff {b : Series K} :
    ordinalValue b = 1 ↔
      b ∈ nearConstantSubgroup K ∧
        b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  constructor
  · intro hvalue
    have hbJ : b ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
      intro hbJ
      rw [ordinalValue_of_mem_negativeMonomialIdeal hbJ] at hvalue
      exact zero_ne_one hvalue
    refine ⟨?_, hbJ⟩
    by_contra hbNear
    obtain ⟨c, hcb, hcType⟩ :=
      ordinalValue_mem_representativeOrderTypes_of_not_mem_nearConstantSubgroup hbNear
    rw [hvalue] at hcType
    have hcNear : c ∈ nearConstantSubgroup K :=
      mem_nearConstantSubgroup_of_supportOrderType_le_one hcType.le
    have hbNear' := (nearConstantSubgroup K).add_mem hcb hcNear
    apply hbNear
    have heq : (b - c) + c = b := by abel
    rwa [heq] at hbNear'
  · rintro ⟨hbNear, hbJ⟩
    exact ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
      hbNear hbJ

/-- The third branch consists exactly of the series outside `J + K`. -/
theorem one_lt_ordinalValue_iff {b : Series K} :
    1 < ordinalValue b ↔ b ∉ nearConstantSubgroup K := by
  constructor
  · intro hvalue hbNear
    by_cases hbJ : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
    · rw [ordinalValue_of_mem_negativeMonomialIdeal hbJ] at hvalue
      exact (not_lt_of_ge zero_le_one) hvalue
    · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
        hbNear hbJ] at hvalue
      exact (lt_irrefl 1) hvalue
  · intro hbNear
    apply lt_of_not_ge
    intro hle
    rcases Order.le_one_iff.mp hle with hzero | hone
    · apply hbNear
      exact negativeMonomialIdeal_le_nearConstantSubgroup
        (ordinalValue_eq_zero_iff.mp hzero)
    · exact hbNear (ordinalValue_eq_one_iff.mp hone).1

/-- A series with zero constant coefficient and support supremum zero lies in the third branch of
the ordinal value. -/
theorem one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
    {b : Series K} (hcoeff : HahnSeries.Nonpositive.constantCoeff b = 0)
    (hsup : HahnSeries.Nonpositive.supportSup b = 0) :
    1 < ordinalValue b := by
  apply one_lt_ordinalValue_iff.mpr
  intro hnear
  have hmem := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hnear
  have hbJ : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    simpa [hcoeff] using hmem
  exact
    (HahnSeries.Nonpositive.not_mem_negativeMonomialIdeal_of_supportSup_eq_zero hsup) hbJ

/-- The ordinal value is at most the ordinary order type of the support. -/
theorem ordinalValue_le_supportOrderType (b : Series K) :
    ordinalValue b ≤ NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType := by
  by_cases hbJ : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
  · rw [ordinalValue_of_mem_negativeMonomialIdeal hbJ]
    exact bot_le
  by_cases hbNear : b ∈ nearConstantSubgroup K
  · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
      hbNear hbJ, Order.one_le_iff_pos]
    apply bot_lt_iff_ne_bot.mpr
    intro htype
    have htypeZero : (b : K⟦ℝ⟧).supportOrderType = 0 := by
      simpa using htype
    have hbZero : b = 0 := by
      apply Subtype.ext
      exact HahnSeries.supportOrderType_eq_zero.mp htypeZero
    subst b
    exact hbJ (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem
  · rw [ordinalValue_of_not_mem_nearConstantSubgroup hbNear]
    apply csInf_le'
    exact ⟨b, by simp, rfl⟩

private theorem mem_negativeMonomialIdeal_iff_of_sub_mem
    {b c : Series K}
    (hbc : b - c ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K ↔
      c ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  let J := HahnSeries.Nonpositive.negativeMonomialIdeal K
  constructor
  · intro hb
    have hc : b - (b - c) ∈ J := J.sub_mem hb hbc
    have heq : b - (b - c) = c := by abel
    rwa [heq] at hc
  · intro hc
    have hb : (b - c) + c ∈ J := J.add_mem hbc hc
    have heq : (b - c) + c = b := by abel
    rwa [heq] at hb

private theorem mem_nearConstantSubgroup_iff_of_sub_mem_negativeMonomialIdeal
    {b c : Series K}
    (hbc : b - c ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    b ∈ nearConstantSubgroup K ↔ c ∈ nearConstantSubgroup K := by
  have hbcNear : b - c ∈ nearConstantSubgroup K :=
    negativeMonomialIdeal_le_nearConstantSubgroup hbc
  constructor
  · intro hb
    have hc := (nearConstantSubgroup K).sub_mem hb hbcNear
    have heq : b - (b - c) = c := by abel
    rwa [heq] at hc
  · intro hc
    have hb := (nearConstantSubgroup K).add_mem hbcNear hc
    have heq : (b - c) + c = b := by abel
    rwa [heq] at hb

private theorem representativeOrderTypes_eq_of_sub_mem_negativeMonomialIdeal
    {b c : Series K}
    (hbc : b - c ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    representativeOrderTypes b = representativeOrderTypes c := by
  have hbcNear : b - c ∈ nearConstantSubgroup K :=
    negativeMonomialIdeal_le_nearConstantSubgroup hbc
  have hcbNear : c - b ∈ nearConstantSubgroup K := by
    have hneg := (nearConstantSubgroup K).neg_mem hbcNear
    have heq : -(b - c) = c - b := by abel
    rwa [heq] at hneg
  ext o
  constructor
  · rintro ⟨d, hbd, hdType⟩
    refine ⟨d, ?_, hdType⟩
    have hsum := (nearConstantSubgroup K).add_mem hcbNear hbd
    have heq : (c - b) + (b - d) = c - d := by abel
    rwa [heq] at hsum
  · rintro ⟨d, hcd, hdType⟩
    refine ⟨d, ?_, hdType⟩
    have hsum := (nearConstantSubgroup K).add_mem hbcNear hcd
    have heq : (b - c) + (c - d) = b - d := by abel
    rwa [heq] at hsum

/-- The ordinal value depends only on the germ modulo the negative-monomial ideal. -/
theorem ordinalValue_eq_of_sub_mem_negativeMonomialIdeal {b c : Series K}
    (hbc : b - c ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    ordinalValue b = ordinalValue c := by
  have hbJ := mem_negativeMonomialIdeal_iff_of_sub_mem hbc
  have hbNear := mem_nearConstantSubgroup_iff_of_sub_mem_negativeMonomialIdeal hbc
  have htypes := representativeOrderTypes_eq_of_sub_mem_negativeMonomialIdeal hbc
  classical
  unfold ordinalValue
  rw [hbJ, hbNear, htypes]

/-- The ordinal value induced on Berarducci germs. -/
noncomputable def germOrdinalValue (q : Germ K) : NatOrdinal :=
  Quotient.liftOn' q ordinalValue fun _ _ h ↦
    ordinalValue_eq_of_sub_mem_negativeMonomialIdeal
      (Ideal.Quotient.eq.mp (Quot.sound h))

@[simp]
theorem germOrdinalValue_mk (b : Series K) :
    germOrdinalValue
      (Ideal.Quotient.mk (HahnSeries.Nonpositive.negativeMonomialIdeal K) b) =
        ordinalValue b :=
  (rfl)

/-- The induced ordinal value is zero exactly at the zero germ. -/
theorem germOrdinalValue_eq_zero_iff {q : Germ K} :
    germOrdinalValue q = 0 ↔ q = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [germOrdinalValue_mk, ordinalValue_eq_zero_iff]
  exact (Ideal.Quotient.eq_zero_iff_mem
    (I := HahnSeries.Nonpositive.negativeMonomialIdeal K) (a := b)).symm

end Berarducci
