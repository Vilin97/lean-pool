/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
import Mathlib.Tactic.Abel

/-!
# Image of Berarducci's ordinal value

Berarducci, Remark 5.3 states that the ordinal value has image in the class of additive-principal
ordinals, where that class includes zero. Thus the value is either zero or
`Ordinal.IsAdditivelyPrincipal`; equivalently, its underlying ordinary ordinal satisfies
Mathlib's `Ordinal.IsPrincipal (\x y => x + y)`.

The proof here derives the assertion directly from the three-branch minimum in Definition 5.2. If
a minimal representative had support order type `a + d` with both summands strictly smaller, the
support-splitting theorem would write it as a lower series plus an upper series. When the upper
series lies in `J + K`, it can be removed. Otherwise it has a negative support exponent, so the
strictly lower series is bounded away from zero and lies in `J`; that lower series can instead be
removed. Either case gives a congruent representative with strictly smaller support order type,
contradicting minimality.

The argument requires no characteristic-zero hypothesis and is therefore proved over an arbitrary
field. It supplies the additive-principality input for Berarducci's principal and residual value
definition.
-/

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

private theorem exists_negative_support_of_not_mem_nearConstantSubgroup
    {b : Series K} (hb : b ∉ nearConstantSubgroup K) :
    ∃ x ∈ (b : K⟦ℝ⟧).support, x < 0 := by
  by_contra hnegative
  apply hb
  rw [mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem]
  have heq : b - HahnSeries.Nonpositive.C
      (HahnSeries.Nonpositive.constantCoeff b) = 0 := by
    apply Subtype.ext
    ext x
    by_cases hx : x = 0
    · subst x
      simp
    · have hxSupport : x ∉ (b : K⟦ℝ⟧).support := by
        intro hxb
        have hxle := HahnSeries.Nonpositive.support_subset b hxb
        have hxge : 0 ≤ x := le_of_not_gt fun hxlt ↦
          hnegative ⟨x, hxb, hxlt⟩
        exact hx (le_antisymm hxle hxge)
      have hxCoeff : (b : K⟦ℝ⟧).coeff x = 0 := by
        rwa [← not_ne_iff, ← HahnSeries.mem_support]
      simp [hx, hxCoeff]
  rw [heq]
  exact (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem

private theorem mem_negativeMonomialIdeal_of_supportBelow_of_negative_support
    {b c : Series K}
    (hbc : HahnSeries.SupportBelow (b : K⟦ℝ⟧) (c : K⟦ℝ⟧))
    {x : ℝ} (hxc : x ∈ (c : K⟦ℝ⟧).support) (hx : x < 0) :
    b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero]
  by_cases hb : b = 0
  · subst b
    simp
  · rw [HahnSeries.Nonpositive.supportSup_of_ne hb]
    apply WithBot.coe_lt_coe.mpr
    have hb' : (b : K⟦ℝ⟧) ≠ 0 := by simpa using hb
    apply (csSup_le (HahnSeries.support_nonempty_iff.mpr hb') ?_).trans_lt hx
    intro y hy
    exact (hbc.lt hy hxc).le

private theorem sub_mem_nearConstantSubgroup_left_of_add_eq
    {b c y z : Series K}
    (hbc : b - c ∈ nearConstantSubgroup K)
    (hc : c = y + z)
    (hz : z ∈ nearConstantSubgroup K) :
    b - y ∈ nearConstantSubgroup K := by
  have hsum := (nearConstantSubgroup K).add_mem hbc hz
  have heq : (b - c) + z = b - y := by
    rw [hc]
    abel
  rwa [heq] at hsum

private theorem sub_mem_nearConstantSubgroup_right_of_add_eq
    {b c y z : Series K}
    (hbc : b - c ∈ nearConstantSubgroup K)
    (hc : c = y + z)
    (hy : y ∈ nearConstantSubgroup K) :
    b - z ∈ nearConstantSubgroup K := by
  have hsum := (nearConstantSubgroup K).add_mem hbc hy
  have heq : (b - c) + y = b - z := by
    rw [hc]
    abel
  rwa [heq] at hsum

/-- Every Berarducci ordinal value strictly above one is positive additive principal. This is the
nontrivial branch of Berarducci, Remark 5.3. -/
theorem ordinalValue_isAdditivelyPrincipal_of_one_lt {b : Series K}
    (hb : 1 < ordinalValue b) :
    Ordinal.IsAdditivelyPrincipal (ordinalValue b).val := by
  have hbNear : b ∉ nearConstantSubgroup K := one_lt_ordinalValue_iff.mp hb
  have hleast := ordinalValue_isLeast_representativeOrderTypes hbNear
  obtain ⟨c, hbc, hcType⟩ := mem_representativeOrderTypes_iff.mp hleast.1
  have hcTypeVal : (c : K⟦ℝ⟧).supportOrderType = (ordinalValue b).val := by
    have h := congrArg NatOrdinal.val hcType
    simpa using h
  have hvalueNe : (ordinalValue b).val ≠ 0 := by
    intro hzero
    have : ordinalValue b = 0 := by
      apply NatOrdinal.val.injective
      simpa using hzero
    rw [this] at hb
    exact not_lt_of_ge zero_le_one hb
  rw [Ordinal.isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add]
  refine ⟨hvalueNe, ?_⟩
  by_contra hprincipal
  obtain ⟨a, ha, d, hd, hadd⟩ :=
    Ordinal.exists_lt_add_of_not_isPrincipal_add hprincipal
  have hcSplit : (c : K⟦ℝ⟧).supportOrderType = a + d := by
    rw [hcTypeVal, hadd]
  obtain ⟨y, z, hyz, hya, hzd, hcyz⟩ :=
    (HahnSeries.supportOrderType_eq_add_iff (c : K⟦ℝ⟧) a d).mp hcSplit
  have hySupport : y.support ⊆ (c : K⟦ℝ⟧).support := by
    rw [hcyz, HahnSeries.support_add_eq_union_of_supportBelow y z hyz]
    exact Set.subset_union_left
  have hzSupport : z.support ⊆ (c : K⟦ℝ⟧).support := by
    rw [hcyz, HahnSeries.support_add_eq_union_of_supportBelow y z hyz]
    exact Set.subset_union_right
  let y' : Series K := ⟨y,
    (HahnSeries.mem_nonpositiveSubring (x := y)).mpr fun _ hx ↦
      HahnSeries.Nonpositive.support_subset c (hySupport hx)⟩
  let z' : Series K := ⟨z,
    (HahnSeries.mem_nonpositiveSubring (x := z)).mpr fun _ hx ↦
      HahnSeries.Nonpositive.support_subset c (hzSupport hx)⟩
  have hyz' : HahnSeries.SupportBelow (y' : K⟦ℝ⟧) (z' : K⟦ℝ⟧) := hyz
  have hcyz' : c = y' + z' := by
    apply Subtype.ext
    exact hcyz
  by_cases hzNear : z' ∈ nearConstantSubgroup K
  · have hby := sub_mem_nearConstantSubgroup_left_of_add_eq hbc hcyz' hzNear
    have hyCandidate : NatOrdinal.of y.supportOrderType ∈
        representativeOrderTypes b :=
      mem_representativeOrderTypes_iff.mpr ⟨y', hby, rfl⟩
    have hle := hleast.2 hyCandidate
    have hlt : NatOrdinal.of y.supportOrderType < ordinalValue b := by
      rw [hya, ← hcType]
      exact NatOrdinal.of.lt_iff_lt.mpr (ha.trans_eq hcTypeVal.symm)
    exact not_lt_of_ge hle hlt
  · obtain ⟨x, hxz, hx⟩ :=
      exists_negative_support_of_not_mem_nearConstantSubgroup hzNear
    have hyJ :=
      mem_negativeMonomialIdeal_of_supportBelow_of_negative_support hyz' hxz hx
    have hyNear : y' ∈ nearConstantSubgroup K :=
      negativeMonomialIdeal_le_nearConstantSubgroup hyJ
    have hbz := sub_mem_nearConstantSubgroup_right_of_add_eq hbc hcyz' hyNear
    have hzCandidate : NatOrdinal.of z.supportOrderType ∈
        representativeOrderTypes b :=
      mem_representativeOrderTypes_iff.mpr ⟨z', hbz, rfl⟩
    have hle := hleast.2 hzCandidate
    have hlt : NatOrdinal.of z.supportOrderType < ordinalValue b := by
      rw [hzd, ← hcType]
      exact NatOrdinal.of.lt_iff_lt.mpr (hd.trans_eq hcTypeVal.symm)
    exact not_lt_of_ge hle hlt

/-- A Berarducci ordinal value is either zero or positive additive principal. This is the
positive formulation of Berarducci, Remark 5.3. -/
theorem ordinalValue_eq_zero_or_isAdditivelyPrincipal (b : Series K) :
    ordinalValue b = 0 ∨
      Ordinal.IsAdditivelyPrincipal (ordinalValue b).val := by
  by_cases hzero : ordinalValue b = 0
  · exact Or.inl hzero
  · right
    have hpos : 0 < ordinalValue b := bot_lt_iff_ne_bot.mpr hzero
    have hone : 1 ≤ ordinalValue b := Order.one_le_iff_pos.mpr hpos
    rcases hone.eq_or_lt with hone | hone
    · have hval : (ordinalValue b).val = 1 := by
        rw [← hone]
        simp
      rw [hval]
      simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 0
    · exact ordinalValue_isAdditivelyPrincipal_of_one_lt hone

/-- The underlying ordinary ordinal of every Berarducci value belongs to Berarducci's class
`H`, represented exactly by Mathlib's additive-principal predicate that includes zero. -/
theorem ordinalValue_isPrincipal_add (b : Series K) :
    Ordinal.IsPrincipal (· + ·) (ordinalValue b).val := by
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal b with hzero | hprincipal
  · have hval : (ordinalValue b).val = 0 := by rw [hzero]; simp
    rw [hval]
    exact Ordinal.isPrincipal_zero
  · exact
      (Ordinal.isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp hprincipal).2

/-- The ordinal value induced on the germ quotient also has image in Berarducci's class `H`. -/
theorem germOrdinalValue_isPrincipal_add (q : Germ K) :
    Ordinal.IsPrincipal (· + ·) (germOrdinalValue q).val := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [germOrdinalValue_mk]
  exact ordinalValue_isPrincipal_add b

end Berarducci
