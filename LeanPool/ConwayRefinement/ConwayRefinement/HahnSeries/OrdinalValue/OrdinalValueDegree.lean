/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueConstantMul

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import Mathlib.Tactic.Abel

/-!
# The exponent of Berarducci's ordinal value

The value `Berarducci.ordinalValueDegree b` is the leading Cantor exponent of Berarducci's order
value `v_J(b)`, with bottom value on the ideal `J`. LM24 does not introduce separate notation for
this exponent-valued transform; it supplies the ordinal-value properties from which the
construction is derived.

The additive part is proved from the intrinsic minimum defining `ordinalValue`. First, minimal
representatives give a Hessenberg-sum bound. The fact that every nonzero ordinal value is a power
of `ω` sharpens this to the max-form inequality in LM24, Fact 2.7.1(1), and gives the max-form
inequality for `ordinalValueDegree`.

The ordinal value is invariant under multiplication by a nonzero constant, hence under negation,
and its kernel is exactly `J`. The weak and strict cuts `ordinalValueDegree b ≤ α` and
`ordinalValueDegree b < α` are identified with the intrinsic cuts `v_J(b) < ω^(α+1)` and
`v_J(b) < ω^α`.

Everything here is valid over any field. Multiplicativity of the ordinal value is kept as the
explicit proposition `OrdinalValueMultiplicative K`, with its consequence for the exponent; it is
Berarducci, Theorem 9.7, proved with its characteristic-zero hypothesis in
`ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue`. The exponent is
bundled as the max-additive degree `ordinalValueDegreeValuation` in
`ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueValuation`, from the
submultiplicative bound of Berarducci, Lemma 5.5 alone.
-/

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

@[simp]
theorem ordinalValue_zero : ordinalValue (0 : Series K) = 0 :=
  ordinalValue_of_mem_negativeMonomialIdeal
    (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem

/-- A nonzero constant series has ordinal value one. -/
theorem ordinalValue_C_of_ne {k : K} (hk : k ≠ 0) :
    ordinalValue (HahnSeries.Nonpositive.C k : Series K) = 1 := by
  apply ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
  · apply mem_nearConstantSubgroup_iff.mpr
    exact ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem, k, by simp⟩
  · intro hmem
    have hcoeff := constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
    exact hk (by simpa using hcoeff)

/-- The ordinal value is invariant under negation: `-b = C (-1) * b`, and a nonzero constant
factor does not change the ordinal value. -/
@[simp]
theorem ordinalValue_neg (b : Series K) : ordinalValue (-b) = ordinalValue b := by
  have hnegOne : (-1 : Series K) = HahnSeries.Nonpositive.C (-1 : K) := by simp
  rw [← neg_one_mul b, hnegOne, ordinalValue_C_mul (neg_ne_zero.mpr one_ne_zero)]

private theorem representativeOrderTypes_eq_of_sub_mem_nearConstantSubgroup
    {b c : Series K} (hbc : b - c ∈ nearConstantSubgroup K) :
    representativeOrderTypes b = representativeOrderTypes c := by
  have hcb : c - b ∈ nearConstantSubgroup K := by
    have hneg := (nearConstantSubgroup K).neg_mem hbc
    have heq : -(b - c) = c - b := by abel
    rwa [heq] at hneg
  ext o
  constructor
  · intro ho
    obtain ⟨d, hbd, hd⟩ := mem_representativeOrderTypes_iff.mp ho
    apply mem_representativeOrderTypes_iff.mpr
    refine ⟨d, ?_, hd⟩
    have hsum := (nearConstantSubgroup K).add_mem hcb hbd
    have heq : (c - b) + (b - d) = c - d := by abel
    rwa [heq] at hsum
  · intro ho
    obtain ⟨d, hcd, hd⟩ := mem_representativeOrderTypes_iff.mp ho
    apply mem_representativeOrderTypes_iff.mpr
    refine ⟨d, ?_, hd⟩
    have hsum := (nearConstantSubgroup K).add_mem hbc hcd
    have heq : (b - c) + (c - d) = b - d := by abel
    rwa [heq] at hsum

private theorem ordinalValue_eq_of_sub_mem_nearConstantSubgroup
    {b c : Series K} (hb : b ∉ nearConstantSubgroup K)
    (hc : c ∉ nearConstantSubgroup K)
    (hbc : b - c ∈ nearConstantSubgroup K) :
    ordinalValue b = ordinalValue c := by
  rw [ordinalValue_of_not_mem_nearConstantSubgroup hb,
    ordinalValue_of_not_mem_nearConstantSubgroup hc,
    representativeOrderTypes_eq_of_sub_mem_nearConstantSubgroup hbc]

/-- The ordinal value of a sum is bounded by the Hessenberg sum of the two ordinal values. -/
theorem ordinalValue_add_le_naturalAdd (b c : Series K) :
    ordinalValue (b + c) ≤ ordinalValue b + ordinalValue c := by
  by_cases hsumNear : b + c ∈ nearConstantSubgroup K
  · by_cases hsumJ : b + c ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
    · rw [ordinalValue_of_mem_negativeMonomialIdeal hsumJ]
      exact bot_le
    · rw [ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
        hsumNear hsumJ]
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      intro hzero
      have hbZero : ordinalValue b = 0 :=
        (NatOrdinal.add_eq_zero_iff.mp hzero).1
      have hcZero : ordinalValue c = 0 :=
        (NatOrdinal.add_eq_zero_iff.mp hzero).2
      have hbJ := ordinalValue_eq_zero_iff.mp hbZero
      have hcJ := ordinalValue_eq_zero_iff.mp hcZero
      exact hsumJ ((HahnSeries.Nonpositive.negativeMonomialIdeal K).add_mem hbJ hcJ)
  · by_cases hbNear : b ∈ nearConstantSubgroup K
    · have hcNear : c ∉ nearConstantSubgroup K := by
        intro hcNear
        exact hsumNear ((nearConstantSubgroup K).add_mem hbNear hcNear)
      have hdiff : (b + c) - c ∈ nearConstantSubgroup K := by
        simpa only [add_sub_cancel_right] using hbNear
      rw [ordinalValue_eq_of_sub_mem_nearConstantSubgroup hsumNear hcNear hdiff]
      exact NatOrdinal.le_add_left
    · by_cases hcNear : c ∈ nearConstantSubgroup K
      · have hdiff : (b + c) - b ∈ nearConstantSubgroup K := by
          have heq : (b + c) - b = c := by abel
          rwa [heq]
        rw [ordinalValue_eq_of_sub_mem_nearConstantSubgroup hsumNear hbNear hdiff]
        exact NatOrdinal.le_add_right
      · obtain ⟨b', hbb', hb'Type⟩ :=
          mem_representativeOrderTypes_iff.mp
            (ordinalValue_mem_representativeOrderTypes b)
        obtain ⟨c', hcc', hc'Type⟩ :=
          mem_representativeOrderTypes_iff.mp
            (ordinalValue_mem_representativeOrderTypes c)
        have hcandidate :
            NatOrdinal.of (((b' + c' : Series K) : K⟦ℝ⟧).supportOrderType) ∈
              representativeOrderTypes (b + c) := by
          apply mem_representativeOrderTypes_iff.mpr
          refine ⟨b' + c', ?_, rfl⟩
          have hsum := (nearConstantSubgroup K).add_mem hbb' hcc'
          have heq : (b + c) - (b' + c') = (b - b') + (c - c') := by abel
          rwa [heq]
        calc
          ordinalValue (b + c) ≤
              NatOrdinal.of (((b' + c' : Series K) : K⟦ℝ⟧).supportOrderType) :=
            (ordinalValue_isLeast_representativeOrderTypes hsumNear).2 hcandidate
          _ ≤ NatOrdinal.of ((NatOrdinal.of (b' : K⟦ℝ⟧).supportOrderType +
              NatOrdinal.of (c' : K⟦ℝ⟧).supportOrderType).val) :=
            NatOrdinal.of.monotone
              (HahnSeries.supportOrderType_add_le_naturalAdd
                (b' : K⟦ℝ⟧) (c' : K⟦ℝ⟧))
          _ = ordinalValue b + ordinalValue c := by
            rw [NatOrdinal.of_val, hb'Type, hc'Type]

/-- The leading Cantor exponent of Berarducci's ordinal value, with bottom on `J`. -/
def ordinalValueDegree (b : Series K) : WithBot NatOrdinal :=
  NatOrdinal.cantorDegree (ordinalValue b)

@[simp]
theorem ordinalValueDegree_eq_bot_iff {b : Series K} :
    ordinalValueDegree b = ⊥ ↔
      b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  rw [ordinalValueDegree, NatOrdinal.cantorDegree_eq_bot, ordinalValue_eq_zero_iff]

@[simp]
theorem ordinalValueDegree_zero : ordinalValueDegree (0 : Series K) = ⊥ := by
  rw [ordinalValueDegree_eq_bot_iff]
  exact (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem

@[simp]
theorem ordinalValueDegree_one : ordinalValueDegree (1 : Series K) = 0 := by
  rw [ordinalValueDegree, ordinalValue_one]
  simpa using NatOrdinal.cantorDegree_wpow (0 : NatOrdinal)

/-- A nonzero constant series has ordinal-value degree zero. -/
theorem ordinalValueDegree_C_of_ne {k : K} (hk : k ≠ 0) :
    ordinalValueDegree (HahnSeries.Nonpositive.C k : Series K) = 0 := by
  rw [ordinalValueDegree, ordinalValue_C_of_ne hk]
  simpa using NatOrdinal.cantorDegree_wpow (0 : NatOrdinal)

/-- The exponent-valued ordinal value is the leading Cantor exponent of the ordinal value. -/
theorem ordinalValueDegree_eq_cantorDegree (b : Series K) :
    ordinalValueDegree b = NatOrdinal.cantorDegree (ordinalValue b) :=
  (rfl)

/-- A nonzero constant factor does not change the exponent-valued ordinal value. -/
theorem ordinalValueDegree_C_mul {k : K} (hk : k ≠ 0) (b : Series K) :
    ordinalValueDegree (HahnSeries.Nonpositive.C k * b) = ordinalValueDegree b := by
  rw [ordinalValueDegree, ordinalValueDegree, ordinalValue_C_mul hk]

/-- The exponent-valued ordinal value is invariant under negation. -/
@[simp]
theorem ordinalValueDegree_neg (b : Series K) : ordinalValueDegree (-b) = ordinalValueDegree b := by
  rw [ordinalValueDegree, ordinalValueDegree, ordinalValue_neg]

/-- Weak degree filtration in terms of the corresponding ordinal-value cut. -/
theorem ordinalValueDegree_le_coe_iff (b : Series K) (α : NatOrdinal) :
    ordinalValueDegree b ≤ (α : WithBot NatOrdinal) ↔ ordinalValue b < ω^ (α + 1) :=
  NatOrdinal.cantorDegree_le_coe_iff _ _

/-- Strict degree filtration in terms of the corresponding ordinal-value cut. -/
theorem ordinalValueDegree_lt_coe_iff (b : Series K) (α : NatOrdinal) :
    ordinalValueDegree b < (α : WithBot NatOrdinal) ↔ ordinalValue b < ω^ α :=
  NatOrdinal.cantorDegree_lt_coe_iff _ _

/-- The exponent-valued ordinal value satisfies the max-form additive inequality. -/
theorem ordinalValueDegree_add_le_max (b c : Series K) :
    ordinalValueDegree (b + c) ≤ max (ordinalValueDegree b) (ordinalValueDegree c) := by
  change NatOrdinal.cantorDegree (ordinalValue (b + c)) ≤
    max (NatOrdinal.cantorDegree (ordinalValue b))
      (NatOrdinal.cantorDegree (ordinalValue c))
  calc
    NatOrdinal.cantorDegree (ordinalValue (b + c)) ≤
        NatOrdinal.cantorDegree (ordinalValue b + ordinalValue c) :=
      by
        rw [NatOrdinal.cantorDegree_eq_ordinalCantorDegree,
          NatOrdinal.cantorDegree_eq_ordinalCantorDegree]
        exact Ordinal.cantorDegree_mono
          (NatOrdinal.val.monotone (ordinalValue_add_le_naturalAdd b c))
    _ = max (ordinalValueDegree b) (ordinalValueDegree c) :=
      NatOrdinal.cantorDegree_add _ _

private theorem exists_ordinalValueDegree_eq_and_ordinalValue_eq_wpow
    {b : Series K} (hb : ordinalValue b ≠ 0) :
    ∃ α : NatOrdinal,
      ordinalValueDegree b = (α : WithBot NatOrdinal) ∧ ordinalValue b = ω^ α := by
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal b with hzero | hprincipal
  · exact (hb hzero).elim
  obtain ⟨α, hα⟩ := Ordinal.isAdditivelyPrincipal_iff.mp hprincipal
  let a : NatOrdinal := NatOrdinal.of α
  have hvalue : ordinalValue b = ω^ a := by
    apply NatOrdinal.val.injective
    simpa only [a, NatOrdinal.val_wpow, NatOrdinal.val_of] using hα
  refine ⟨a, ?_, hvalue⟩
  rw [ordinalValueDegree, hvalue, NatOrdinal.cantorDegree_wpow]

/-- An ordinal value has degree `α` exactly when it is the pure power `ω^α`. -/
theorem ordinalValueDegree_eq_coe_iff (b : Series K) (α : NatOrdinal) :
    ordinalValueDegree b = (α : WithBot NatOrdinal) ↔ ordinalValue b = ω^ α := by
  constructor
  · intro hdegree
    have hvalueNe : ordinalValue b ≠ 0 := by
      intro hzero
      have hbot : ordinalValueDegree b = ⊥ := by
        rw [ordinalValueDegree, hzero, NatOrdinal.cantorDegree_zero]
      exact WithBot.bot_ne_coe (hbot.symm.trans hdegree)
    obtain ⟨d, hdDegree, hdValue⟩ :=
      exists_ordinalValueDegree_eq_and_ordinalValue_eq_wpow hvalueNe
    have hdα : d = α := WithBot.coe_eq_coe.mp (hdDegree.symm.trans hdegree)
    rwa [hdα] at hdValue
  · intro hvalue
    rw [ordinalValueDegree, hvalue, NatOrdinal.cantorDegree_wpow]

/-- Berarducci's ordinal-value degree never exceeds the Hahn-series degree. -/
theorem ordinalValueDegree_le_degree (b : Series K) :
    ordinalValueDegree b ≤ (b : K⟦ℝ⟧).degree := by
  rw [ordinalValueDegree, NatOrdinal.cantorDegree_eq_ordinalCantorDegree,
    HahnSeries.degree_eq_cantorDegree]
  apply Ordinal.cantorDegree_mono
  simpa using NatOrdinal.val.monotone (ordinalValue_le_supportOrderType b)

/-- Berarducci's ordinal value satisfies the max-form inequality in LM24, Fact 2.7.1(1). -/
theorem ordinalValue_add_le_max (b c : Series K) :
    ordinalValue (b + c) ≤ max (ordinalValue b) (ordinalValue c) := by
  by_cases hsumZero : ordinalValue (b + c) = 0
  · rw [hsumZero]
    exact bot_le
  by_cases hbZero : ordinalValue b = 0
  · calc
      ordinalValue (b + c) ≤ ordinalValue b + ordinalValue c :=
        ordinalValue_add_le_naturalAdd b c
      _ = ordinalValue c := by rw [hbZero, zero_add]
      _ ≤ max (ordinalValue b) (ordinalValue c) := le_max_right _ _
  by_cases hcZero : ordinalValue c = 0
  · calc
      ordinalValue (b + c) ≤ ordinalValue b + ordinalValue c :=
        ordinalValue_add_le_naturalAdd b c
      _ = ordinalValue b := by rw [hcZero, add_zero]
      _ ≤ max (ordinalValue b) (ordinalValue c) := le_max_left _ _
  obtain ⟨s, hsDegree, hsValue⟩ :=
    exists_ordinalValueDegree_eq_and_ordinalValue_eq_wpow hsumZero
  obtain ⟨a, haDegree, haValue⟩ :=
    exists_ordinalValueDegree_eq_and_ordinalValue_eq_wpow hbZero
  obtain ⟨d, hdDegree, hdValue⟩ :=
    exists_ordinalValueDegree_eq_and_ordinalValue_eq_wpow hcZero
  have hdegree := ordinalValueDegree_add_le_max b c
  rw [hsDegree, haDegree, hdDegree, ← WithBot.coe_max, WithBot.coe_le_coe] at hdegree
  rw [hsValue, haValue, hdValue]
  rcases le_total a d with had | hda
  · rw [max_eq_right (NatOrdinal.wpow_le_wpow.mpr had)]
    exact NatOrdinal.wpow_le_wpow.mpr (hdegree.trans_eq (max_eq_right had))
  · rw [max_eq_left (NatOrdinal.wpow_le_wpow.mpr hda)]
    exact NatOrdinal.wpow_le_wpow.mpr (hdegree.trans_eq (max_eq_left hda))

/-- Multiplicativity of Berarducci's ordinal value, isolated from its definitions. -/
def OrdinalValueMultiplicative (K : Type v) [Field K] : Prop :=
  ∀ b c : Series K, ordinalValue (b * c) = ordinalValue b * ordinalValue c

/-- Establish Berarducci ordinal-value multiplicativity from the two-series identity. -/
theorem OrdinalValueMultiplicative.of_forall
    (h : ∀ b c : Series K, ordinalValue (b * c) = ordinalValue b * ordinalValue c) :
    OrdinalValueMultiplicative K := h

/-- Apply Berarducci ordinal-value multiplicativity to two series. -/
theorem OrdinalValueMultiplicative.ordinalValue_mul
    (hmul : OrdinalValueMultiplicative K) (b c : Series K) :
    ordinalValue (b * c) = ordinalValue b * ordinalValue c :=
  hmul b c

/-- Multiplicativity of the exponent-valued ordinal value, assuming the single Berarducci product
theorem. -/
theorem OrdinalValueMultiplicative.ordinalValueDegree_mul
    (hmul : OrdinalValueMultiplicative K) (b c : Series K) :
    ordinalValueDegree (b * c) = ordinalValueDegree b + ordinalValueDegree c := by
  simpa only [ordinalValueDegree, hmul b c] using
    NatOrdinal.cantorDegree_mul (ordinalValue b) (ordinalValue c)

end Berarducci
