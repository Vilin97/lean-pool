/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueConstantMul

/-!
# Submultiplicativity of Berarducci's ordinal value

Berarducci, Lemma 5.5(2): the ordinal value of a product is at most the Hessenberg product of the
two ordinal values. The product on the right is Hessenberg multiplication, carried by
`NatOrdinal`; it dominates ordinary ordinal multiplication and the two must not be interchanged.
This is the inequality half of Berarducci, Theorem 9.7; the opposite inequality is the deep part
of the paper and is not proved here.

The proof follows the source. Choosing representatives `b'`, `c'` modulo `J + K` whose support
order types realize `v_J(b)` and `v_J(c)`, and writing `b - b' = j + r`, `c - c' = i + s` with
`j, i ∈ J` and `r, s` constant, expansion gives

`b c ≡ b' c' + s b' + r c'   (mod J + K)`.

The max-form additive inequality of Berarducci, Lemma 5.5(1) then reduces the claim to the
order-type bound for `b' c'` together with constant-factor invariance for the two cross terms.

The ideal cases `b ∈ J` and `c ∈ J` come first: the right-hand side is then zero, and the bounds
`v_J(b) ≤ v_J(b) ⊙ v_J(c)` and `v_J(c) ≤ v_J(b) ⊙ v_J(c)` used afterwards are unavailable.

For the leading Cantor exponent, the bound reads `ordinalValueDegree (b c) ≤ ordinalValueDegree b
+ ordinalValueDegree c`, since the Cantor degree of a Hessenberg product is the Hessenberg sum of
the Cantor degrees. This is the product inequality of the max-additive degree
`ordinalValueDegreeValuation`.
-/

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

private theorem ordinalValue_C_mul_le (k : K) (b : Series K) :
    ordinalValue (HahnSeries.Nonpositive.C k * b) ≤ ordinalValue b := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [map_zero, zero_mul, ordinalValue_zero]
    exact bot_le
  · exact (ordinalValue_C_mul hk b).le

private theorem ordinalValue_le_one_of_mem_nearConstantSubgroup {b : Series K}
    (hb : b ∈ nearConstantSubgroup K) : ordinalValue b ≤ 1 :=
  le_of_not_gt fun h ↦ (one_lt_ordinalValue_iff.mp h) hb

/-- Berarducci, Lemma 5.5(2): the ordinal value of a product is at most the Hessenberg product of
the ordinal values of the factors. -/
theorem ordinalValue_mul_le_naturalMul (b c : Series K) :
    ordinalValue (b * c) ≤ ordinalValue b * ordinalValue c := by
  by_cases hbJ : b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
  · rw [ordinalValue_of_mem_negativeMonomialIdeal
      ((HahnSeries.Nonpositive.negativeMonomialIdeal K).mul_mem_right c hbJ)]
    exact bot_le
  by_cases hcJ : c ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
  · rw [ordinalValue_of_mem_negativeMonomialIdeal
      ((HahnSeries.Nonpositive.negativeMonomialIdeal K).mul_mem_left b hcJ)]
    exact bot_le
  have hb1 : 1 ≤ ordinalValue b :=
    Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h ↦ hbJ (ordinalValue_eq_zero_iff.mp h))
  have hc1 : 1 ≤ ordinalValue c :=
    Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h ↦ hcJ (ordinalValue_eq_zero_iff.mp h))
  have hbmul : ordinalValue b ≤ ordinalValue b * ordinalValue c :=
    le_mul_of_one_le_right zero_le hc1
  have hcmul : ordinalValue c ≤ ordinalValue b * ordinalValue c :=
    le_mul_of_one_le_left zero_le hb1
  obtain ⟨b', hbb', hb'⟩ :=
    mem_representativeOrderTypes_iff.mp (ordinalValue_mem_representativeOrderTypes b)
  obtain ⟨c', hcc', hc'⟩ :=
    mem_representativeOrderTypes_iff.mp (ordinalValue_mem_representativeOrderTypes c)
  obtain ⟨j, hj, r, hjr⟩ := mem_nearConstantSubgroup_iff.mp hbb'
  obtain ⟨i, hi, s, his⟩ := mem_nearConstantSubgroup_iff.mp hcc'
  have hb : b = b' + (j + HahnSeries.Nonpositive.C r) := by rw [hjr]; ring
  have hc : c = c' + (i + HahnSeries.Nonpositive.C s) := by rw [his]; ring
  set d : Series K :=
    b' * c' + (HahnSeries.Nonpositive.C s * b' + HahnSeries.Nonpositive.C r * c') with hdDef
  have hkey : b * c - d =
      (b' * i + j * c' + j * i + j * HahnSeries.Nonpositive.C s +
        HahnSeries.Nonpositive.C r * i) + HahnSeries.Nonpositive.C (r * s) := by
    rw [hdDef, map_mul, hb, hc]; ring
  have hrest : b * c - d ∈ nearConstantSubgroup K := by
    rw [hkey]
    refine mem_nearConstantSubgroup_iff.mpr ⟨_, ?_, r * s, rfl⟩
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ b' hi) (Ideal.mul_mem_right c' _ hj))
      (Ideal.mul_mem_right i _ hj)) (Ideal.mul_mem_right _ _ hj))
      (Ideal.mul_mem_left _ _ hi)
  have hdle : ordinalValue d ≤ ordinalValue b * ordinalValue c := by
    refine (ordinalValue_add_le_max _ _).trans (max_le ?_ ((ordinalValue_add_le_max _ _).trans
      (max_le ?_ ?_)))
    · calc ordinalValue (b' * c')
          ≤ NatOrdinal.of ((b' * c' : Series K) : K⟦ℝ⟧).supportOrderType :=
            ordinalValue_le_supportOrderType _
        _ ≤ NatOrdinal.of ((NatOrdinal.of (b' : K⟦ℝ⟧).supportOrderType *
              NatOrdinal.of (c' : K⟦ℝ⟧).supportOrderType).val) := by
            apply NatOrdinal.of.monotone
            rw [Subring.coe_mul]
            exact HahnSeries.supportOrderType_mul_le_naturalMul _ _
        _ = ordinalValue b * ordinalValue c := by rw [NatOrdinal.of_val, hb', hc']
    · exact ((ordinalValue_C_mul_le s b').trans
        ((ordinalValue_le_supportOrderType b').trans_eq hb')).trans hbmul
    · exact ((ordinalValue_C_mul_le r c').trans
        ((ordinalValue_le_supportOrderType c').trans_eq hc')).trans hcmul
  have hsplit : b * c = d + (b * c - d) := by ring
  calc ordinalValue (b * c) = ordinalValue (d + (b * c - d)) := by rw [← hsplit]
    _ ≤ max (ordinalValue d) (ordinalValue (b * c - d)) := ordinalValue_add_le_max _ _
    _ ≤ ordinalValue b * ordinalValue c :=
        max_le hdle ((ordinalValue_le_one_of_mem_nearConstantSubgroup hrest).trans
          (hb1.trans hbmul))

/-- Berarducci, Lemma 5.5(2) for the leading Cantor exponent: the exponent of a product is at
most the Hessenberg sum of the exponents. -/
theorem ordinalValueDegree_mul_le_add (b c : Series K) :
    ordinalValueDegree (b * c) ≤ ordinalValueDegree b + ordinalValueDegree c := by
  rw [ordinalValueDegree_eq_cantorDegree, ordinalValueDegree_eq_cantorDegree,
    ordinalValueDegree_eq_cantorDegree, ← NatOrdinal.cantorDegree_mul,
    NatOrdinal.cantorDegree_eq_ordinalCantorDegree, NatOrdinal.cantorDegree_eq_ordinalCantorDegree]
  exact Ordinal.cantorDegree_mono (NatOrdinal.val.monotone (ordinalValue_mul_le_naturalMul b c))

/-- Berarducci's germ ordinal value is submultiplicative under Hessenberg multiplication. -/
theorem germOrdinalValue_mul_le_naturalMul (q p : Germ K) :
    germOrdinalValue (q * p) ≤ germOrdinalValue q * germOrdinalValue p := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective p
  rw [← map_mul, germOrdinalValue_mk, germOrdinalValue_mk, germOrdinalValue_mk]
  exact ordinalValue_mul_le_naturalMul b c

end Berarducci
