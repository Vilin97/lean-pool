/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrderTypeMultiplicativity

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.CriticalPointExistence
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.MainLemma
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Irreducibility at multiplicatively principal support order types

Berarducci, Theorem 10.5 proves that a nonpositive real Hahn series with support order type `ω`
or `ω ^ (ω ^ β)` is irreducible, as is its sum with one, provided no strictly negative monomial
divides it.

The proof combines multiplicativity of the ordinal value with critical points. In a nontrivial
factorisation, multiplicative principality forces one factor to have ordinal value one. The two
critical points must sum to zero because every strictly negative translated truncation has smaller
ordinal value. But a nonunit of ordinal value one has a strictly negative critical point, giving a
contradiction.

## References

* A. Berarducci, *Factorization in generalized power series*, Trans. Amer. Math. Soc. 352
  (2000), 553–577, cited as [Ber00].
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries Ordinal

variable {K : Type v} [Field K]

private theorem not_mem_negativeMonomialIdeal_of_no_negativeMonomial_dvd
    {a : Series K}
    (ha : ∀ (gamma : ℝ) (hgamma : gamma < 0),
      ¬HahnSeries.Nonpositive.single gamma (1 : K) hgamma.le ∣ a) :
    a ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  intro haJ
  have hsup :=
    HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mp haJ
  by_cases haZero : a = 0
  · have hneg : (-1 : ℝ) < 0 := by norm_num
    apply ha (-1) hneg
    refine ⟨0, ?_⟩
    simp [haZero]
  · rw [HahnSeries.Nonpositive.supportSup_of_ne haZero] at hsup
    have hsupReal : sSup (a : K⟦ℝ⟧).support < 0 := WithBot.coe_lt_coe.mp hsup
    apply ha (sSup (a : K⟦ℝ⟧).support) hsupReal
    refine ⟨HahnSeries.Nonpositive.normalize a, ?_⟩
    apply Subtype.ext
    simpa only [Subring.coe_mul, HahnSeries.Nonpositive.coe_single,
      HahnSeries.single_one_mul_eq_translate] using
      (HahnSeries.Nonpositive.translate_csSup_normalize a).symm

private theorem ordinalValue_eq_one_of_isUnit {b : Series K} (hb : IsUnit b) :
    ordinalValue b = 1 := by
  have hbConstant := HahnSeries.Nonpositive.eq_C_constantCoeff_of_isUnit hb
  have hcoeff : HahnSeries.Nonpositive.constantCoeff b ≠ 0 := by
    intro hzero
    have hbZero : b = 0 := by simpa [hzero] using hbConstant
    exact hb.ne_zero hbZero
  rw [hbConstant, ordinalValue_C_of_ne hcoeff]

private theorem exists_negative_support_of_ordinalValue_eq_one_of_not_isUnit
    {b : Series K} (hbValue : ordinalValue b = 1) (hbUnit : ¬IsUnit b) :
    ∃ gamma ∈ (b : K⟦ℝ⟧).support, gamma < 0 := by
  have hbNear := (ordinalValue_eq_one_iff.mp hbValue).1
  have hbJ := (ordinalValue_eq_one_iff.mp hbValue).2
  have hbCoeff : HahnSeries.Nonpositive.constantCoeff b ≠ 0 := by
    intro hzero
    apply hbJ
    have hsub := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hbNear
    simpa [hzero] using hsub
  have hzeroSupport : (0 : ℝ) ∈ (b : K⟦ℝ⟧).support := by
    rw [HahnSeries.mem_support, ← HahnSeries.Nonpositive.constantCoeff_apply]
    exact hbCoeff
  by_contra hnegative
  have hsupport : (b : K⟦ℝ⟧).support = {0} := by
    apply Set.Subset.antisymm
    · intro gamma hgamma
      rw [Set.mem_singleton_iff]
      have hnonpositive := HahnSeries.Nonpositive.support_subset b hgamma
      exact le_antisymm hnonpositive (le_of_not_gt fun hgammaNeg ↦
        hnegative ⟨gamma, hgamma, hgammaNeg⟩)
    · exact Set.singleton_subset_iff.mpr hzeroSupport
  apply hbUnit
  have hbConstant : b = HahnSeries.Nonpositive.C
      (HahnSeries.Nonpositive.constantCoeff b) := by
    apply Subtype.ext
    apply HahnSeries.coeff_injective
    funext gamma
    by_cases hgamma : gamma = 0
    · subst gamma
      simp [HahnSeries.Nonpositive.constantCoeff_apply]
    · have hgammaSupport : gamma ∉ (b : K⟦ℝ⟧).support := by
        rw [hsupport]
        simpa using hgamma
      rw [HahnSeries.mem_support, not_ne_iff] at hgammaSupport
      simp [hgamma, hgammaSupport]
  rw [hbConstant]
  exact (isUnit_iff_ne_zero.mpr hbCoeff).map HahnSeries.Nonpositive.C

private theorem criticalPoint_lt_zero_of_ordinalValue_eq_one_of_not_isUnit
    {b : Series K} {x : ℝ} (hbValue : ordinalValue b = 1)
    (hbUnit : ¬IsUnit b) (hx : IsCriticalPoint b x) : x < 0 := by
  obtain ⟨gamma, hgammaSupport, hgamma⟩ :=
    exists_negative_support_of_ordinalValue_eq_one_of_not_isUnit hbValue hbUnit
  apply lt_of_le_of_ne hx.nonpositive
  intro hxZero
  have hxValue : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) = 1 := by
    rw [hxZero, translatedTruncation_zero, hbValue]
  have hgammaPos : 0 < ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma) :=
    ordinalValue_translatedTruncation_pos_of_mem_support hgammaSupport
  have hgammaValue : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma) = 1 := by
    apply le_antisymm
    · exact (hx.value_le gamma hgamma.le).trans_eq hxValue
    · exact Order.one_le_iff_pos.mpr hgammaPos
  have hxLeGamma := hx.le_of_value_eq gamma hgamma.le (hgammaValue.trans hxValue.symm)
  exact (not_le_of_gt hgamma) (hxZero ▸ hxLeGamma)

private theorem factor_ordinalValue_eq_one_of_mul_eq_infiniteMultiplicativelyPrincipal
    {b c rho : NatOrdinal}
    (hrho : Ordinal.IsInfiniteMultiplicativelyPrincipal rho.val)
    (hmul : b * c = rho) : b = 1 ∨ c = 1 := by
  have hrhoPos : 0 < rho := by
    rw [← NatOrdinal.val.lt_iff_lt]
    exact hrho.isSuccLimit.bot_lt
  have hbNe : b ≠ 0 := by
    intro hb
    rw [hb, zero_mul] at hmul
    exact hrhoPos.ne' hmul.symm
  have hcNe : c ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hmul
    exact hrhoPos.ne' hmul.symm
  by_cases hb : b = 1
  · exact Or.inl hb
  by_cases hc : c = 1
  · exact Or.inr hc
  exfalso
  have hbOne : 1 < b := lt_of_le_of_ne (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hbNe))
    (Ne.symm hb)
  have hcOne : 1 < c := lt_of_le_of_ne (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hcNe))
    (Ne.symm hc)
  have hbLt : b < rho := by
    rw [← hmul]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hcOne (pos_iff_ne_zero.mpr hbNe)
  have hcLt : c < rho := by
    rw [← hmul]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hbOne (pos_iff_ne_zero.mpr hcNe)
  have hlt := NatOrdinal.mul_lt_of_isMultiplicativelyPrincipal
    (Ordinal.isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal.mp
      hrho).2 hbLt hcLt
  rw [hmul] at hlt
  exact (lt_irrefl _) hlt

private theorem irreducible_of_infiniteMultiplicativelyPrincipal_ordinalValue
    [CharZero K] {a : Series K}
    (haPrincipal : Ordinal.IsInfiniteMultiplicativelyPrincipal (ordinalValue a).val)
    (haNegative : ∀ u : ℝ, u < 0 →
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ordinalValue a) :
    Irreducible a := by
  have haOne : 1 < ordinalValue a := by
    rw [← NatOrdinal.val.lt_iff_lt]
    exact (show (1 : Ordinal) < 2 by norm_num).trans
      (Ordinal.isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal.mp
        haPrincipal).1
  rw [irreducible_iff]
  refine ⟨fun haUnit ↦ haOne.ne' (ordinalValue_eq_one_of_isUnit haUnit), ?_⟩
  intro b c habc
  by_cases hbUnit : IsUnit b
  · exact Or.inl hbUnit
  by_cases hcUnit : IsUnit c
  · exact Or.inr hcUnit
  exfalso
  have hmul : ordinalValue b * ordinalValue c = ordinalValue a := by
    rw [← ordinalValue_mul, ← habc]
  have hfactor :=
    factor_ordinalValue_eq_one_of_mul_eq_infiniteMultiplicativelyPrincipal haPrincipal hmul
  have haNe : a ≠ 0 := by
    intro haZero
    rw [haZero, ordinalValue_zero] at haOne
    exact (not_lt_of_ge zero_le_one) haOne
  have hbNe : b ≠ 0 := by
    intro hbZero
    apply haNe
    rw [habc, hbZero, zero_mul]
  have hcNe : c ≠ 0 := by
    intro hcZero
    apply haNe
    rw [habc, hcZero, mul_zero]
  obtain ⟨x, hx⟩ := exists_isCriticalPoint hbNe
  obtain ⟨y, hy⟩ := exists_isCriticalPoint hcNe
  have hbLe : ordinalValue b ≤ ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) := by
    simpa using hx.value_le 0 le_rfl
  have hcLe : ordinalValue c ≤ ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) := by
    simpa using hy.value_le 0 le_rfl
  have hcriticalLower : ordinalValue a ≤
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) (x + y)) := by
    calc
      ordinalValue a = ordinalValue b * ordinalValue c := hmul.symm
      _ ≤ ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) *
          ordinalValue (translatedTruncation (c : K⟦ℝ⟧) y) :=
        mul_le_mul hbLe hcLe bot_le bot_le
      _ = ordinalValue (translatedTruncation (((b * c : Series K) : K⟦ℝ⟧)) (x + y)) :=
        (criticalPoint_product_value hx hy).symm
      _ = ordinalValue (translatedTruncation (a : K⟦ℝ⟧) (x + y)) := by rw [habc]
  have hsum : x + y = 0 := by
    apply le_antisymm (add_nonpos hx.nonpositive hy.nonpositive)
    apply le_of_not_gt
    intro hnegative
    exact (not_lt_of_ge hcriticalLower) (haNegative (x + y) hnegative)
  rcases hfactor with hbValue | hcValue
  · have hxNegative :=
      criticalPoint_lt_zero_of_ordinalValue_eq_one_of_not_isUnit hbValue hbUnit hx
    linarith [hy.nonpositive]
  · have hyNegative :=
      criticalPoint_lt_zero_of_ordinalValue_eq_one_of_not_isUnit hcValue hcUnit hy
    linarith [hx.nonpositive]

private theorem translatedTruncation_one_eq_zero_of_neg {u : ℝ} (hu : u < 0) :
    translatedTruncation (1 : K⟦ℝ⟧) u = 0 := by
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext delta
  rw [coeff_translatedTruncation]
  by_cases hdelta : delta ≤ 0
  · rw [ite_eq_left hdelta]
    have hsum : u + delta ≠ 0 := ne_of_lt (add_neg_of_neg_of_nonpos hu hdelta)
    simp [hsum]
  · rw [ite_eq_right hdelta]
    rfl

private theorem ordinalValue_add_one_eq_of_one_lt
    {a : Series K} (ha : 1 < ordinalValue a) : ordinalValue (a + 1) = ordinalValue a := by
  apply le_antisymm
  · simpa [ordinalValue_one, max_eq_left ha.le] using ordinalValue_add_le_max a 1
  · have h := ordinalValue_add_le_max (a + 1) (-1)
    have hsum : (a + 1) + (-1) = a := by ring
    rw [hsum, ordinalValue_neg, ordinalValue_one] at h
    exact (le_max_iff.mp h).resolve_right (not_le_of_gt ha)

private theorem ordinalValue_translatedTruncation_lt_of_supportOrderType_eq_ordinalValue
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

/-- Berarducci, Theorem 10.5: a nonpositive real Hahn series not divisible by a strictly
negative monomial is irreducible, as is its sum with one, when its support has order type `ω` or
`ω ^ (ω ^ beta)`. -/
theorem irreducible_and_add_one_of_supportOrderType
    [CharZero K] {a : Series K}
    (haMonomial : ∀ (gamma : ℝ) (hgamma : gamma < 0),
      ¬HahnSeries.Nonpositive.single gamma (1 : K) hgamma.le ∣ a)
    (haType : (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∨
      ∃ beta : Ordinal, (a : K⟦ℝ⟧).supportOrderType =
        Ordinal.omega0 ^ Ordinal.omega0 ^ beta) :
    Irreducible a ∧ Irreducible (a + 1) := by
  have haJ := not_mem_negativeMonomialIdeal_of_no_negativeMonomial_dvd haMonomial
  have haPrincipal : Ordinal.IsInfiniteMultiplicativelyPrincipal
      (a : K⟦ℝ⟧).supportOrderType := by
    rcases haType with haOmega | ⟨beta, haBeta⟩
    · rw [haOmega]
      simpa using Ordinal.isInfiniteMultiplicativelyPrincipal_omega0_opow_opow 0
    · rw [haBeta]
      exact Ordinal.isInfiniteMultiplicativelyPrincipal_omega0_opow_opow beta
  have haWeak : HahnSeries.IsWeaklyPrincipal (a : K⟦ℝ⟧) := by
    rw [HahnSeries.isWeaklyPrincipal_iff]
    exact haPrincipal.isAdditivelyPrincipal
  have haValue := supportOrderType_eq_ordinalValue_of_isWeaklyPrincipal haWeak haJ
  have haOrderPrincipal : Ordinal.IsInfiniteMultiplicativelyPrincipal (ordinalValue a).val := by
    rw [← haValue]
    exact haPrincipal
  have haOne : 1 < ordinalValue a := by
    rw [← NatOrdinal.val.lt_iff_lt]
    exact (show (1 : Ordinal) < 2 by norm_num).trans
      (Ordinal.isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal.mp
        haOrderPrincipal).1
  have haNegative : ∀ u : ℝ, u < 0 →
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ordinalValue a :=
    fun _ hu ↦ ordinalValue_translatedTruncation_lt_of_supportOrderType_eq_ordinalValue
      haValue (zero_lt_one.trans haOne).ne' hu
  refine ⟨irreducible_of_infiniteMultiplicativelyPrincipal_ordinalValue
    haOrderPrincipal haNegative, ?_⟩
  have haAddValue := ordinalValue_add_one_eq_of_one_lt haOne
  have haAddPrincipal :
      Ordinal.IsInfiniteMultiplicativelyPrincipal (ordinalValue (a + 1)).val := by
    rw [haAddValue]
    exact haOrderPrincipal
  apply irreducible_of_infiniteMultiplicativelyPrincipal_ordinalValue haAddPrincipal
  intro u hu
  have hgerm : translatedTruncation (((a + 1 : Series K) : K⟦ℝ⟧)) u =
      translatedTruncation (a : K⟦ℝ⟧) u := by
    rw [show (((a + 1 : Series K) : K⟦ℝ⟧)) = (a : K⟦ℝ⟧) + 1 from rfl,
      translatedTruncation_add, translatedTruncation_one_eq_zero_of_neg hu, add_zero]
  rw [hgerm, haAddValue]
  exact haNegative u hu

end Berarducci
