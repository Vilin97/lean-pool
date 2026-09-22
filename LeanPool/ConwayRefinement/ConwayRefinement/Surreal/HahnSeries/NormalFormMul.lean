/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
/-
Continues and modifies the Apache-2.0-licensed Conway normal-form work in CombinatorialGames PR
#263: https://github.com/vihdzp/combinatorial-games/pull/263
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormAdd

import all LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# Multiplicative compatibility of the surreal Conway normal form

This module develops the multiplication-option comparison needed to prove that the Conway
normal-form equivalence preserves multiplication. The central cofinality lemmas show that every
coefficient truncation on either side of a Hahn product is separated from the product by a Conway
multiplication option formed from coefficient truncations of its factors.

The two elementary Hahn-series interface lemmas at the start expose multiplication facts that are
currently hidden behind the opaque `SurrealHahnSeries` field instance in CombinatorialGames.
-/

universe u

open IGame Order Set

public noncomputable section

namespace SurrealHahnSeries

private theorem ofLex_coe_mul (x y : SurrealHahnSeries) :
    ofLex (x * y).1 = ofLex x.1 * ofLex y.1 := by
  with_unfolding_all rfl

private theorem ofLex_coe_single (p : Surreal) (r : ℝ) :
    ofLex (single p r).1 = HahnSeries.single (OrderDual.toDual p) r := by
  apply HahnSeries.ext
  funext k
  rw [HahnSeries.coeff_single]
  unfold single mk
  by_cases hk : k = OrderDual.toDual p
  · subst k
    simp
  · have hk' : k.ofDual ≠ p := fun h ↦ hk (by simpa using congrArg OrderDual.toDual h)
    simp [hk, hk']

private theorem mem_support_ofLex_coe_iff (x : SurrealHahnSeries) (k : Surreal) :
    OrderDual.toDual k ∈ (ofLex x.1).support ↔ k ∈ x.support := by
  rfl

private theorem ofLex_coe_zero : ofLex (0 : SurrealHahnSeries).1 = 0 := by
  with_unfolding_all rfl

private theorem ofLex_coe_ne_zero {x : SurrealHahnSeries} (hx : x ≠ 0) :
    ofLex x.1 ≠ 0 := by
  intro hzero
  apply hx
  apply Subtype.ext
  rw [← ofLex_inj, hzero, ofLex_coe_zero]

private theorem ofLex_coe_order_eq_exp_zero {x : SurrealHahnSeries} (hx : x ≠ 0) :
    (ofLex x.1).order = OrderDual.toDual (x.exp ⟨0, by
      change 0 < x.length
      rw [pos_iff_ne_zero, ne_eq, length_eq_zero]
      exact hx⟩).1 := by
  have hlength : 0 < x.length := by
    rw [pos_iff_ne_zero, ne_eq, length_eq_zero]
    exact hx
  have hxRaw : ofLex x.1 ≠ 0 := ofLex_coe_ne_zero hx
  apply WithTop.coe_inj.mp
  rw [HahnSeries.order_eq_orderTop_of_ne_zero hxRaw]
  apply HahnSeries.orderTop_eq_of_le
  · rw [mem_support_ofLex_coe_iff]
    exact (x.exp ⟨0, hlength⟩).2
  · intro k hk
    have hk' : k.ofDual ∈ x.support := by
      simpa using (mem_support_ofLex_coe_iff x k.ofDual).1 (by simpa using hk)
    let j := x.exp.symm ⟨k.ofDual, hk'⟩
    have hj : (⟨0, hlength⟩ : Iio x.length) ≤ j := by
      change (0 : Ordinal) ≤ j.1
      exact bot_le
    have hexp : x.exp j ≤ x.exp ⟨0, hlength⟩ := x.exp_anti hj
    change k.ofDual ≤ (x.exp ⟨0, hlength⟩).1
    change (x.exp j).1 ≤ (x.exp ⟨0, hlength⟩).1 at hexp
    dsimp [j] at hexp
    simpa only [x.exp.apply_symm_apply] using hexp

private theorem ofLex_coe_leadingCoeff_eq_coeffIdx_zero {x : SurrealHahnSeries}
    (hx : x ≠ 0) :
    (ofLex x.1).leadingCoeff = x.coeffIdx 0 := by
  rw [HahnSeries.leadingCoeff_eq, ofLex_coe_order_eq_exp_zero hx,
    x.coeffIdx_of_lt (by
      rw [pos_iff_ne_zero, ne_eq, length_eq_zero]
      exact hx)]
  rfl

/-- Lexicographic comparison of surreal Hahn series, stated directly in terms of their public
coefficient function. -/
theorem lt_iff_exists_coeff {x y : SurrealHahnSeries} :
    x < y ↔ ∃ i : Surreal, (∀ j, i < j → x.coeff j = y.coeff j) ∧
      x.coeff i < y.coeff i := by
  rfl

/-- The multiplicative unit is the singleton surreal Hahn series at exponent zero. -/
theorem one_eq_single_zero : (1 : SurrealHahnSeries) = single 0 1 := by
  apply Subtype.ext
  rw [← ofLex_inj, ofLex_coe_single]
  with_unfolding_all rfl

/-- An integer cast is the constant singleton surreal Hahn series. -/
theorem intCast_eq_single_zero (n : ℤ) :
    (n : SurrealHahnSeries) = single 0 (n : ℝ) := by
  apply Subtype.ext
  rw [← ofLex_inj, ofLex_coe_single]
  with_unfolding_all rfl

/-- Conway normal forms preserve multiplication by an integer on the left. -/
theorem _root_.Surreal.toHahnSeries_intCast_mul (n : ℤ) (x : Surreal) :
    ((n : Surreal) * x).toHahnSeries =
      SurrealHahnSeries.single 0 (n : ℝ) * x.toHahnSeries := by
  have hsource : (n : Surreal) * x = n • x := by
    rw [← Int.cast_smul_eq_zsmul Surreal]
    rfl
  have htarget : SurrealHahnSeries.single 0 (n : ℝ) * x.toHahnSeries =
      n • x.toHahnSeries := by
    rw [← SurrealHahnSeries.intCast_eq_single_zero,
      ← Int.cast_smul_eq_zsmul SurrealHahnSeries]
    rfl
  rw [hsource, htarget]
  calc
    (n • x).toHahnSeries =
        Surreal.toHahnSeriesOrderAddMonoidIso (n • x) :=
      (Surreal.toHahnSeriesOrderAddMonoidIso_apply _).symm
    _ = n • Surreal.toHahnSeriesOrderAddMonoidIso x :=
      map_zsmul Surreal.toHahnSeriesOrderAddMonoidIso.toAddEquiv n x
    _ = n • x.toHahnSeries := by
      rw [Surreal.toHahnSeriesOrderAddMonoidIso_apply]

/-- Conway normal forms preserve multiplication by an integer on the right. -/
theorem _root_.Surreal.toHahnSeries_mul_intCast (x : Surreal) (n : ℤ) :
    (x * (n : Surreal)).toHahnSeries =
      x.toHahnSeries * SurrealHahnSeries.single 0 (n : ℝ) := by
  rw [mul_comm x, Surreal.toHahnSeries_intCast_mul, mul_comm]

/-- The surreal value map commutes with rational scalar multiplication. -/
theorem toSurreal_rat_smul (q : ℚ) (x : SurrealHahnSeries.{u}) :
    (q • x).toSurreal = q • x.toSurreal := by
  rw [← Surreal.toHahnSeriesOrderAddMonoidIso_symm_apply (q • x),
    ← Surreal.toHahnSeriesOrderAddMonoidIso_symm_apply x]
  exact map_rat_smul Surreal.toHahnSeriesOrderAddMonoidIso.symm.toAddMonoidHom q x

/-- A rational cast is the constant singleton surreal Hahn series. -/
theorem ratCast_eq_single_zero (q : ℚ) :
    (q : SurrealHahnSeries.{u}) = single 0 (q : ℝ) := by
  calc
    (q : SurrealHahnSeries.{u}) = q • (1 : SurrealHahnSeries) := by simp
    _ = q • (1 : Surreal).toHahnSeries := by
      exact congrArg (fun z : SurrealHahnSeries ↦ q • z) <|
        one_eq_single_zero.trans Surreal.toHahnSeries_one.symm
    _ = (q • (1 : Surreal)).toHahnSeries := by
      rw [← Surreal.toHahnSeriesOrderAddMonoidIso_apply,
        ← Surreal.toHahnSeriesOrderAddMonoidIso_apply]
      exact (map_rat_smul
        Surreal.toHahnSeriesOrderAddMonoidIso.toAddMonoidHom q 1).symm
    _ = (q : Surreal).toHahnSeries := by simp
    _ = single 0 (q : ℝ) := Surreal.toHahnSeries_ratCast q

/-- Conway normal forms preserve multiplication by a rational constant on the left. -/
theorem toSurreal_single_zero_ratCast_mul (q : ℚ) (x : SurrealHahnSeries.{u}) :
    (single 0 (q : ℝ) * x).toSurreal = (q : Surreal) * x.toSurreal := by
  rw [← ratCast_eq_single_zero, ← Rat.smul_def, toSurreal_rat_smul]
  simp [Rat.smul_def]

/-- The product of two singleton surreal Hahn series is the singleton at the sum exponent. -/
theorem single_mul_single (p q : Surreal.{u}) (r s : ℝ) :
    single p r * single q s = single (p + q) (r * s) := by
  apply Subtype.ext
  rw [← ofLex_inj, ofLex_coe_mul, ofLex_coe_single, ofLex_coe_single,
    HahnSeries.single_mul_single, ofLex_coe_single]
  congr 2

/-- Multiplication by a singleton shifts exponents and scales coefficients. -/
theorem coeff_single_mul (p : Surreal.{u}) (r : ℝ)
    (y : SurrealHahnSeries.{u}) (k : Surreal) :
    (single p r * y).coeff k = r * y.coeff (k - p) := by
  have h := congrArg (fun z : HahnSeries Surrealᵒᵈ ℝ ↦
    z.coeff (OrderDual.toDual k)) (ofLex_coe_mul (single p r) y)
  rw [ofLex_coe_single, HahnSeries.coeff_single_mul] at h
  exact h

/-- Truncation commutes with multiplication by a singleton after translating the cutoff. -/
theorem trunc_single_mul (p q : Surreal.{u}) (r : ℝ)
    (y : SurrealHahnSeries.{u}) :
    (single p r * y).trunc (p + q) = single p r * y.trunc q := by
  ext k
  obtain hk | hk := le_or_gt k (p + q)
  · rw [coeff_trunc_of_le hk, coeff_single_mul]
    rw [coeff_trunc_of_le (sub_le_iff_le_add'.2 (by simpa [add_comm] using hk))]
    simp
  · rw [coeff_trunc_of_lt hk, coeff_single_mul]
    rw [coeff_single_mul, coeff_trunc_of_lt]
    exact lt_sub_iff_add_lt.mpr (by simpa [add_comm] using hk)

/-- A coefficient perturbation of a series becomes the corresponding translated perturbation
after multiplication by a nonzero singleton. -/
theorem single_mul_trunc_add_single_div (p q : Surreal.{u}) (r s : ℝ)
    (y : SurrealHahnSeries.{u}) (hr : r ≠ 0) :
    single p r * (y.trunc q + single q (s / r)) =
      (single p r * y).trunc (p + q) + single (p + q) s := by
  rw [mul_add, trunc_single_mul, single_mul_single, mul_div_cancel₀ s hr]

/-- The leading indexed term of a formal product is the product of the leading indexed terms. -/
theorem term_zero_mul (x y : SurrealHahnSeries) :
    (x * y).term 0 = x.term 0 * y.term 0 := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [zero_mul, term_of_le (by simp), zero_mul]
  obtain rfl | hy := eq_or_ne y 0
  · rw [mul_zero, term_of_le (by simp), mul_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hxLength : 0 < x.length := by
    rw [pos_iff_ne_zero, ne_eq, length_eq_zero]
    exact hx
  have hyLength : 0 < y.length := by
    rw [pos_iff_ne_zero, ne_eq, length_eq_zero]
    exact hy
  have hxyLength : 0 < (x * y).length := by
    rw [pos_iff_ne_zero, ne_eq, length_eq_zero]
    exact hxy
  have hxRaw : ofLex x.1 ≠ 0 := ofLex_coe_ne_zero hx
  have hyRaw : ofLex y.1 ≠ 0 := ofLex_coe_ne_zero hy
  have hleadingNe :
      (ofLex x.1).leadingCoeff * (ofLex y.1).leadingCoeff ≠ 0 := by
    exact mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hxRaw)
      (HahnSeries.leadingCoeff_ne_zero.mpr hyRaw)
  have hexp := HahnSeries.order_mul_of_ne_zero hleadingNe
  rw [← ofLex_coe_mul, ofLex_coe_order_eq_exp_zero hxy,
    ofLex_coe_order_eq_exp_zero hx, ofLex_coe_order_eq_exp_zero hy] at hexp
  have hexp' :
      ((x * y).exp ⟨0, hxyLength⟩).1 =
        (x.exp ⟨0, hxLength⟩).1 + (y.exp ⟨0, hyLength⟩).1 := by
    simpa using congrArg OrderDual.ofDual hexp
  have hcoeff := HahnSeries.leadingCoeff_mul_of_ne_zero hleadingNe
  rw [← ofLex_coe_mul, ofLex_coe_leadingCoeff_eq_coeffIdx_zero hxy,
    ofLex_coe_leadingCoeff_eq_coeffIdx_zero hx,
    ofLex_coe_leadingCoeff_eq_coeffIdx_zero hy] at hcoeff
  rw [term_of_lt hxyLength, term_of_lt hxLength, term_of_lt hyLength,
    hcoeff, hexp', Real.toSurreal_mul, Surreal.wpow_add]
  ring

/-- The leading term of the surreal represented by a series is its zeroth indexed term. -/
theorem leadingTerm_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.leadingTerm = x.term 0 := by
  have h := leadingTerm_sub_truncIdx (x := x) (i := 0)
  have hzeroSeries : x.truncIdx 0 = 0 := by
    rw [← length_eq_zero, length_truncIdx]
    simp
  have hzero : (x.truncIdx 0).toSurreal = 0 := by
    calc
      (x.truncIdx 0).toSurreal = (0 : SurrealHahnSeries).toSurreal :=
        congrArg toSurreal hzeroSeries
      _ = 0 := toSurreal_zero
  rw [hzero, sub_zero] at h
  exact h

/-- Formal Hahn multiplication and Conway multiplication have the same leading term. -/
theorem leadingTerm_toSurreal_mul (x y : SurrealHahnSeries) :
    (x * y).toSurreal.leadingTerm = (x.toSurreal * y.toSurreal).leadingTerm := by
  rw [leadingTerm_toSurreal, term_zero_mul, ← leadingTerm_toSurreal,
    ← leadingTerm_toSurreal, Surreal.leadingTerm_mul]

/-- Every exponent in the support of a product is a sum of exponents from the two factors. -/
theorem exists_add_eq_of_mem_support_mul {x y : SurrealHahnSeries.{u}} {k : Surreal}
    (hk : k ∈ (x * y).support) :
    ∃ p ∈ x.support, ∃ q ∈ y.support, p + q = k := by
  have hk' : OrderDual.toDual k ∈ (ofLex (x * y).1).support :=
    (mem_support_ofLex_coe_iff (x * y) k).2 hk
  rw [ofLex_coe_mul] at hk'
  obtain ⟨p, hp, q, hq, hpq⟩ := HahnSeries.support_mul_subset hk'
  refine ⟨p.ofDual, (mem_support_ofLex_coe_iff x p.ofDual).1 ?_,
    q.ofDual, (mem_support_ofLex_coe_iff y q.ofDual).1 ?_, ?_⟩
  · simpa using hp
  · simpa using hq
  · simpa using congrArg OrderDual.ofDual hpq

/-- Every left truncation option of a singleton product is the singleton times a truncation
option of the other factor; multiplication by a negative coefficient reverses the side. -/
theorem exists_eq_single_mul_of_mem_truncLT
    {p : Surreal.{u}} {r : ℝ} {y t : SurrealHahnSeries.{u}}
    (ht : t ∈ truncLT (single p r * y)) :
    (0 < r ∧ ∃ b ∈ truncLT y, single p r * b = t) ∨
      (r < 0 ∧ ∃ b ∈ truncGT y, single p r * b = t) := by
  rw [truncLT_def] at ht
  obtain ⟨k, hk, s, hs, rfl⟩ := ht
  obtain ⟨p', hp', q, hq, hpq⟩ := exists_add_eq_of_mem_support_mul hk
  have hp : p' = p := support_single_subset hp'
  subst p'
  subst k
  have hr : r ≠ 0 := by
    intro hr
    subst r
    simp at hp'
  have hcoeff : (single p r * y).coeff (p + q) = r * y.coeff q := by
    rw [coeff_single_mul]
    congr 1
    abel_nf
  rw [hcoeff] at hs
  obtain hrNeg | hrPos := lt_or_gt_of_ne hr
  · right
    refine ⟨hrNeg, y.trunc q + single q (s / r), ?_, ?_⟩
    · exact trunc_add_single_truncGT hq <|
        (lt_div_iff_of_neg hrNeg).2 (by simpa [mul_comm] using hs)
    · exact single_mul_trunc_add_single_div p q r s y hr
  · left
    refine ⟨hrPos, y.trunc q + single q (s / r), ?_, ?_⟩
    · exact trunc_add_single_truncLT hq <|
        (div_lt_iff₀ hrPos).2 (by simpa [mul_comm] using hs)
    · exact single_mul_trunc_add_single_div p q r s y hr

/-- Every right truncation option of a singleton product is the singleton times a truncation
option of the other factor; multiplication by a negative coefficient reverses the side. -/
theorem exists_eq_single_mul_of_mem_truncGT
    {p : Surreal.{u}} {r : ℝ} {y t : SurrealHahnSeries.{u}}
    (ht : t ∈ truncGT (single p r * y)) :
    (0 < r ∧ ∃ b ∈ truncGT y, single p r * b = t) ∨
      (r < 0 ∧ ∃ b ∈ truncLT y, single p r * b = t) := by
  rw [truncGT_def] at ht
  obtain ⟨k, hk, s, hs, rfl⟩ := ht
  obtain ⟨p', hp', q, hq, hpq⟩ := exists_add_eq_of_mem_support_mul hk
  have hp : p' = p := support_single_subset hp'
  subst p'
  subst k
  have hr : r ≠ 0 := by
    intro hr
    subst r
    simp at hp'
  have hcoeff : (single p r * y).coeff (p + q) = r * y.coeff q := by
    rw [coeff_single_mul]
    congr 1
    abel_nf
  rw [hcoeff] at hs
  obtain hrNeg | hrPos := lt_or_gt_of_ne hr
  · right
    refine ⟨hrNeg, y.trunc q + single q (s / r), ?_, ?_⟩
    · exact trunc_add_single_truncLT hq <|
        (div_lt_iff_of_neg hrNeg).2 (by simpa [mul_comm] using hs)
    · exact single_mul_trunc_add_single_div p q r s y hr
  · left
    refine ⟨hrPos, y.trunc q + single q (s / r), ?_, ?_⟩
    · exact trunc_add_single_truncGT hq <|
        (lt_div_iff₀ hrPos).2 (by simpa [mul_comm] using hs)
    · exact single_mul_trunc_add_single_div p q r s y hr

/-- A product of surreal Hahn series supported at nonnegative exponents is again supported at
nonnegative exponents. -/
theorem support_mul_subset_Ici {x y : SurrealHahnSeries}
    (hx : x.support ⊆ Ici 0) (hy : y.support ⊆ Ici 0) :
    (x * y).support ⊆ Ici 0 := by
  intro k hk
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_add_eq_of_mem_support_mul hk
  have hpNonneg : 0 ≤ p := by simpa only [mem_Ici] using hx hp
  have hqNonneg : 0 ≤ q := by simpa only [mem_Ici] using hy hq
  simpa only [mem_Ici] using add_nonneg hpNonneg hqNonneg

private theorem coeff_mul_zero_of_support_subsets {x y : SurrealHahnSeries}
    (hx : x.support ⊆ Ioi 0) (hy : y.support ⊆ Ici 0) :
    (x * y).coeff 0 = 0 := by
  apply notMem_support_iff.mp
  intro hzero
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_add_eq_of_mem_support_mul hzero
  have hpPos : 0 < p := by simpa only [mem_Ioi] using hx hp
  have hqNonneg : 0 ≤ q := by simpa only [mem_Ici] using hy hq
  nlinarith

/-- At exponent zero, multiplication of nonnegative-support surreal Hahn series is multiplication
of their constant coefficients. -/
theorem coeff_zero_mul_of_support_subset_Ici {x y : SurrealHahnSeries}
    (hx : x.support ⊆ Ici 0) (hy : y.support ⊆ Ici 0) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  have hxSplit : x.trunc 0 + single 0 (x.coeff 0) = x :=
    trunc_add_single fun i hi ↦ hx hi
  have hySplit : y.trunc 0 + single 0 (y.coeff 0) = y :=
    trunc_add_single fun i hi ↦ hy hi
  conv_lhs => rw [← hxSplit, ← hySplit]
  rw [add_mul, mul_add, mul_add,
    coeff_add_apply, coeff_add_apply, coeff_add_apply]
  have hxTrunc : (x.trunc 0).support ⊆ Ioi 0 := by
    intro i hi
    rw [support_trunc] at hi
    exact hi.2
  have hyTrunc : (y.trunc 0).support ⊆ Ioi 0 := by
    intro i hi
    rw [support_trunc] at hi
    exact hi.2
  have hxTruncNonneg : (x.trunc 0).support ⊆ Ici 0 := fun i hi ↦ by
    rw [mem_Ici]
    exact (show 0 < i by simpa only [mem_Ioi] using hxTrunc hi).le
  have hyTruncNonneg : (y.trunc 0).support ⊆ Ici 0 := fun i hi ↦ by
    rw [mem_Ici]
    exact (show 0 < i by simpa only [mem_Ioi] using hyTrunc hi).le
  have hsingleNonneg (r : ℝ) : (single 0 r).support ⊆ Ici 0 := by
    intro i hi
    have hi' := support_single_subset hi
    simp only [mem_singleton_iff] at hi'
    subst i
    exact le_refl (0 : Surreal)
  rw [coeff_mul_zero_of_support_subsets hxTrunc hyTruncNonneg,
    coeff_mul_zero_of_support_subsets hxTrunc (hsingleNonneg _)]
  have hsingleTrunc : (single 0 (x.coeff 0) * y.trunc 0).coeff 0 = 0 := by
    rw [mul_comm]
    exact coeff_mul_zero_of_support_subsets hyTrunc (hsingleNonneg _)
  rw [hsingleTrunc, single_mul_single]
  simp [coeff_single_self]

/-- The ring expression occurring in a Conway multiplication option. -/
def mulOptionValue (x y a b : SurrealHahnSeries) : SurrealHahnSeries :=
  a * y + x * b - a * b

/-- Evaluation of the Hahn-series expression attached to a Conway multiplication option. -/
theorem mulOptionValue_eq (x y a b : SurrealHahnSeries) :
    mulOptionValue x y a b = a * y + x * b - a * b :=
  (rfl)

/-- Two left approximations give a multiplication option strictly below the product. -/
theorem mulOptionValue_lt_mul_of_lt_of_lt {x y a b : SurrealHahnSeries}
    (ha : a < x) (hb : b < y) : mulOptionValue x y a b < x * y := by
  dsimp [mulOptionValue]
  nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]

/-- Two right approximations give a multiplication option strictly below the product. -/
theorem mulOptionValue_lt_mul_of_gt_of_gt {x y a b : SurrealHahnSeries}
    (ha : x < a) (hb : y < b) : mulOptionValue x y a b < x * y := by
  dsimp [mulOptionValue]
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr ha) (sub_neg.mpr hb)]

/-- A left and a right approximation give a multiplication option strictly above the product. -/
theorem mul_lt_mulOptionValue_of_lt_of_gt {x y a b : SurrealHahnSeries}
    (ha : a < x) (hb : y < b) : x * y < mulOptionValue x y a b := by
  dsimp [mulOptionValue]
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ha) (sub_neg.mpr hb)]

/-- A right and a left approximation give a multiplication option strictly above the product. -/
theorem mul_lt_mulOptionValue_of_gt_of_lt {x y a b : SurrealHahnSeries}
    (ha : x < a) (hb : b < y) : x * y < mulOptionValue x y a b := by
  dsimp [mulOptionValue]
  nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr ha) (sub_pos.mpr hb)]

private theorem sub_leftApprox_pos (x : SurrealHahnSeries) (p : Surreal) (d : ℝ)
    (hd : 0 < d) :
    0 < x - (x.trunc p + single p (x.coeff p - d)) := by
  rw [lt_iff_exists_coeff]
  refine ⟨p, ?_, ?_⟩
  · intro j hpj
    rw [coeff_zero, coeff_sub_apply, coeff_add_apply, coeff_trunc_of_lt hpj,
      coeff_single_of_ne hpj.ne]
    simp
  · rw [coeff_zero, coeff_sub_apply, coeff_add_apply, coeff_trunc_of_le le_rfl,
      coeff_single_self]
    simp only [Pi.zero_apply]
    linarith

private theorem sub_leftApprox_lt_single (x : SurrealHahnSeries) (p : Surreal)
    (d C : ℝ) (hdC : d < C) :
    x - (x.trunc p + single p (x.coeff p - d)) < single p C := by
  rw [lt_iff_exists_coeff]
  refine ⟨p, ?_, ?_⟩
  · intro j hpj
    rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_lt hpj,
      coeff_single_of_ne hpj.ne, coeff_single_of_ne hpj.ne]
    simp
  · rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_le le_rfl,
      coeff_single_self, coeff_single_self]
    linarith

private theorem rightApprox_sub_pos (x : SurrealHahnSeries) (p : Surreal) (d : ℝ)
    (hd : 0 < d) :
    0 < (x.trunc p + single p (x.coeff p + d)) - x := by
  rw [lt_iff_exists_coeff]
  refine ⟨p, ?_, ?_⟩
  · intro j hpj
    rw [coeff_zero, coeff_sub_apply, coeff_add_apply, coeff_trunc_of_lt hpj,
      coeff_single_of_ne hpj.ne]
    simp
  · rw [coeff_zero, coeff_sub_apply, coeff_add_apply, coeff_trunc_of_le le_rfl,
      coeff_single_self]
    simp only [Pi.zero_apply]
    linarith

private theorem rightApprox_sub_lt_single (x : SurrealHahnSeries) (p : Surreal)
    (d C : ℝ) (hdC : d < C) :
    (x.trunc p + single p (x.coeff p + d)) - x < single p C := by
  rw [lt_iff_exists_coeff]
  refine ⟨p, ?_, ?_⟩
  · intro j hpj
    rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_lt hpj,
      coeff_single_of_ne hpj.ne, coeff_single_of_ne hpj.ne]
    simp
  · rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_le le_rfl,
      coeff_single_self, coeff_single_self]
    linarith

private theorem exists_small_square {d : ℝ} (hd : 0 < d) :
    ∃ e : ℝ, 0 < e ∧ 4 * e ^ 2 < d := by
  let e := min 1 (d / 8)
  have he1 : e ≤ 1 := min_le_left _ _
  have hed : e ≤ d / 8 := min_le_right _ _
  have he : 0 < e := lt_min zero_lt_one (by linarith)
  refine ⟨e, he, ?_⟩
  nlinarith [sq_nonneg e]

private theorem single_lt_sub_leftApprox (x : SurrealHahnSeries) (k : Surreal)
    (r C : ℝ) (hC : C < x.coeff k - r) :
    single k C < x - (x.trunc k + single k r) := by
  rw [lt_iff_exists_coeff]
  refine ⟨k, ?_, ?_⟩
  · intro j hkj
    rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_lt hkj,
      coeff_single_of_ne hkj.ne, coeff_single_of_ne hkj.ne]
    simp
  · rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_le le_rfl,
      coeff_single_self, coeff_single_self]
    linarith

private theorem single_lt_rightApprox_sub (x : SurrealHahnSeries) (k : Surreal)
    (r C : ℝ) (hC : C < r - x.coeff k) :
    single k C < (x.trunc k + single k r) - x := by
  rw [lt_iff_exists_coeff]
  refine ⟨k, ?_, ?_⟩
  · intro j hkj
    rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_lt hkj,
      coeff_single_of_ne hkj.ne, coeff_single_of_ne hkj.ne]
    simp
  · rw [coeff_sub_apply, coeff_add_apply, coeff_trunc_of_le le_rfl,
      coeff_single_self, coeff_single_self]
    linarith

/-- Every left coefficient truncation of a product is strictly dominated by a same-side
multiplication option, which is itself strictly below the product. -/
theorem exists_mulOptionValue_between_of_mem_truncLT
    {x y t : SurrealHahnSeries} (ht : t ∈ truncLT (x * y)) :
    ∃ a ∈ truncLT x, ∃ b ∈ truncLT y,
      t < mulOptionValue x y a b ∧ mulOptionValue x y a b < x * y := by
  rw [truncLT_def] at ht
  obtain ⟨k, hk, r, hr, rfl⟩ := ht
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_add_eq_of_mem_support_mul hk
  obtain ⟨e, he, heSmall⟩ := exists_small_square (sub_pos.mpr hr)
  let a := x.trunc p + single p (x.coeff p - e)
  let b := y.trunc q + single q (y.coeff q - e)
  have ha : a ∈ truncLT x := by
    apply trunc_add_single_truncLT hp
    linarith
  have hb : b ∈ truncLT y := by
    apply trunc_add_single_truncLT hq
    linarith
  have hxaPos : 0 < x - a := sub_leftApprox_pos x p e he
  have hybPos : 0 < y - b := sub_leftApprox_pos y q e he
  have hxaBound : x - a < single p (2 * e) := by
    apply sub_leftApprox_lt_single
    linarith
  have hybBound : y - b < single q (2 * e) := by
    apply sub_leftApprox_lt_single
    linarith
  have hpMonoPos : 0 < single p (2 * e) := hxaPos.trans hxaBound
  have hproductBound :
      (x - a) * (y - b) < single (p + q) (4 * e ^ 2) := by
    calc
      (x - a) * (y - b) < single p (2 * e) * (y - b) :=
        mul_lt_mul_of_pos_right hxaBound hybPos
      _ < single p (2 * e) * single q (2 * e) :=
        mul_lt_mul_of_pos_left hybBound hpMonoPos
      _ = single (p + q) ((2 * e) * (2 * e)) :=
        single_mul_single p q (2 * e) (2 * e)
      _ = single (p + q) (4 * e ^ 2) := by ring_nf
  have hmonoGap :
      single (p + q) (4 * e ^ 2) <
        x * y - ((x * y).trunc k + single k r) := by
    rw [hpq]
    exact single_lt_sub_leftApprox (x * y) k r (4 * e ^ 2) heSmall
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · dsimp [mulOptionValue]
    have := hproductBound.trans hmonoGap
    nlinarith
  · exact mulOptionValue_lt_mul_of_lt_of_lt
      (lt_of_truncLT ha) (lt_of_truncLT hb)

/-- Every right coefficient truncation of a product strictly dominates an opposite-side
multiplication option, which is itself strictly above the product. -/
theorem exists_mulOptionValue_between_of_mem_truncGT
    {x y t : SurrealHahnSeries} (ht : t ∈ truncGT (x * y)) :
    ∃ a ∈ truncLT x, ∃ b ∈ truncGT y,
      x * y < mulOptionValue x y a b ∧ mulOptionValue x y a b < t := by
  rw [truncGT_def] at ht
  obtain ⟨k, hk, r, hr, rfl⟩ := ht
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_add_eq_of_mem_support_mul hk
  obtain ⟨e, he, heSmall⟩ := exists_small_square (sub_pos.mpr hr)
  let a := x.trunc p + single p (x.coeff p - e)
  let b := y.trunc q + single q (y.coeff q + e)
  have ha : a ∈ truncLT x := by
    apply trunc_add_single_truncLT hp
    linarith
  have hb : b ∈ truncGT y := by
    apply trunc_add_single_truncGT hq
    linarith
  have hxaPos : 0 < x - a := sub_leftApprox_pos x p e he
  have hbyPos : 0 < b - y := rightApprox_sub_pos y q e he
  have hxaBound : x - a < single p (2 * e) := by
    apply sub_leftApprox_lt_single
    linarith
  have hbyBound : b - y < single q (2 * e) := by
    apply rightApprox_sub_lt_single
    linarith
  have hpMonoPos : 0 < single p (2 * e) := hxaPos.trans hxaBound
  have hproductBound :
      (x - a) * (b - y) < single (p + q) (4 * e ^ 2) := by
    calc
      (x - a) * (b - y) < single p (2 * e) * (b - y) :=
        mul_lt_mul_of_pos_right hxaBound hbyPos
      _ < single p (2 * e) * single q (2 * e) :=
        mul_lt_mul_of_pos_left hbyBound hpMonoPos
      _ = single (p + q) ((2 * e) * (2 * e)) :=
        single_mul_single p q (2 * e) (2 * e)
      _ = single (p + q) (4 * e ^ 2) := by ring_nf
  have hmonoGap :
      single (p + q) (4 * e ^ 2) <
        ((x * y).trunc k + single k r) - x * y := by
    rw [hpq]
    exact single_lt_rightApprox_sub (x * y) k r (4 * e ^ 2) heSmall
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · exact mul_lt_mulOptionValue_of_lt_of_gt
      (lt_of_truncLT ha) (gt_of_truncGT hb)
  · dsimp [mulOptionValue]
    have := hproductBound.trans hmonoGap
    nlinarith

private theorem mulOption_equiv
    {x y a b : SurrealHahnSeries.{u}}
    (hay : (a * y).toSurreal = a.toSurreal * y.toSurreal)
    (hxb : (x * b).toSurreal = x.toSurreal * b.toSurreal)
    (hab : (a * b).toSurreal = a.toSurreal * b.toSurreal) :
    IGame.mulOption x.toIGame y.toIGame a.toIGame b.toIGame ≈
      (mulOptionValue x y a b).toIGame := by
  rw [← Surreal.mk_eq_mk]
  simp only [IGame.mulOption, Surreal.mk_sub, Surreal.mk_add, Surreal.mk_mul,
    mk_toIGame]
  rw [mulOptionValue_eq]
  simp only [sub_eq_add_neg, toSurreal_add, toSurreal_neg]
  rw [hay, hxb, hab]

private theorem cutMulOption_equiv
    {x y a b : SurrealHahnSeries.{u}}
    (hay : (a * y).toSurreal = a.toSurreal * y.toSurreal)
    (hxb : (x * b).toSurreal = x.toSurreal * b.toSurreal)
    (hab : (a * b).toSurreal = a.toSurreal * b.toSurreal) :
    IGame.mulOption !{toIGame '' truncLT x | toIGame '' truncGT x}
        !{toIGame '' truncLT y | toIGame '' truncGT y} a.toIGame b.toIGame ≈
          (mulOptionValue x y a b).toIGame := by
  exact (Numeric.mulOption_congr₁ (toIGame_equiv x).symm).trans <|
    (Numeric.mulOption_congr₂ (toIGame_equiv y).symm).trans <|
      mulOption_equiv hay hxb hab

/-- Truncation options of a series of limit length are strictly shorter. -/
private theorem length_lt_of_mem_truncLT_or_mem_truncGT {y b : SurrealHahnSeries.{u}}
    (hy : IsSuccPrelimit y.length) (hb : b ∈ truncLT y ∨ b ∈ truncGT y) :
    b.length < y.length :=
  hb.elim (length_lt_of_truncLT hy) (length_lt_of_truncGT hy)

/-- The constant series `single 0 r` represents the real number `r`. -/
private theorem toIGame_single_zero_equiv (r : ℝ) : (single 0 r).toIGame ≈ (r : IGame) := by
  rw [← Surreal.mk_eq_mk, mk_toIGame]
  simp [toSurreal_single]

/-- The constant series with dyadic coefficient `q` represents the dyadic `q`. -/
private theorem toIGame_single_zero_dyadic_equiv (q : Dyadic) :
    (single 0 (q.toRat : ℝ)).toIGame ≈ (q : IGame) := by
  apply AntisymmRel.trans ?_ (Real.toIGame_dyadic_equiv q)
  rw [← Surreal.mk_eq_mk, mk_toIGame]
  simp [toSurreal_single]

/-- Constant series are ordered by their coefficients. -/
private theorem single_zero_lt_single_zero {q r : ℝ} (h : q < r) :
    single 0 q < single 0 r := by
  rw [← toSurreal_lt_toSurreal_iff, toSurreal_single, toSurreal_single, Surreal.wpow_zero,
    mul_one, mul_one]
  exact Real.toSurreal_lt_iff.mpr h

/-- The Conway multiplication option of the real `r` against the cut of `y`, at the dyadic option
`q` of `r` and the truncation option `b` of `y`, is the Hahn-series multiplication option
`mulOptionValue (single 0 r) y (single 0 q) b`, provided multiplication by `single 0 r` is
already compatible on `b`. -/
private theorem mulOption_real_equiv (r : ℝ) (y : SurrealHahnSeries.{u}) (q : Dyadic)
    {b : SurrealHahnSeries.{u}}
    (hb : (single 0 r * b).toSurreal = (r : Surreal) * b.toSurreal) :
    IGame.mulOption (r : IGame) !{toIGame '' truncLT y | toIGame '' truncGT y}
        (q : IGame) b.toIGame ≈
      (mulOptionValue (single 0 r) y (single 0 (q.toRat : ℝ)) b).toIGame :=
  (Numeric.mulOption_congr₁ (toIGame_single_zero_equiv r).symm).trans <|
    (Numeric.mulOption_congr₂ (toIGame_equiv y).symm).trans <|
      (Numeric.mulOption_congr₃ (toIGame_single_zero_dyadic_equiv q).symm).trans <|
        mulOption_equiv
          (by simpa [toSurreal_single] using toSurreal_single_zero_ratCast_mul q.toRat y)
          (by simpa [toSurreal_single] using hb)
          (by simpa [toSurreal_single] using toSurreal_single_zero_ratCast_mul q.toRat b)

/-- The Conway multiplication option at the dyadic option `0` of `r` is the truncation option
`single 0 r * b` itself. -/
private theorem mulOption_real_zero_equiv (r : ℝ) (y : SurrealHahnSeries.{u})
    {b : SurrealHahnSeries.{u}}
    (hb : (single 0 r * b).toSurreal = (r : Surreal) * b.toSurreal) :
    IGame.mulOption (r : IGame) !{toIGame '' truncLT y | toIGame '' truncGT y}
        ((0 : Dyadic) : IGame) b.toIGame ≈ (single 0 r * b).toIGame := by
  grw [mulOption_real_equiv r y 0 hb]
  simp [mulOptionValue_eq]

/-- The cut of `single 0 r * y`, for `y` of limit length, fits between the options of the Conway
product of `r` with the cut of `y`: every option is a multiplication option at a dyadic option of
`r` and a truncation option of `y`, and lies on the correct side of the product. -/
private theorem fits_single_zero_mul (r : ℝ) {y : SurrealHahnSeries.{u}}
    (hy : IsSuccPrelimit y.length)
    (hmul : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single 0 r * b).toSurreal = (r : Surreal) * b.toSurreal) :
    Fits !{toIGame '' truncLT (single 0 r * y) | toIGame '' truncGT (single 0 r * y)}
      ((r : IGame) * !{toIGame '' truncLT y | toIGame '' truncGT y}) := by
  have hoption (q : Dyadic) {b : SurrealHahnSeries.{u}}
      (hb : b ∈ truncLT y ∨ b ∈ truncGT y) :=
    mulOption_real_equiv r y q (hmul b (length_lt_of_mem_truncLT_or_mem_truncGT hy hb))
  simp only [Fits, forall_moves_mul, moves_ofSets, Player.cases]
  constructor
  · intro p
    cases p <;> simp only [Real.forall_leftMoves_toIGame,
      Real.forall_rightMoves_toIGame, forall_mem_image]
    · intro q hq b hb
      rw [Numeric.not_le]
      grw [hoption q (Or.inl hb), ← toIGame_equiv (single 0 r * y)]
      exact_mod_cast mulOptionValue_lt_mul_of_lt_of_lt
        (single_zero_lt_single_zero hq) (lt_of_truncLT hb)
    · intro q hq b hb
      rw [Numeric.not_le]
      grw [hoption q (Or.inr hb), ← toIGame_equiv (single 0 r * y)]
      exact_mod_cast mulOptionValue_lt_mul_of_gt_of_gt
        (single_zero_lt_single_zero hq) (gt_of_truncGT hb)
  · intro p
    cases p <;> simp only [Real.forall_leftMoves_toIGame,
      Real.forall_rightMoves_toIGame, forall_mem_image]
    · intro q hq b hb
      rw [Numeric.not_le]
      grw [← toIGame_equiv (single 0 r * y), hoption q (Or.inr hb)]
      exact_mod_cast mul_lt_mulOptionValue_of_lt_of_gt
        (single_zero_lt_single_zero hq) (gt_of_truncGT hb)
    · intro q hq b hb
      rw [Numeric.not_le]
      grw [← toIGame_equiv (single 0 r * y), hoption q (Or.inl hb)]
      exact_mod_cast mul_lt_mulOptionValue_of_gt_of_lt
        (single_zero_lt_single_zero hq) (lt_of_truncLT hb)

/-- Every left truncation option of `single 0 r * y` is dominated by a left option of the Conway
product of `r` with the cut of `y`. The truncation option is `single 0 r * b` for a truncation
option `b` of `y` on the side determined by the sign of `r`, and the multiplication option at the
dyadic `0` and `b` represents it. -/
private theorem exists_leftMove_ge_of_mem_truncLT_single_zero_mul (r : ℝ)
    {y : SurrealHahnSeries.{u}} (hy : IsSuccPrelimit y.length)
    (hmul : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single 0 r * b).toSurreal = (r : Surreal) * b.toSurreal) :
    ∀ z ∈ !{toIGame '' truncLT (single 0 r * y) | toIGame '' truncGT (single 0 r * y)}ᴸ,
      ∃ w ∈ ((r : IGame) * !{toIGame '' truncLT y | toIGame '' truncGT y})ᴸ, z ≤ w := by
  rw [moves_ofSets]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨hrPos, b, hb, rfl⟩ | ⟨hrNeg, b, hb, rfl⟩ :=
    exists_eq_single_mul_of_mem_truncLT ht
  · refine ⟨_, mulOption_mem_moves_mul (b := b.toIGame) (px := left) (py := left)
      (Real.mem_leftMoves_toIGame_of_lt (q := 0) (by simpa using hrPos)) ?_, ?_⟩
    · rw [moves_ofSets]
      exact mem_image_of_mem toIGame hb
    · exact (mulOption_real_zero_equiv r y
        (hmul b (length_lt_of_mem_truncLT_or_mem_truncGT hy (Or.inl hb)))).symm.le
  · refine ⟨_, mulOption_mem_moves_mul (b := b.toIGame) (px := right) (py := right)
      (Real.mem_rightMoves_toIGame_of_lt (q := 0) (by simpa using hrNeg)) ?_, ?_⟩
    · rw [moves_ofSets]
      exact mem_image_of_mem toIGame hb
    · exact (mulOption_real_zero_equiv r y
        (hmul b (length_lt_of_mem_truncLT_or_mem_truncGT hy (Or.inr hb)))).symm.le

/-- Every right truncation option of `single 0 r * y` dominates a right option of the Conway
product of `r` with the cut of `y`, namely the multiplication option at the dyadic `0` and the
truncation option `b` of `y` with `single 0 r * b` the given option. -/
private theorem exists_rightMove_le_of_mem_truncGT_single_zero_mul (r : ℝ)
    {y : SurrealHahnSeries.{u}} (hy : IsSuccPrelimit y.length)
    (hmul : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single 0 r * b).toSurreal = (r : Surreal) * b.toSurreal) :
    ∀ z ∈ !{toIGame '' truncLT (single 0 r * y) | toIGame '' truncGT (single 0 r * y)}ᴿ,
      ∃ w ∈ ((r : IGame) * !{toIGame '' truncLT y | toIGame '' truncGT y})ᴿ, w ≤ z := by
  rw [moves_ofSets]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨hrPos, b, hb, rfl⟩ | ⟨hrNeg, b, hb, rfl⟩ :=
    exists_eq_single_mul_of_mem_truncGT ht
  · refine ⟨_, mulOption_mem_moves_mul (b := b.toIGame) (px := left) (py := right)
      (Real.mem_leftMoves_toIGame_of_lt (q := 0) (by simpa using hrPos)) ?_, ?_⟩
    · rw [moves_ofSets]
      exact mem_image_of_mem toIGame hb
    · exact (mulOption_real_zero_equiv r y
        (hmul b (length_lt_of_mem_truncLT_or_mem_truncGT hy (Or.inr hb)))).le
  · refine ⟨_, mulOption_mem_moves_mul (b := b.toIGame) (px := right) (py := left)
      (Real.mem_rightMoves_toIGame_of_lt (q := 0) (by simpa using hrNeg)) ?_, ?_⟩
    · rw [moves_ofSets]
      exact mem_image_of_mem toIGame hb
    · exact (mulOption_real_zero_equiv r y
        (hmul b (length_lt_of_mem_truncLT_or_mem_truncGT hy (Or.inl hb)))).le

/-- The limit step for multiplication by a real constant. Rational options of the real constant
are handled by additive compatibility, while truncation options of the other factor are strictly
shorter recursive inputs. -/
theorem toSurreal_single_zero_mul_of_isSuccPrelimit (r : ℝ)
    {y : SurrealHahnSeries.{u}} (hy : IsSuccPrelimit y.length)
    (hmul : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single 0 r * b).toSurreal = (r : Surreal) * b.toSurreal) :
    (single 0 r * y).toSurreal = (r : Surreal) * y.toSurreal := by
  rw [← mk_toIGame (single 0 r * y), ← mk_toIGame y, ← Surreal.mk_real_toIGame,
    ← Surreal.mk_mul]
  apply Surreal.mk_eq
  rw [toIGame_limit hy]
  exact (toIGame_equiv (single 0 r * y)).trans
    (Fits.equiv_of_forall_moves (fits_single_zero_mul r hy hmul)
      (exists_leftMove_ge_of_mem_truncLT_single_zero_mul r hy hmul)
      (exists_rightMove_le_of_mem_truncGT_single_zero_mul r hy hmul))

/-- Conway normal forms preserve multiplication by every real constant on the left. -/
theorem toSurreal_single_zero_mul (r : ℝ) (y : SurrealHahnSeries.{u}) :
    (single 0 r * y).toSurreal = (r : Surreal) * y.toSurreal := by
  induction y using lengthRecOn with
  | succ y i s hi hs IH =>
      rw [mul_add, toSurreal_add, IH, single_mul_single, toSurreal_single,
        toSurreal_succ hi, Real.toSurreal_mul]
      ring_nf
  | limit y hy IH => exact toSurreal_single_zero_mul_of_isSuccPrelimit r hy IH

private theorem toSurreal_single_mul_of_one (p : Surreal.{u}) (r : ℝ)
    (y : SurrealHahnSeries.{u})
    (hone : (single p 1 * y).toSurreal = ω^ p * y.toSurreal) :
    (single p r * y).toSurreal = (r : Surreal) * ω^ p * y.toSurreal := by
  have hfactor : single p r = single 0 r * single p 1 := by
    rw [single_mul_single]
    simp
  rw [hfactor, mul_assoc, toSurreal_single_zero_mul, hone]
  ring

private theorem toSurreal_single_one_mul_succ (g : IGame.{u}) [Numeric g]
    {y : SurrealHahnSeries.{u}} {i : Surreal} {s : ℝ}
    (hi : ∀ j ∈ y.support, i < j)
    (IH : (single (Surreal.mk g) 1 * y).toSurreal =
      ω^ (Surreal.mk g) * y.toSurreal) :
    (single (Surreal.mk g) 1 * (y + single i s)).toSurreal =
      ω^ (Surreal.mk g) * (y + single i s).toSurreal := by
  rw [mul_add, toSurreal_add, IH, single_mul_single, toSurreal_single,
    toSurreal_succ hi, Surreal.wpow_add]
  ring_nf

/-- The monomial `single (mk g) 1` represents `ω^ g`. -/
private theorem toIGame_single_one_equiv (g : IGame.{u}) [Numeric g] :
    (single (Surreal.mk g) 1).toIGame ≈ ω^ g := by
  rw [← Surreal.mk_eq_mk, mk_toIGame, Surreal.mk_wpow]
  simp [toSurreal_single]

/-- The monomial `single (mk z) q` with dyadic coefficient `q` represents `q * ω^ z`. -/
private theorem toIGame_single_dyadic_equiv (q : Dyadic) (z : IGame.{u}) [Numeric z] :
    (single (Surreal.mk z) (q.toRat : ℝ)).toIGame ≈ (q : IGame) * ω^ z := by
  rw [← Surreal.mk_eq_mk, mk_toIGame, Surreal.mk_mul, Surreal.mk_wpow, Surreal.mk_dyadic]
  simp [toSurreal_single]

/-- A dyadic multiple of the monomial at a left option `z` of `g` is below the monomial at `g`,
since `q * ω^ z < ω^ g` for `z < g`. -/
private theorem single_dyadic_lt_single_one_of_mem_leftMoves (g : IGame.{u}) [Numeric g]
    (q : Dyadic) {z : IGame.{u}} [Numeric z] (hz : z ∈ gᴸ) :
    single (Surreal.mk z) (q.toRat : ℝ) < single (Surreal.mk g) 1 := by
  rw [← toSurreal_lt_toSurreal_iff]
  simp only [toSurreal_single]
  simpa using
    Surreal.mul_wpow_lt_wpow q.toRat (Surreal.mk_lt_mk.mpr (Numeric.left_lt hz))

/-- The monomial at `g` is below every positive dyadic multiple of the monomial at a right option
`z` of `g`, since `ω^ g < q * ω^ z` for `g < z` and `0 < q`. -/
private theorem single_one_lt_single_dyadic_of_mem_rightMoves (g : IGame.{u}) [Numeric g]
    {q : Dyadic} {z : IGame.{u}} [Numeric z] (hq : 0 < q) (hz : z ∈ gᴿ) :
    single (Surreal.mk g) 1 < single (Surreal.mk z) (q.toRat : ℝ) := by
  rw [← toSurreal_lt_toSurreal_iff]
  simp only [toSurreal_single]
  have hqReal : (0 : ℝ) < (q.toRat : ℝ) := by exact_mod_cast hq
  simpa using Surreal.wpow_lt_mul_wpow hqReal
    (Surreal.mk_lt_mk.mpr (Numeric.lt_right hz))

/-- The Conway multiplication option of `ω^ g` against the cut of `y`, at the option `q * ω^ z`
of `ω^ g` and the truncation option `b` of `y`, is the Hahn-series multiplication option
`mulOptionValue (single (mk g) 1) y (single (mk z) q) b`, provided multiplication by
`single (mk z) 1` is compatible everywhere and multiplication by `single (mk g) 1` is compatible
on `b`. -/
private theorem mulOption_wpow_equiv (g : IGame.{u}) [Numeric g] (y : SurrealHahnSeries.{u})
    (q : Dyadic) {z : IGame.{u}} [Numeric z]
    (hz : ∀ c : SurrealHahnSeries.{u},
      (single (Surreal.mk z) 1 * c).toSurreal = ω^ (Surreal.mk z) * c.toSurreal)
    {b : SurrealHahnSeries.{u}}
    (hb : (single (Surreal.mk g) 1 * b).toSurreal = ω^ (Surreal.mk g) * b.toSurreal) :
    IGame.mulOption (ω^ g) !{toIGame '' truncLT y | toIGame '' truncGT y}
        ((q : IGame) * ω^ z) b.toIGame ≈
      (mulOptionValue (single (Surreal.mk g) 1) y
        (single (Surreal.mk z) (q.toRat : ℝ)) b).toIGame := by
  have hAcompat (c : SurrealHahnSeries.{u}) :
      (single (Surreal.mk z) (q.toRat : ℝ) * c).toSurreal =
        (single (Surreal.mk z) (q.toRat : ℝ)).toSurreal * c.toSurreal := by
    simpa [toSurreal_single, mul_assoc] using
      toSurreal_single_mul_of_one (Surreal.mk z) (q.toRat : ℝ) c (hz c)
  exact (Numeric.mulOption_congr₁ (toIGame_single_one_equiv g).symm).trans <|
    (Numeric.mulOption_congr₂ (toIGame_equiv y).symm).trans <|
      (Numeric.mulOption_congr₃ (toIGame_single_dyadic_equiv q z).symm).trans <|
        mulOption_equiv (hAcompat y) (by simpa [toSurreal_single] using hb) (hAcompat b)

/-- The Conway multiplication option at the option `0` of `ω^ g` is the truncation option
`single (mk g) 1 * b` itself. -/
private theorem mulOption_wpow_zero_equiv (g : IGame.{u}) [Numeric g]
    (y : SurrealHahnSeries.{u}) {b : SurrealHahnSeries.{u}}
    (hb : (single (Surreal.mk g) 1 * b).toSurreal = ω^ (Surreal.mk g) * b.toSurreal) :
    IGame.mulOption (ω^ g) !{toIGame '' truncLT y | toIGame '' truncGT y} 0 b.toIGame ≈
      (single (Surreal.mk g) 1 * b).toIGame :=
  (Numeric.mulOption_congr₁ (toIGame_single_one_equiv g).symm).trans <|
    (Numeric.mulOption_congr₂ (toIGame_equiv y).symm).trans <|
      (Numeric.mulOption_congr₃ toIGame_zero.symm.antisymmRel).trans <| by
        grw [mulOption_equiv (x := single (Surreal.mk g) 1) (y := y) (a := 0) (b := b)
          (by simp) (by simpa [toSurreal_single] using hb) (by simp)]
        simp [mulOptionValue_eq]

/-- The cut of `single (mk g) 1 * y`, for `y` of limit length, fits between the options of the
Conway product of `ω^ g` with the cut of `y`: every option is a multiplication option at an
option `0` or `q * ω^ z` of `ω^ g` and a truncation option of `y`, and lies on the correct side
of the product. -/
private theorem fits_single_one_mul (g : IGame.{u}) [Numeric g] {y : SurrealHahnSeries.{u}}
    (hy : IsSuccPrelimit y.length)
    (hmove : ∀ p z [Numeric z], z ∈ g.moves p → ∀ b : SurrealHahnSeries.{u},
      (single (Surreal.mk z) 1 * b).toSurreal = ω^ (Surreal.mk z) * b.toSurreal)
    (hlenRec : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single (Surreal.mk g) 1 * b).toSurreal = ω^ (Surreal.mk g) * b.toSurreal) :
    Fits !{toIGame '' truncLT (single (Surreal.mk g) 1 * y) |
        toIGame '' truncGT (single (Surreal.mk g) 1 * y)}
      (ω^ g * !{toIGame '' truncLT y | toIGame '' truncGT y}) := by
  have hoption (q : Dyadic) {p : Player} {z : IGame.{u}} [Numeric z] (hz : z ∈ g.moves p)
      {b : SurrealHahnSeries.{u}} (hb : b ∈ truncLT y ∨ b ∈ truncGT y) :=
    mulOption_wpow_equiv g y q (hmove p z hz)
      (hlenRec b (length_lt_of_mem_truncLT_or_mem_truncGT hy hb))
  have hzeroOption {b : SurrealHahnSeries.{u}} (hb : b ∈ truncLT y ∨ b ∈ truncGT y) :=
    mulOption_wpow_zero_equiv g y (hlenRec b (length_lt_of_mem_truncLT_or_mem_truncGT hy hb))
  have hxpos : 0 < single (Surreal.mk g) 1 := by
    rw [← toSurreal_lt_toSurreal_iff]
    simp [toSurreal_single]
  simp only [Fits, forall_moves_mul, moves_ofSets, Player.cases]
  constructor
  · intro p
    cases p <;> simp only [forall_leftMoves_wpow, forall_rightMoves_wpow,
      forall_mem_image]
    · constructor
      · intro b hb
        rw [Numeric.not_le]
        grw [hzeroOption (Or.inl hb), ← toIGame_equiv (single (Surreal.mk g) 1 * y)]
        exact_mod_cast mul_lt_mul_of_pos_left (lt_of_truncLT hb) hxpos
      · intro q _ z hz b hb
        let := Numeric.of_mem_moves hz
        rw [Numeric.not_le]
        grw [hoption q hz (Or.inl hb), ← toIGame_equiv (single (Surreal.mk g) 1 * y)]
        exact_mod_cast mulOptionValue_lt_mul_of_lt_of_lt
          (single_dyadic_lt_single_one_of_mem_leftMoves g q hz) (lt_of_truncLT hb)
    · intro q hq z hz b hb
      let := Numeric.of_mem_moves hz
      rw [Numeric.not_le]
      grw [hoption q hz (Or.inr hb), ← toIGame_equiv (single (Surreal.mk g) 1 * y)]
      exact_mod_cast mulOptionValue_lt_mul_of_gt_of_gt
        (single_one_lt_single_dyadic_of_mem_rightMoves g hq hz) (gt_of_truncGT hb)
  · intro p
    cases p <;> simp only [forall_leftMoves_wpow, forall_rightMoves_wpow,
      forall_mem_image]
    · constructor
      · intro b hb
        rw [Numeric.not_le]
        grw [← toIGame_equiv (single (Surreal.mk g) 1 * y), hzeroOption (Or.inr hb)]
        exact_mod_cast mul_lt_mul_of_pos_left (gt_of_truncGT hb) hxpos
      · intro q _ z hz b hb
        let := Numeric.of_mem_moves hz
        rw [Numeric.not_le]
        grw [← toIGame_equiv (single (Surreal.mk g) 1 * y), hoption q hz (Or.inr hb)]
        exact_mod_cast mul_lt_mulOptionValue_of_lt_of_gt
          (single_dyadic_lt_single_one_of_mem_leftMoves g q hz) (gt_of_truncGT hb)
    · intro q hq z hz b hb
      let := Numeric.of_mem_moves hz
      rw [Numeric.not_le]
      grw [← toIGame_equiv (single (Surreal.mk g) 1 * y), hoption q hz (Or.inl hb)]
      exact_mod_cast mul_lt_mulOptionValue_of_gt_of_lt
        (single_one_lt_single_dyadic_of_mem_rightMoves g hq hz) (lt_of_truncLT hb)

/-- Every left truncation option of `single (mk g) 1 * y` is dominated by a left option of the
Conway product of `ω^ g` with the cut of `y`: it is `single (mk g) 1 * b` for a left truncation
option `b` of `y`, represented by the multiplication option at `0` and `b`. -/
private theorem exists_leftMove_ge_of_mem_truncLT_single_one_mul (g : IGame.{u}) [Numeric g]
    {y : SurrealHahnSeries.{u}} (hy : IsSuccPrelimit y.length)
    (hlenRec : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single (Surreal.mk g) 1 * b).toSurreal = ω^ (Surreal.mk g) * b.toSurreal) :
    ∀ z ∈ !{toIGame '' truncLT (single (Surreal.mk g) 1 * y) |
        toIGame '' truncGT (single (Surreal.mk g) 1 * y)}ᴸ,
      ∃ w ∈ (ω^ g * !{toIGame '' truncLT y | toIGame '' truncGT y})ᴸ, z ≤ w := by
  rw [moves_ofSets]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨-, b, hb, rfl⟩ | ⟨hfalse, -⟩ := exists_eq_single_mul_of_mem_truncLT ht
  · refine ⟨_, mulOption_mem_moves_mul (b := b.toIGame) (px := left) (py := left)
      (zero_mem_leftMoves_wpow g) ?_, ?_⟩
    · rw [moves_ofSets]
      exact mem_image_of_mem toIGame hb
    · exact (mulOption_wpow_zero_equiv g y
        (hlenRec b (length_lt_of_mem_truncLT_or_mem_truncGT hy (Or.inl hb)))).symm.le
  · norm_num at hfalse

/-- Every right truncation option of `single (mk g) 1 * y` dominates a right option of the
Conway product of `ω^ g` with the cut of `y`: it is `single (mk g) 1 * b` for a right truncation
option `b` of `y`, represented by the multiplication option at `0` and `b`. -/
private theorem exists_rightMove_le_of_mem_truncGT_single_one_mul (g : IGame.{u}) [Numeric g]
    {y : SurrealHahnSeries.{u}} (hy : IsSuccPrelimit y.length)
    (hlenRec : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single (Surreal.mk g) 1 * b).toSurreal = ω^ (Surreal.mk g) * b.toSurreal) :
    ∀ z ∈ !{toIGame '' truncLT (single (Surreal.mk g) 1 * y) |
        toIGame '' truncGT (single (Surreal.mk g) 1 * y)}ᴿ,
      ∃ w ∈ (ω^ g * !{toIGame '' truncLT y | toIGame '' truncGT y})ᴿ, w ≤ z := by
  rw [moves_ofSets]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨-, b, hb, rfl⟩ | ⟨hfalse, -⟩ := exists_eq_single_mul_of_mem_truncGT ht
  · refine ⟨_, mulOption_mem_moves_mul (b := b.toIGame) (px := left) (py := right)
      (zero_mem_leftMoves_wpow g) ?_, ?_⟩
    · rw [moves_ofSets]
      exact mem_image_of_mem toIGame hb
    · exact (mulOption_wpow_zero_equiv g y
        (hlenRec b (length_lt_of_mem_truncLT_or_mem_truncGT hy (Or.inr hb)))).le
  · norm_num at hfalse

/-- The limit step for multiplication by the monomial `single (mk g) 1`, given compatibility of
the monomials at the options of `g` on every input and of this monomial on strictly shorter
inputs. -/
private theorem toSurreal_single_one_mul_limit (g : IGame.{u}) [Numeric g]
    {y : SurrealHahnSeries.{u}} (hy : IsSuccPrelimit y.length)
    (hmove : ∀ p z [Numeric z], z ∈ g.moves p → ∀ b : SurrealHahnSeries.{u},
      (single (Surreal.mk z) 1 * b).toSurreal = ω^ (Surreal.mk z) * b.toSurreal)
    (hlenRec : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (single (Surreal.mk g) 1 * b).toSurreal = ω^ (Surreal.mk g) * b.toSurreal) :
    (single (Surreal.mk g) 1 * y).toSurreal = ω^ (Surreal.mk g) * y.toSurreal := by
  rw [← mk_toIGame (single (Surreal.mk g) 1 * y), ← mk_toIGame y, ← Surreal.mk_wpow,
    ← Surreal.mk_mul]
  apply Surreal.mk_eq
  rw [toIGame_limit hy]
  exact (toIGame_equiv (single (Surreal.mk g) 1 * y)).trans
    (Fits.equiv_of_forall_moves (fits_single_one_mul g hy hmove hlenRec)
      (exists_leftMove_ge_of_mem_truncLT_single_one_mul g hy hlenRec)
      (exists_rightMove_le_of_mem_truncGT_single_one_mul g hy hlenRec))

private theorem toSurreal_single_one_mul (g : IGame.{u}) [Numeric g]
    (y : SurrealHahnSeries.{u}) :
    (single (Surreal.mk g) 1 * y).toSurreal = ω^ (Surreal.mk g) * y.toSurreal := by
  let motive := fun g : IGame.{u} ↦ ∀ (_hg : Numeric g) (y : SurrealHahnSeries.{u}),
    (single (Surreal.mk g) 1 * y).toSurreal = ω^ (Surreal.mk g) * y.toSurreal
  apply IGame.moveRecOn (motive := motive) g
  intro g IH hg y
  induction y using lengthRecOn with
  | succ y i s hi hs IHlen => exact toSurreal_single_one_mul_succ g hi IHlen
  | limit y hy IHlen =>
      apply toSurreal_single_one_mul_limit g hy
      · intro p z hzNumeric hz b
        exact IH p z hz hzNumeric b
      · exact IHlen

/-- Conway normal forms preserve multiplication by an arbitrary singleton on the left. -/
theorem toSurreal_single_mul (p : Surreal.{u}) (r : ℝ) (y : SurrealHahnSeries.{u}) :
    (single p r * y).toSurreal = (single p r).toSurreal * y.toSurreal := by
  calc
    (single p r * y).toSurreal = (r : Surreal) * ω^ p * y.toSurreal :=
      toSurreal_single_mul_of_one p r y (by simpa using toSurreal_single_one_mul p.out y)
    _ = (single p r).toSurreal * y.toSurreal := by rw [toSurreal_single]

/-- The limit-by-limit induction step for Conway normal-form multiplication, stated with the two
recursive axes it uses. Compatibility for shorter left inputs is needed only against right inputs
no longer than the fixed right input; compatibility for shorter right inputs is needed only against
the fixed left input. -/
theorem toSurreal_mul_of_isSuccPrelimit_of_axes
    {x y : SurrealHahnSeries.{u}}
    (hx : IsSuccPrelimit x.length) (hy : IsSuccPrelimit y.length)
    (hmulLeft : ∀ a b : SurrealHahnSeries.{u},
      a.length < x.length → b.length ≤ y.length →
      (a * b).toSurreal = a.toSurreal * b.toSurreal)
    (hmulRight : ∀ b : SurrealHahnSeries.{u}, b.length < y.length →
      (x * b).toSurreal = x.toSurreal * b.toSurreal) :
    (x * y).toSurreal = x.toSurreal * y.toSurreal := by
  have hlenX {a : SurrealHahnSeries.{u}}
      (ha : a ∈ truncLT x ∨ a ∈ truncGT x) : a.length < x.length :=
    ha.elim (length_lt_of_truncLT hx) (length_lt_of_truncGT hx)
  have hlenY {b : SurrealHahnSeries.{u}}
      (hb : b ∈ truncLT y ∨ b ∈ truncGT y) : b.length < y.length :=
    hb.elim (length_lt_of_truncLT hy) (length_lt_of_truncGT hy)
  have hmulAY {a : SurrealHahnSeries.{u}} (ha : a ∈ truncLT x ∨ a ∈ truncGT x) :
      (a * y).toSurreal = a.toSurreal * y.toSurreal :=
    hmulLeft a y (hlenX ha) le_rfl
  have hmulXB {b : SurrealHahnSeries.{u}} (hb : b ∈ truncLT y ∨ b ∈ truncGT y) :
      (x * b).toSurreal = x.toSurreal * b.toSurreal :=
    hmulRight b (hlenY hb)
  have hmulAB {a b : SurrealHahnSeries.{u}}
      (ha : a ∈ truncLT x ∨ a ∈ truncGT x)
      (hb : b ∈ truncLT y ∨ b ∈ truncGT y) :
      (a * b).toSurreal = a.toSurreal * b.toSurreal :=
    hmulLeft a b (hlenX ha) (hlenY hb).le
  rw [← mk_toIGame (x * y), ← mk_toIGame x, ← mk_toIGame y,
    ← Surreal.mk_mul]
  apply Surreal.mk_eq
  rw [toIGame_limit hx, toIGame_limit hy]
  apply (toIGame_equiv (x * y)).trans
  apply Fits.equiv_of_forall_moves
  · simp only [Fits, forall_moves_mul, moves_ofSets, Player.cases]
    constructor
    · intro p
      cases p <;> simp only [forall_mem_image]
      · intro a ha b hb
        rw [Numeric.not_le]
        grw [cutMulOption_equiv (hmulAY (Or.inl ha)) (hmulXB (Or.inl hb))
          (hmulAB (Or.inl ha) (Or.inl hb)), ← toIGame_equiv (x * y)]
        exact_mod_cast mulOptionValue_lt_mul_of_lt_of_lt
          (lt_of_truncLT ha) (lt_of_truncLT hb)
      · intro a ha b hb
        rw [Numeric.not_le]
        grw [cutMulOption_equiv (hmulAY (Or.inr ha)) (hmulXB (Or.inr hb))
          (hmulAB (Or.inr ha) (Or.inr hb)), ← toIGame_equiv (x * y)]
        exact_mod_cast mulOptionValue_lt_mul_of_gt_of_gt
          (gt_of_truncGT ha) (gt_of_truncGT hb)
    · intro p
      cases p <;> simp only [forall_mem_image]
      · intro a ha b hb
        rw [Numeric.not_le]
        grw [← toIGame_equiv (x * y),
          cutMulOption_equiv (hmulAY (Or.inl ha)) (hmulXB (Or.inr hb))
            (hmulAB (Or.inl ha) (Or.inr hb))]
        exact_mod_cast mul_lt_mulOptionValue_of_lt_of_gt
          (lt_of_truncLT ha) (gt_of_truncGT hb)
      · intro a ha b hb
        rw [Numeric.not_le]
        grw [← toIGame_equiv (x * y),
          cutMulOption_equiv (hmulAY (Or.inr ha)) (hmulXB (Or.inl hb))
            (hmulAB (Or.inr ha) (Or.inl hb))]
        exact_mod_cast mul_lt_mulOptionValue_of_gt_of_lt
          (gt_of_truncGT ha) (lt_of_truncLT hb)
  · rw [moves_ofSets]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, ha, b, hb, htb, -⟩ :=
      exists_mulOptionValue_between_of_mem_truncLT ht
    let w := IGame.mulOption
      !{toIGame '' truncLT x | toIGame '' truncGT x}
      !{toIGame '' truncLT y | toIGame '' truncGT y}
        a.toIGame b.toIGame
    refine ⟨w, ?_, ?_⟩
    · dsimp only [w]
      apply mulOption_mem_moves_mul (px := left) (py := left)
      · rw [moves_ofSets]
        exact mem_image_of_mem toIGame ha
      · rw [moves_ofSets]
        exact mem_image_of_mem toIGame hb
    · dsimp only [w]
      grw [cutMulOption_equiv (hmulAY (Or.inl ha)) (hmulXB (Or.inl hb))
        (hmulAB (Or.inl ha) (Or.inl hb))]
      exact (toIGame_lt_toIGame_iff.mpr htb).le
  · rw [moves_ofSets]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, ha, b, hb, -, hbt⟩ :=
      exists_mulOptionValue_between_of_mem_truncGT ht
    let w := IGame.mulOption
      !{toIGame '' truncLT x | toIGame '' truncGT x}
      !{toIGame '' truncLT y | toIGame '' truncGT y}
        a.toIGame b.toIGame
    refine ⟨w, ?_, ?_⟩
    · dsimp only [w]
      apply mulOption_mem_moves_mul (px := left) (py := right)
      · rw [moves_ofSets]
        exact mem_image_of_mem toIGame ha
      · rw [moves_ofSets]
        exact mem_image_of_mem toIGame hb
    · dsimp only [w]
      grw [cutMulOption_equiv (hmulAY (Or.inl ha)) (hmulXB (Or.inr hb))
        (hmulAB (Or.inl ha) (Or.inr hb))]
      exact (toIGame_lt_toIGame_iff.mpr hbt).le

/-- The limit-by-limit induction step for Conway normal-form multiplication. If multiplication is
already compatible whenever at least one input has strictly shorter support, it is compatible for
two inputs whose support lengths are successor prelimits. -/
theorem toSurreal_mul_of_isSuccPrelimit
    {x y : SurrealHahnSeries.{u}}
    (hx : IsSuccPrelimit x.length) (hy : IsSuccPrelimit y.length)
    (hmul : ∀ a b : SurrealHahnSeries.{u},
      a.length ≤ x.length → b.length ≤ y.length →
      (a.length < x.length ∨ b.length < y.length) →
      (a * b).toSurreal = a.toSurreal * b.toSurreal) :
    (x * y).toSurreal = x.toSurreal * y.toSurreal :=
  toSurreal_mul_of_isSuccPrelimit_of_axes hx hy
    (fun a b ha hb ↦ hmul a b ha.le hb (Or.inl ha))
    (fun b hb ↦ hmul x b le_rfl hb.le (Or.inr hb))

/-- The Conway normal-form equivalence from surreal Hahn series to surreal numbers preserves
multiplication. -/
theorem toSurreal_mul (x y : SurrealHahnSeries.{u}) :
    (x * y).toSurreal = x.toSurreal * y.toSurreal := by
  apply lengthRecOn (motive := fun x ↦ ∀ y,
    (x * y).toSurreal = x.toSurreal * y.toSurreal) x
  · intro x i r hi _ IH y
    rw [add_mul, toSurreal_add, IH, toSurreal_single_mul, toSurreal_succ hi,
      toSurreal_single]
    ring
  · intro x hx IHx y
    apply lengthRecOn (motive := fun y ↦
      (x * y).toSurreal = x.toSurreal * y.toSurreal) y
    · intro y i r hi _ IHy
      have hsingle :
          (x * single i r).toSurreal = x.toSurreal * (single i r).toSurreal := by
        rw [mul_comm, toSurreal_single_mul, mul_comm]
      rw [mul_add, toSurreal_add, IHy, hsingle, toSurreal_succ hi, toSurreal_single]
      ring
    · intro y hy IHy
      exact toSurreal_mul_of_isSuccPrelimit_of_axes hx hy
        (fun a b ha _ ↦ IHx a ha b) IHy

/-- Conway normal forms preserve arbitrary surreal products. -/
@[simp]
theorem _root_.Surreal.toHahnSeries_mul (x y : Surreal.{u}) :
    (x * y).toHahnSeries = x.toHahnSeries * y.toHahnSeries := by
  apply toSurreal_strictMono.injective
  rw [toSurreal_mul, Surreal.toSurreal_toHahnSeries,
    Surreal.toSurreal_toHahnSeries, Surreal.toSurreal_toHahnSeries]

/-- Conway normal form as a ring equivalence between surreals and small surreal Hahn series. -/
def _root_.Surreal.toHahnSeriesRingEquiv :
    Surreal.{u} ≃+* SurrealHahnSeries.{u} where
  toEquiv := Surreal.toHahnSeriesOrderIso.toEquiv
  map_add' := Surreal.toHahnSeries_add
  map_mul' := Surreal.toHahnSeries_mul

@[simp]
theorem _root_.Surreal.toHahnSeriesRingEquiv_apply (x : Surreal.{u}) :
    Surreal.toHahnSeriesRingEquiv x = x.toHahnSeries :=
  (rfl)

@[simp]
theorem _root_.Surreal.toHahnSeriesRingEquiv_symm_apply (x : SurrealHahnSeries.{u}) :
    Surreal.toHahnSeriesRingEquiv.symm x = x.toSurreal :=
  (rfl)

end SurrealHahnSeries
