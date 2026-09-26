/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Multiplicativity
import Mathlib.Tactic.Abel

/-!
# Addition of principal series

This module proves the corrected form of LM24, Proposition 3.6.2. The printed proposition assumes
only that `b`, `c` are principal and `deg (b + c) = deg b`. That statement is false: if `b` is a
principal series of positive degree and `c = 1`, then `deg (b + c) = deg b`, but the terminal
constant makes `b + c` nonprincipal.
`ConwayRefinement.HahnSeries.Tests.PrincipalAddition` preserves this counterexample.

After being shown the counterexample, Mantova confirmed in correspondence that imposing
`deg b = deg c` repairs the proposition. He also suggested the potentially more general
hypothesis that the two degrees are either both zero or both nonzero. This module proves and
uses only the equal-degree version; the broader version is not treated as established.

Both later uses in LM24 have the additional equality `deg c = deg b`. Under the proved
hypotheses

`deg b = deg c = deg (b + c)`,

the source argument is valid. Every proper negative truncation of each summand has degree below
the common degree, so the same holds for the sum. This forces the support supremum of the sum to
be zero and bounds each closed initial segment of its support below the corresponding power of
`ω`. The generic initial-segment criterion then identifies the full support order type with that
power.
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace HahnSeries.Nonpositive

open HahnSeries

variable {K : Type v} [Field K]

/-- Negation preserves principality. -/
@[simp]
theorem IsPrincipal.neg {p : Nonpositive ℝ K} (hp : IsPrincipal p) :
    IsPrincipal (-p) := by
  rw [isPrincipal_iff]
  constructor
  · change HahnSeries.IsWeaklyPrincipal (-(p : K⟦ℝ⟧))
    rw [HahnSeries.isWeaklyPrincipal_iff, HahnSeries.supportOrderType_neg]
    exact HahnSeries.isWeaklyPrincipal_iff.mp hp.isWeaklyPrincipal
  · simpa only [supportSup_neg] using hp.supportSup_eq_zero

/-- Multiplication by a nonzero coefficient, embedded as a constant Hahn series, preserves
principality. -/
theorem IsPrincipal.const_mul {p : Nonpositive ℝ K} (hp : IsPrincipal p)
    {k : K} (hk : k ≠ 0) :
    IsPrincipal ((C : K →+* Nonpositive ℝ K) k * p) := by
  have hsupport :
      ((((C : K →+* Nonpositive ℝ K) k * p : Nonpositive ℝ K) :
          K⟦ℝ⟧).support) = (p : K⟦ℝ⟧).support := by
    rw [Subring.coe_mul, coe_C, HahnSeries.C_mul_eq_smul]
    ext x
    simp [HahnSeries.mem_support, HahnSeries.coeff_smul, hk]
  have htype :
      HahnSeries.supportOrderType
          (↑((C : K →+* Nonpositive ℝ K) k * p) : K⟦ℝ⟧) =
        (p : K⟦ℝ⟧).supportOrderType := by
    rw [HahnSeries.supportOrderType_eq_setOrderType,
      HahnSeries.supportOrderType_eq_setOrderType]
    exact Set.IsPWO.orderType_congr _ _ hsupport
  rw [isPrincipal_iff]
  constructor
  · rw [HahnSeries.isWeaklyPrincipal_iff, htype]
    exact HahnSeries.isWeaklyPrincipal_iff.mp hp.isWeaklyPrincipal
  · have hproductNe : (C : K →+* Nonpositive ℝ K) k * p ≠ 0 :=
      mul_ne_zero (isPrincipal_C hk).ne_zero hp.ne_zero
    calc
      supportSup ((C : K →+* Nonpositive ℝ K) k * p) = supportSup p := by
        rw [supportSup_of_ne hproductNe, supportSup_of_ne hp.ne_zero, hsupport]
      _ = 0 := hp.supportSup_eq_zero

/-- A principal series of degree `α` has support order type `ω^α`. -/
theorem IsPrincipal.supportOrderType_eq_wpow_of_degree_eq
    {p : Nonpositive ℝ K} (hp : IsPrincipal p) {α : NatOrdinal}
    (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal)) :
    (p : K⟦ℝ⟧).supportOrderType = (ω^ α).val := by
  obtain ⟨e, he⟩ := Ordinal.isAdditivelyPrincipal_iff.mp
    (HahnSeries.isWeaklyPrincipal_iff.mp hp.isWeaklyPrincipal)
  have hdegree : (NatOrdinal.of e : WithBot NatOrdinal) = α := by
    rw [HahnSeries.degree_eq_cantorDegree, he,
      Ordinal.cantorDegree_of_ne_zero
        (Ordinal.opow_ne_zero e Ordinal.omega0_ne_zero),
      Ordinal.log_opow Ordinal.one_lt_omega0] at hpDegree
    exact hpDegree
  have hdegree' : NatOrdinal.of e = α := WithBot.coe_eq_coe.mp hdegree
  rw [he, ← hdegree']
  simp

/-- A principal series of positive degree has zero constant coefficient. -/
theorem IsPrincipal.constantCoeff_eq_zero_of_degree_pos
    {p : Nonpositive ℝ K} (hp : IsPrincipal p) {α : NatOrdinal}
    (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal))
    (hα : 0 < α) :
    constantCoeff p = 0 := by
  have hpType := hp.supportOrderType_eq_wpow_of_degree_eq hpDegree
  rw [constantCoeff_apply]
  apply not_ne_iff.mp
  intro hcoeff
  have hzeroSupport : 0 ∈ (p : K⟦ℝ⟧).support :=
    (HahnSeries.mem_support _ _).mpr hcoeff
  have hlimit : Order.IsSuccLimit (p : K⟦ℝ⟧).isPWO_support.orderType := by
    rw [← supportOrderType_eq_setOrderType, hpType, NatOrdinal.val_wpow]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
      (NatOrdinal.val.strictMono hα).ne'
  obtain ⟨y, hy, hypos⟩ :=
    (p : K⟦ℝ⟧).isPWO_support.exists_gt_of_isSuccLimit_orderType
      hlimit hzeroSupport
  exact (not_lt_of_ge (support_subset p hy)) hypos

private theorem truncLE_ne_self_of_isPrincipal
    {p : Nonpositive ℝ K} (hp : IsPrincipal p) {x : ℝ} (hx : x < 0) :
    truncLE x (p : K⟦ℝ⟧) ≠ p := by
  have hpLUB : IsLUB (p : K⟦ℝ⟧).support 0 :=
    (supportSup_eq_coe_iff.mp hp.supportSup_eq_zero).2
  obtain ⟨y, hy, hxy, -⟩ := hpLUB.exists_between hx
  intro heq
  have hyTrunc : y ∈ (truncLE x (p : K⟦ℝ⟧)).support := by
    rw [heq]
    exact hy
  rw [support_truncLE] at hyTrunc
  exact (not_lt_of_ge hyTrunc.2) hxy

/-- Every negative weak truncation of a principal series has degree below its degree. -/
theorem IsPrincipal.degree_truncLE_lt_of_degree_eq
    {p : Nonpositive ℝ K} (hp : IsPrincipal p) {α : NatOrdinal}
    (hpDegree : (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal))
    {x : ℝ} (hx : x < 0) :
    (truncLE x (p : K⟦ℝ⟧)).degree < (α : WithBot NatOrdinal) := by
  rw [← hpDegree]
  exact degree_lt_of_supportOrderType_lt_of_isWeaklyPrincipal
    hp.isWeaklyPrincipal
    (supportOrderType_truncLE_lt x (truncLE_ne_self_of_isPrincipal hp hx))

private theorem support_subsingleton_of_supportOrderType_eq_one
    {p : K⟦ℝ⟧} (hpType : p.supportOrderType = 1) :
    p.support.Subsingleton := by
  intro x hx y hy
  apply le_antisymm
  · apply le_of_not_gt
    intro hyx
    let hbelow := p.isPWO_support.mono
      (s := p.support ∩ Set.Iio x) Set.inter_subset_left
    have hbelowLt := p.isPWO_support.orderType_inter_Iio_lt hx
    rw [← supportOrderType_eq_setOrderType, hpType] at hbelowLt
    have hbelowZero : hbelow.orderType = 0 := by simpa using hbelowLt
    have hbelowEmpty := hbelow.orderType_eq_zero.mp hbelowZero
    have : y ∈ p.support ∩ Set.Iio x := ⟨hy, hyx⟩
    rw [hbelowEmpty] at this
    exact this
  · apply le_of_not_gt
    intro hxy
    let hbelow := p.isPWO_support.mono
      (s := p.support ∩ Set.Iio y) Set.inter_subset_left
    have hbelowLt := p.isPWO_support.orderType_inter_Iio_lt hy
    rw [← supportOrderType_eq_setOrderType, hpType] at hbelowLt
    have hbelowZero : hbelow.orderType = 0 := by simpa using hbelowLt
    have hbelowEmpty := hbelow.orderType_eq_zero.mp hbelowZero
    have : x ∈ p.support ∩ Set.Iio y := ⟨hx, hxy⟩
    rw [hbelowEmpty] at this
    exact this

/-- A principal series of degree zero is exactly its constant coefficient. -/
theorem IsPrincipal.eq_C_constantCoeff_of_degree_zero
    {p : Nonpositive ℝ K} (hp : IsPrincipal p)
    (hpDegree : (p : K⟦ℝ⟧).degree = (0 : WithBot NatOrdinal)) :
    p = C (constantCoeff p) := by
  have hpType : (p : K⟦ℝ⟧).supportOrderType = 1 := by
    simpa using hp.supportOrderType_eq_wpow_of_degree_eq hpDegree
  have hpSubsingleton := support_subsingleton_of_supportOrderType_eq_one hpType
  have hpNe : (p : K⟦ℝ⟧) ≠ 0 := by simpa using hp.ne_zero
  obtain ⟨z, hz⟩ := HahnSeries.support_nonempty_iff.mpr hpNe
  have hpSupport : (p : K⟦ℝ⟧).support = {z} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (hpSubsingleton hy hz)
    · intro hy
      exact Set.mem_singleton_iff.mp hy ▸ hz
  have hpLUB : IsLUB (p : K⟦ℝ⟧).support 0 :=
    (supportSup_eq_coe_iff.mp hp.supportSup_eq_zero).2
  have hz0 : z = 0 := by
    rw [hpSupport] at hpLUB
    exact isLUB_singleton.unique hpLUB
  apply Subtype.ext
  ext x
  by_cases hx : x = 0
  · subst x
    simp [constantCoeff_apply]
  · have hxSupport : x ∉ (p : K⟦ℝ⟧).support := by
      rw [hpSupport, hz0, Set.mem_singleton_iff]
      exact hx
    have hxCoeff : (p : K⟦ℝ⟧).coeff x = 0 := by
      rwa [← not_ne_iff, ← HahnSeries.mem_support]
    simp [coe_C, hx, hxCoeff]

private theorem add_of_same_degree_coe
    {b c : Nonpositive ℝ K} (hb : IsPrincipal b) (hc : IsPrincipal c)
    {α : NatOrdinal}
    (hbDegree : (b : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal))
    (hcDegree : (c : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal))
    (hsumDegree : ((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
      (α : WithBot NatOrdinal)) :
    IsPrincipal (b + c) := by
  have hsumNe : b + c ≠ 0 := by
    intro hzero
    have : ((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).degree = ⊥ := by
      rw [hzero]
      exact degree_zero
    exact WithBot.bot_ne_coe (this.symm.trans hsumDegree)
  rcases eq_or_ne α 0 with rfl | hα
  · have hbC := hb.eq_C_constantCoeff_of_degree_zero hbDegree
    have hcC := hc.eq_C_constantCoeff_of_degree_zero hcDegree
    rw [hbC, hcC, ← map_add]
    apply isPrincipal_C
    intro hcoeff
    apply hsumNe
    rw [hbC, hcC, ← map_add, hcoeff, map_zero]
  · have hαpos : 0 < α := bot_lt_iff_ne_bot.mpr hα
    have hbZeroCoeff := hb.constantCoeff_eq_zero_of_degree_pos hbDegree hαpos
    have hcZeroCoeff := hc.constantCoeff_eq_zero_of_degree_pos hcDegree hαpos
    have hsumZeroCoeff : constantCoeff (b + c) = 0 := by
      rw [map_add, hbZeroCoeff, hcZeroCoeff, add_zero]
    have htruncDegree : ∀ x : ℝ, x < 0 →
        (truncLE x (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧))).degree <
          (α : WithBot NatOrdinal) := by
      intro x hx
      change (truncLE x ((b : K⟦ℝ⟧) + (c : K⟦ℝ⟧))).degree <
        (α : WithBot NatOrdinal)
      rw [truncLE_add]
      apply (degree_add_le _ _).trans_lt
      exact max_lt
        (hb.degree_truncLE_lt_of_degree_eq hbDegree hx)
        (hc.degree_truncLE_lt_of_degree_eq hcDegree hx)
    have hsumSup : supportSup (b + c) = 0 := by
      apply le_antisymm (supportSup_le_zero (b + c))
      apply le_of_not_gt
      intro hsupLt
      rw [supportSup_of_ne hsumNe] at hsupLt
      have hsupLtReal : sSup (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).support) < 0 :=
        WithBot.coe_lt_coe.mp hsupLt
      obtain ⟨x, hsx, hx0⟩ := exists_between hsupLtReal
      have hsupportLE : (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).support) ⊆
          Set.Iic x := by
        intro y hy
        exact (le_csSup (bddAbove_support (b + c)) hy).trans hsx.le
      have htruncSelf :
          truncLE x (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧)) = b + c :=
        truncLE_eq_self_of_support_subset_Iic hsupportLE
      have hsumDegree' : ((b : K⟦ℝ⟧) + (c : K⟦ℝ⟧)).degree =
          (α : WithBot NatOrdinal) := by
        simpa using hsumDegree
      have hlt := htruncDegree x hx0
      rw [htruncSelf, hsumDegree'] at hlt
      exact (lt_irrefl _ hlt)
    rw [isPrincipal_iff]
    refine ⟨?_, hsumSup⟩
    rw [HahnSeries.isWeaklyPrincipal_iff]
    have htypeLE : (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).supportOrderType) ≤
        (ω^ α).val := by
      rw [supportOrderType_eq_setOrderType]
      apply Set.IsPWO.orderType_le_of_forall_inter_Iic_lt
        (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).isPWO_support)
      intro x hx
      have hx0 : x < 0 := by
        have hxle := support_subset (b + c) hx
        exact lt_of_le_of_ne hxle fun hxzero ↦ by
          subst x
          exact (HahnSeries.mem_support _ _).mp hx (by
            simpa [constantCoeff_apply] using hsumZeroCoeff)
      have hsupportTrunc :
          (truncLE x (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧))).support =
            (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).support ∩ Set.Iic x) := by
        rw [support_truncLE]
        rfl
      let hInter :=
        (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).isPWO_support).mono
          (s := ((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).support ∩ Set.Iic x)
          Set.inter_subset_left
      let hTrunc :=
        (truncLE x (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧))).isPWO_support
      change hInter.orderType < (ω^ α).val
      calc
        hInter.orderType = hTrunc.orderType :=
          hInter.orderType_congr hTrunc hsupportTrunc.symm
        _ = (truncLE x (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧))).supportOrderType :=
          (supportOrderType_eq_setOrderType _).symm
        _ < (ω^ α).val :=
          (degree_lt_coe_iff_supportOrderType_lt_wpow _ α).mp
            (htruncDegree x hx0)
    have htypeGE : (ω^ α).val ≤
        (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).supportOrderType) := by
      have hsumNe' : (((b + c : Nonpositive ℝ K) : K⟦ℝ⟧)) ≠ 0 := by
        intro hzero
        exact hsumNe (Subtype.ext hzero)
      have h := (coe_le_degree_iff (x :=
        ((b + c : Nonpositive ℝ K) : K⟦ℝ⟧)) (a := α.val) hsumNe').mp
        (by rw [hsumDegree]; simp)
      simpa only [NatOrdinal.val_wpow] using h
    rw [le_antisymm htypeLE htypeGE]
    exact Ordinal.isAdditivelyPrincipal_omega0_opow α.val

/-- Corrected LM24, Proposition 3.6.2: a sum of two principal series of the same degree is
principal if the degree of the sum is unchanged. -/
theorem IsPrincipal.add_of_degree_eq
    {b c : Nonpositive ℝ K} (hb : IsPrincipal b) (hc : IsPrincipal c)
    (hcDegree : (c : K⟦ℝ⟧).degree = (b : K⟦ℝ⟧).degree)
    (hsumDegree : ((b + c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
      (b : K⟦ℝ⟧).degree) :
    IsPrincipal (b + c) := by
  have hbDegreeNe : (b : K⟦ℝ⟧).degree ≠ ⊥ := by
    intro hbot
    have hbZero : (b : K⟦ℝ⟧) = 0 := degree_eq_bot.mp hbot
    exact hb.ne_zero (Subtype.ext hbZero)
  let α := (b : K⟦ℝ⟧).degree.unbot hbDegreeNe
  have hbDegree : (b : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) := by
    exact (WithBot.coe_unbot _ hbDegreeNe).symm
  apply add_of_same_degree_coe hb hc hbDegree
  · exact hcDegree.trans hbDegree
  · exact hsumDegree.trans hbDegree

end HahnSeries.Nonpositive
