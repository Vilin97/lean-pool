/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Hom.Monoid
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Transfer
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.Round

/-!
# Additive compatibility of the surreal Conway normal form

This module proves that the Conway normal-form order equivalence preserves addition. The argument
follows the additive part of CombinatorialGames PR #263 and fills its unfinished proof obligations
against the pinned dependency. The construction is based on pages 429–431 of Siegel.
-/

universe u

public noncomputable section

namespace Surreal

open ArchimedeanClass Order Set SurrealHahnSeries

namespace PartialSum

variable {x y : Surreal} (h : x.support ⊆ Ioi y.wlog)

/-- The Conway series of `x`, regarded as a partial sum of `x + y` when every exponent of `x`
strictly exceeds the leading exponent of `y`. -/
def ofAdd (x y : Surreal) (h : x.support ⊆ Ioi y.wlog) : PartialSum (x + y) where
  carrier := x.toHahnSeries
  term_eq_leadingTerm_sub {j} hj := by
    rw [← leadingTerm_sub_truncIdx, toSurreal_toHahnSeries]
    obtain rfl | hy' := eq_or_ne y 0
    · simp
    rw [add_sub_right_comm, leadingTerm_add_eq_left]
    nth_rw 1 [← toSurreal_toHahnSeries x]
    rw [vlt_def, ← mk_leadingTerm, leadingTerm_sub_truncIdx, mk_term hj, ← vlt_def,
      ← wlog_lt_wlog_iff hy' (wpow_ne_zero _), wlog_wpow]
    apply h
    rw [← support_toHahnSeries]
    exact (x.toHahnSeries.exp ⟨j, hj⟩).2

@[simp]
theorem carrier_ofAdd : (ofAdd x y h).carrier = x.toHahnSeries :=
  (rfl)

theorem length_ofAdd : (ofAdd x y h).length = x.length := by
  rw [length_eq_carrier_length, carrier_ofAdd, length_toHahnSeries]

theorem truncIdx_top_add_length {x y : Surreal}
    (h : x.support ⊆ Ioi y.wlog) :
    (⊤ : PartialSum (x + y)).truncIdx x.length = ofAdd x y h :=
  by
    rw [← length_ofAdd h]
    exact PartialSum.truncIdx_length_of_le (y := ofAdd x y h) le_top

@[simp]
theorem term_succ_ofAdd_length {x y : Surreal} (h : x.support ⊆ Ioi y.wlog) :
    (succ (ofAdd x y h)).carrier.term x.length = y.leadingTerm := by
  rw [← length_ofAdd h, term_succ_length, carrier_ofAdd,
    toSurreal_toHahnSeries, add_sub_cancel_left]

end PartialSum

private theorem truncIdx_add_length_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) : (x + y).toHahnSeries.truncIdx x.length = x := by
  have h := congrArg PartialSum.carrier (PartialSum.truncIdx_top_add_length hx)
  have h' := congrArg SurrealHahnSeries.toSurreal h
  simpa using h'

private theorem le_length_add_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) : x.length ≤ (x + y).length := by
  conv_lhs => rw [← truncIdx_add_length_of_subset hx]
  simp

open PartialSum in
private theorem lt_length_add_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) (hy : y ≠ 0) : x.length < (x + y).length := by
  apply (le_length_add_of_subset hx).lt_of_ne
  rw [← PartialSum.length_ofAdd hx, ← PartialSum.length_top]
  rw [ne_eq, length_inj]
  apply_fun carrier
  simpa

private theorem term_add_length_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) (hy : y ≠ 0) :
    (x + y).toHahnSeries.term x.length = y.leadingTerm := by
  have hl := lt_length_add_of_subset hx hy
  have htop : x.length < (⊤ : PartialSum (x + y)).length := by
    simpa using hl
  have hbase : PartialSum.ofAdd x y hx < (⊤ : PartialSum (x + y)) := by
    rw [← PartialSum.length_lt_length, PartialSum.length_ofAdd,
      PartialSum.length_top]
    exact hl
  have hs : x.length < (succ (PartialSum.ofAdd x y hx)).length := by
    rw [← PartialSum.length_ofAdd hx]
    exact lt_succ_of_not_isMax hbase.not_isMax
  calc
    (x + y).toHahnSeries.term x.length =
        (⊤ : PartialSum (x + y)).carrier.term x.length :=
      congrArg (fun q : SurrealHahnSeries ↦ q.term x.length)
        (PartialSum.carrier_top (x + y)).symm
    _ = (succ (PartialSum.ofAdd x y hx)).carrier.term x.length :=
      PartialSum.term_congr htop hs
    _ = y.leadingTerm := PartialSum.term_succ_ofAdd_length hx

private theorem exp_add_length_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) (hy : y ≠ 0) :
    ↑((x + y).toHahnSeries.exp ⟨x.length, by
      simpa using lt_length_add_of_subset hx hy⟩) = y.wlog := by
  rw [← SurrealHahnSeries.wlog_term, term_add_length_of_subset hx hy,
    wlog_leadingTerm]

open PartialSum in
private theorem trunc_add_of_subset {x y i : Surreal}
    (hx : x.support ⊆ Ioi i) (hy : y ≤ᵥ ω^ i) : (x + y).trunc i = x := by
  obtain rfl | hy' := eq_or_ne y 0
  · rw [add_zero]
    exact trunc_eq_self hx
  have hy'' : y.wlog ≤ i := by
    simpa using wlog_le_wlog_of_vle hy' hy
  have hx' : x.support ⊆ Ioi y.wlog := hx.trans (by simpa)
  have hl := lt_length_add_of_subset hx' hy'
  have hl' : x.length < (x + y).toHahnSeries.length := by
    simpa using hl
  conv_rhs => rw [← truncIdx_add_length_of_subset hx']
  rw [truncIdx_of_lt hl']
  rw [SurrealHahnSeries.toSurreal_trunc]
  rw [toSurreal_toHahnSeries]
  let e : Surreal := ↑((x + y).toHahnSeries.exp ⟨x.length, hl'⟩)
  have he : e = y.wlog := by
    exact exp_add_length_of_subset hx' hy'
  apply (trunc_eq_trunc (he.le.trans hy'') _).symm
  intro k hek hki
  apply notMem_support_iff.mp
  intro hk
  have hkTrunc : k ∈ ((x + y).trunc e).support := by
    rw [support_trunc]
    exact ⟨hk, hek⟩
  have htrunc : (x + y).trunc e = x := by
    nth_rw 1 [← toSurreal_toHahnSeries (x + y)]
    rw [← SurrealHahnSeries.toSurreal_trunc, ← truncIdx_of_lt hl',
      truncIdx_add_length_of_subset hx']
  have hkx : k ∈ x.support := by
    rwa [htrunc] at hkTrunc
  exact (not_lt_of_ge hki) (hx hkx)

private theorem coeff_add_of_subset {x y i : Surreal}
    (hx : x.support ⊆ Ioi i) (hy : y ≤ᵥ ω^ i) :
    (x + y).coeff i = stdPart (y / ω^ i) := by
  obtain rfl | hy' := eq_or_ne y 0
  · simp only [add_zero, zero_div, stdPart_zero]
    apply notMem_support_iff.mp
    intro hi
    exact (lt_irrefl i) (hx hi)
  have hylog : y.wlog ≤ i := by
    simpa using wlog_le_wlog_of_vle hy' hy
  obtain heq | hlt := hylog.eq_or_lt
  · subst i
    have hexp := exp_add_length_of_subset hx hy'
    rw [← coeff_toHahnSeries, ← hexp, SurrealHahnSeries.coeff_exp,
      ← SurrealHahnSeries.leadingCoeff_term,
      term_add_length_of_subset hx hy', leadingCoeff_leadingTerm, leadingCoeff,
      hexp]
  · have hxlog : x.support ⊆ Ioi y.wlog := fun _ hk ↦ hlt.trans (hx hk)
    have htrunc : (x + y).trunc y.wlog = x :=
      trunc_add_of_subset hxlog (wpow_wlog_veq hy').symm.1
    have hcoeff : (x + y).coeff i = 0 := by
      apply notMem_support_iff.mp
      intro hi
      have hiTrunc : i ∈ ((x + y).trunc y.wlog).support := by
        rw [support_trunc]
        exact ⟨hi, hlt⟩
      rw [htrunc] at hiTrunc
      exact (lt_irrefl i) (hx hiTrunc)
    rw [hcoeff]
    symm
    rw [stdPart_eq_zero]
    apply ne_of_gt
    rw [ArchimedeanClass.mk_div, LinearOrderedAddCommGroupWithTop.sub_pos]
    left
    apply vlt_def.mp
    rw [← wlog_lt_wlog_iff hy' (wpow_ne_zero _), wlog_wpow]
    exact hlt

private theorem sub_trunc_vle_wpow (x i : Surreal) : x - x.trunc i ≤ᵥ ω^ i := by
  let s := x.toHahnSeries
  obtain ⟨j, hj⟩ := SurrealHahnSeries.trunc_mem_range_truncIdx s i
  have hsx : s.toSurreal = x := by
    simp [s]
  have htr : (s.trunc i).toSurreal = x.trunc i := by
    rw [SurrealHahnSeries.toSurreal_trunc, hsx]
  have hlead : (x - x.trunc i).leadingTerm = s.term j := by
    calc
      (x - x.trunc i).leadingTerm =
          (s.toSurreal - (s.truncIdx j).toSurreal).leadingTerm := by
        rw [hsx, hj, htr]
      _ = s.term j := SurrealHahnSeries.leadingTerm_sub_truncIdx
  obtain hjlen | hjlen := lt_or_ge j s.length
  · have hexpLe : ↑(s.exp ⟨j, hjlen⟩) ≤ i := by
      by_contra hle
      have hiExp : i < ↑(s.exp ⟨j, hjlen⟩) := lt_of_not_ge hle
      have hmem : ↑(s.exp ⟨j, hjlen⟩) ∈ (s.trunc i).support := by
        rw [SurrealHahnSeries.support_trunc]
        exact ⟨(s.exp ⟨j, hjlen⟩).2, hiExp⟩
      rw [← hj, SurrealHahnSeries.support_truncIdx, dif_pos hjlen] at hmem
      have hfalse : ↑(s.exp ⟨j, hjlen⟩) < ↑(s.exp ⟨j, hjlen⟩) := by
        simpa using hmem.2
      exact (lt_irrefl _) hfalse
    have hrem : x - x.trunc i ≠ 0 := by
      intro hzero
      have htermNe : s.term j ≠ 0 := by
        rw [ne_eq, SurrealHahnSeries.term_eq_zero, not_le]
        exact hjlen
      apply htermNe
      rw [← hlead, hzero, leadingTerm_zero]
    rw [← wlog_le_wlog_iff hrem (wpow_ne_zero _), wlog_wpow,
      ← wlog_leadingTerm, hlead, SurrealHahnSeries.wlog_term hjlen]
    exact hexpLe
  · have hzero : x - x.trunc i = 0 := by
      rw [← leadingTerm_eq_zero, hlead, SurrealHahnSeries.term_of_le hjlen]
    simp [hzero]

/-- A Conway coefficient is the standard part of the remainder after truncation, divided by its
corresponding monomial. -/
theorem coeff_eq_stdPart {x i : Surreal} :
    x.coeff i = stdPart ((x - x.trunc i) / ω^ i) := by
  conv_lhs => rw [← add_sub_cancel (x.trunc i) x]
  apply coeff_add_of_subset
  · simp
  · exact sub_trunc_vle_wpow x i

theorem support_subset_of_round_eq {x y : Surreal} (hx : x.round y = x) (hy : 0 < y) :
    x.support ⊆ Ici y.wlog := by
  intro z hzy
  rw [mem_Ici]
  contrapose! hzy
  intro hz
  have hz' : z ∈ x.toHahnSeries.support := by
    simpa using hz
  obtain ⟨i, rfl⟩ := SurrealHahnSeries.eq_exp_of_mem_support hz'
  have H : ArchimedeanClass.mk y < .mk (x - x.toHahnSeries.truncIdx i) := by
    nth_rw 1 [← toSurreal_toHahnSeries x]
    conv_rhs => rw [← mk_leadingTerm, SurrealHahnSeries.leadingTerm_sub_truncIdx,
      SurrealHahnSeries.mk_term i.2]
    rw [← vlt_def, ← wlog_lt_wlog_iff (by simp) hy.ne']
    simpa
  refine (@birthday_round_le x (x.toHahnSeries.truncIdx i) y ⟨?_, ?_⟩).not_gt ?_
  · rw [sub_lt_comm]
    exact lt_of_mk_lt_mk_of_nonneg H hy.le
  · rw [← sub_lt_iff_lt_add']
    apply lt_of_mk_lt_mk_of_nonneg _ hy.le
    rwa [mk_sub_comm]
  · apply (SurrealHahnSeries.birthday_truncIdx_lt i.2).trans_eq
    simp [hx]

theorem support_subset_of_round_wpow_eq {x y : Surreal} (h : x.round (ω^ y) = x) :
    x.support ⊆ Ici y := by
  simpa using support_subset_of_round_eq h

theorem eq_round_of_support_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) (hy : 0 < y) : x.round y = x := by
  apply round_eq_of_forall_birthday_le
  · simpa
  · intro w hw
    convert SurrealHahnSeries.birthday_trunc_le w.toHahnSeries y.wlog
    · symm
      rw [SurrealHahnSeries.toSurreal_trunc, toSurreal_toHahnSeries]
      calc
        w.trunc y.wlog = (x + (w - x)).trunc y.wlog := by
          congr 2
          abel
        _ = x := trunc_add_of_subset hx <| by
          have habs : |w - x| < y := by
            rw [abs_lt]
            constructor <;> linarith [hw.1, hw.2]
          apply ValuativeRel.vle_trans _ (wpow_wlog_veq hy.ne').symm.1
          rw [vle_def]
          exact ArchimedeanClass.mk_le_mk_of_abs (by simpa [abs_of_pos hy] using habs.le)
    · exact (toSurreal_toHahnSeries w).symm

theorem eq_round_wpow_of_support_subset {x y : Surreal} (hx : x.support ⊆ Ioi y) :
    x.round (ω^ y) = x :=
  eq_round_of_support_subset (by simpa) (by simp)

private theorem support_add_subset_Ioi {x y z : Surreal}
    (hx : x.support ⊆ Ioi z) (hy : y.support ⊆ Ioi z) : (x + y).support ⊆ Ioi z := by
  apply (support_subset_of_round_wpow_eq (y := !{{z} | x.support ∪ y.support}) _).trans
  · aesop
  · apply round_add_of_eq
    all_goals
      refine eq_round_wpow_of_support_subset fun w hw ↦ ?_
      aesop

/-- The Conway normal-form order equivalence preserves addition. -/
@[simp]
theorem toHahnSeries_add (x y : Surreal) :
    (x + y).toHahnSeries = x.toHahnSeries + y.toHahnSeries := by
  ext i
  rw [coeff_toHahnSeries, SurrealHahnSeries.coeff_add_apply]
  trans ((x.trunc i + y.trunc i) +
      ((x - x.trunc i) + (y - y.trunc i))).coeff i
  · abel_nf
  · rw [coeff_add_of_subset, add_div, stdPart_add]
    · rw [coeff_toHahnSeries x, coeff_toHahnSeries y, coeff_eq_stdPart,
        coeff_eq_stdPart]
    · rw [ArchimedeanClass.mk_div]
      obtain heq | hlt := (vle_def.mp (sub_trunc_vle_wpow x i)).eq_or_lt
      · rw [heq]
        exact LinearOrderedAddCommGroupWithTop.sub_self_nonneg
      · exact (LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hlt)).le
    · rw [ArchimedeanClass.mk_div]
      obtain heq | hlt := (vle_def.mp (sub_trunc_vle_wpow y i)).eq_or_lt
      · rw [heq]
        exact LinearOrderedAddCommGroupWithTop.sub_self_nonneg
      · exact (LinearOrderedAddCommGroupWithTop.sub_pos.mpr (Or.inl hlt)).le
    · apply support_add_subset_Ioi <;> simp
    · apply ValuativeRel.vle_add <;> exact sub_trunc_vle_wpow _ _

/-- Conway coefficients are additive. -/
@[simp]
theorem coeff_add (x y : Surreal) : (x + y).coeff = x.coeff + y.coeff := by
  rw [← coeff_toHahnSeries, toHahnSeries_add,
    SurrealHahnSeries.coeff_add, coeff_toHahnSeries, coeff_toHahnSeries]

/-- The Conway support of a sum is contained in the union of the two source supports. -/
theorem support_add_subset {x y : Surreal} :
    (x + y).support ⊆ x.support ∪ y.support := by
  intro i hi
  have hi' : i ∈ (x.toHahnSeries + y.toHahnSeries).support := by
    rw [← toHahnSeries_add]
    simpa only [support_toHahnSeries] using hi
  have hout := SurrealHahnSeries.support_add_subset hi'
  simpa only [support_toHahnSeries] using hout

/-- The Conway normal form as an order-preserving additive equivalence. -/
def toHahnSeriesOrderAddMonoidIso : Surreal ≃+o SurrealHahnSeries where
  toEquiv := toHahnSeriesOrderIso.toEquiv
  map_add' := toHahnSeries_add
  map_le_map_iff' := toHahnSeries_le_toHahnSeries_iff

@[simp]
theorem toHahnSeriesOrderAddMonoidIso_apply (x : Surreal) :
    toHahnSeriesOrderAddMonoidIso x = x.toHahnSeries :=
  (rfl)

@[simp]
theorem toHahnSeriesOrderAddMonoidIso_symm_apply (x : SurrealHahnSeries) :
    toHahnSeriesOrderAddMonoidIso.symm x = x.toSurreal :=
  (rfl)

/-- The Conway normal form of one is the singleton series at exponent zero. -/
@[simp]
theorem toHahnSeries_one : (1 : Surreal).toHahnSeries = .single 0 1 := by
  simpa using toHahnSeries_realCast (1 : ℝ)

/-- The Conway coefficient function of one is supported at exponent zero. -/
@[simp]
theorem coeff_one : (1 : Surreal).coeff = Pi.single 0 1 := by
  rw [← coeff_toHahnSeries, toHahnSeries_one, SurrealHahnSeries.coeff_single]

/-- Negation of a surreal number agrees with coefficientwise negation of its Conway normal form. -/
@[simp]
theorem toHahnSeries_neg (x : Surreal) : (-x).toHahnSeries = -x.toHahnSeries := by
  apply eq_neg_of_add_eq_zero_left
  rw [← toHahnSeries_add, neg_add_cancel, toHahnSeries_zero]

/-- Conway coefficients commute with negation. -/
@[simp]
theorem coeff_neg (x : Surreal) : (-x).coeff = -x.coeff := by
  rw [← coeff_toHahnSeries, toHahnSeries_neg,
    SurrealHahnSeries.coeff_neg, coeff_toHahnSeries]

/-- Addition of surreal Hahn series agrees with addition of their surreal values. -/
@[simp]
theorem _root_.SurrealHahnSeries.toSurreal_add (x y : SurrealHahnSeries) :
    (x + y).toSurreal = x.toSurreal + y.toSurreal :=
  toHahnSeriesOrderAddMonoidIso.symm.map_add x y

/-- Negation of a surreal Hahn series agrees with negation of its surreal value. -/
@[simp]
theorem _root_.SurrealHahnSeries.toSurreal_neg (x : SurrealHahnSeries) :
    (-x).toSurreal = -x.toSurreal :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← SurrealHahnSeries.toSurreal_add, neg_add_cancel,
      SurrealHahnSeries.toSurreal_zero]

end Surreal
