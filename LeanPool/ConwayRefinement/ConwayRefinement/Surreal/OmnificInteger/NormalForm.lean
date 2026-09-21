/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
/-
Partly adapted and modified from the Apache-2.0-licensed CombinatorialGames PR #317:
https://github.com/vihdzp/combinatorial-games/pull/317
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormAdd
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Basic

/-!
# Conway normal forms of omnific integers

This module proves Conway's normal-form characterization of the omnific integers: a surreal is an
omnific integer exactly when its Conway support consists of nonnegative exponents and its constant
coefficient is an integer. The proof uses the fixed-point definition from
`ConwayRefinement.Surreal.OmnificInteger.Basic` and the Conway normal-form rounding
criterion.

The characterization is Theorem 31 of *On Numbers and Games* and is the presentation of `Oz`
recalled in LM24, Section 1.1.
-/

universe u

public noncomputable section

namespace Surreal

open Set

/-- A positive omnific integer is at least one. -/
theorem IsOmnificInteger.one_le_iff_pos {x : Surreal.{u}}
    (h : IsOmnificInteger x) : 1 ≤ x ↔ 0 < x where
  mp := zero_lt_one.trans_le
  mpr hx := by
    rw [isOmnificInteger_iff_round_one] at h
    by_contra hnot
    have hxle : x ≤ 1 := le_of_not_ge hnot
    have hzero : 0 ∈ Ioo (x - 1) (x + 1) := by
      constructor <;> linarith
    rw [round_of_zero_mem hzero] at h
    exact hx.ne h

/-- An omnific integer below one is nonpositive. -/
theorem IsOmnificInteger.lt_one_iff_nonpos {x : Surreal.{u}}
    (h : IsOmnificInteger x) : x < 1 ↔ x ≤ 0 := by
  rw [← not_iff_not]
  simpa only [not_le, not_lt] using h.one_le_iff_pos

/-- An omnific integer strictly between negative one and one is zero. -/
theorem IsOmnificInteger.eq_zero_of_mem_Ioo_neg_one_one {x : Surreal.{u}}
    (hx : IsOmnificInteger x) (hbound : x ∈ Ioo (-1) 1) : x = 0 := by
  have hxNonpos : x ≤ 0 := hx.lt_one_iff_nonpos.mp hbound.2
  have hnegNonpos : -x ≤ 0 := hx.neg.lt_one_iff_nonpos.mp (by linarith [hbound.1])
  linarith

/-- Two omnific integers whose difference is strictly between negative one and one are equal. -/
theorem IsOmnificInteger.eq_of_sub_mem_Ioo_neg_one_one {x y : Surreal.{u}}
    (hx : IsOmnificInteger x) (hy : IsOmnificInteger y)
    (hbound : x - y ∈ Ioo (-1) 1) : x = y := by
  have hzero := (hx.sub hy).eq_zero_of_mem_Ioo_neg_one_one hbound
  linarith

/-- A real number is an omnific integer exactly when it is the image of an integer. -/
@[simp]
theorem isOmnificInteger_realCast_iff {r : ℝ} :
    IsOmnificInteger (r : Surreal.{u}) ↔ r ∈ range ((↑) : ℤ → ℝ) where
  mpr := by
    rintro ⟨n, rfl⟩
    simpa only [Real.toSurreal_intCast] using IsOmnificInteger.intCast n
  mp h := by
    rw [← Int.fract_eq_zero_iff]
    apply (Int.fract_nonneg r).antisymm'
    rw [← Real.toSurreal_le_iff, Real.toSurreal_zero,
      ← IsOmnificInteger.lt_one_iff_nonpos]
    · exact_mod_cast Int.fract_lt_one r
    · rw [Int.fract, Real.toSurreal_sub]
      apply h.sub
      simpa only [Real.toSurreal_intCast] using IsOmnificInteger.intCast ⌊r⌋

/-- If a Conway support is nonnegative, removing its positive truncation leaves its real constant
coefficient. -/
theorem sub_trunc_zero_eq_realCast_of_support_subset_Ici {x : Surreal.{u}}
    (hx : x.support ⊆ Ici 0) :
    x - x.trunc 0 = (x.coeff 0 : Surreal) := by
  rw [← toHahnSeries_inj]
  ext i
  simp only [sub_eq_add_neg, toHahnSeries_add, toHahnSeries_neg,
    SurrealHahnSeries.coeff_add_apply, SurrealHahnSeries.coeff_neg,
    Pi.neg_apply, coeff_toHahnSeries, toHahnSeries_trunc,
    SurrealHahnSeries.coeff_trunc, toHahnSeries_realCast,
    SurrealHahnSeries.coeff_single]
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have hcoeff : x.coeff i = 0 := by
      rw [← notMem_support_iff]
      exact fun hmem ↦ (not_le_of_gt hi) (hx hmem)
    simp [hcoeff, hi.ne]
  · simp
  · simp [hi, hi.ne']

/-- Conway's normal-form characterization: `x` is an omnific integer exactly when all exponents
in its support are nonnegative and its coefficient at exponent zero is an integer. -/
theorem isOmnificInteger_iff_normalForm {x : Surreal.{u}} :
    IsOmnificInteger x ↔
      x.support ⊆ Ici 0 ∧ x.coeff 0 ∈ range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hx
    have hround : x.round 1 = x := isOmnificInteger_iff_round_one.mp hx
    have hsupp : x.support ⊆ Ici 0 := by
      simpa only [wlog_one] using support_subset_of_round_eq hround zero_lt_one
    refine ⟨hsupp, ?_⟩
    rw [← isOmnificInteger_realCast_iff]
    rw [← sub_trunc_zero_eq_realCast_of_support_subset_Ici hsupp]
    apply hx.sub
    rw [isOmnificInteger_iff_round_one]
    apply eq_round_of_support_subset
    · simpa only [wlog_one, support_trunc] using
        (inter_subset_right : x.support ∩ Ioi 0 ⊆ Ioi 0)
    · exact zero_lt_one
  · rintro ⟨hsupp, hcoeff⟩
    have htrunc : IsOmnificInteger (x.trunc 0) := by
      rw [isOmnificInteger_iff_round_one]
      apply eq_round_of_support_subset
      · simpa only [wlog_one, support_trunc] using
          (inter_subset_right : x.support ∩ Ioi 0 ⊆ Ioi 0)
      · exact zero_lt_one
    have hconstant : IsOmnificInteger (x.coeff 0 : Surreal) :=
      isOmnificInteger_realCast_iff.mpr hcoeff
    rw [← sub_add_cancel x (x.trunc 0),
      sub_trunc_zero_eq_realCast_of_support_subset_Ici hsupp]
    exact hconstant.add htrunc

end Surreal
