/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Permanent
import Mathlib.Tactic

/-! # Birkhoff -/

open scoped BigOperators

namespace BeyondBethe

/-- Membership in the Birkhoff polytope, stated without bundling the matrix. -/
def IsDoublyStochastic
    {n : Type*} [Fintype n] (X : Matrix n n ℝ) : Prop :=
  Matrix.Nonnegative X ∧
    (∀ i, ∑ j, X i j = 1) ∧
    (∀ j, ∑ i, X i j = 1)

theorem IsDoublyStochastic.nonnegative
    {n : Type*} [Fintype n] {X : Matrix n n ℝ}
    (hX : IsDoublyStochastic X) : Matrix.Nonnegative X :=
  hX.1

theorem IsDoublyStochastic.row_sum
    {n : Type*} [Fintype n] {X : Matrix n n ℝ}
    (hX : IsDoublyStochastic X) (i : n) :
    ∑ j, X i j = 1 :=
  hX.2.1 i

theorem IsDoublyStochastic.col_sum
    {n : Type*} [Fintype n] {X : Matrix n n ℝ}
    (hX : IsDoublyStochastic X) (j : n) :
    ∑ i, X i j = 1 :=
  hX.2.2 j

theorem IsDoublyStochastic.entry_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : IsDoublyStochastic X) (i j : n) :
    X i j ≤ 1 := by
  rw [← hX.row_sum i]
  exact Finset.single_le_sum
    (fun k _ ↦ hX.nonnegative i k) (Finset.mem_univ j)

theorem IsDoublyStochastic.entry_lt_one_of_positive
    {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : IsDoublyStochastic X)
    (hXpos : ∀ i j, 0 < X i j) (hcard : 1 < Fintype.card n)
    (i j : n) :
    X i j < 1 := by
  obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card hcard j
  rw [← hX.row_sum i]
  calc
    X i j < X i j + X i k := lt_add_of_pos_right _ (hXpos i k)
    _ = ∑ l ∈ ({j, k} : Finset n), X i l := by
      rw [Finset.sum_pair hkj.symm]
    _ ≤ ∑ l, X i l := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun l _ _ ↦ hX.nonnegative i l)

/-- Total column mass of two rows. -/
def pairAlpha {n : Type*} (X : Matrix n n ℝ) (r s j : n) : ℝ :=
  X r j + X s j

theorem pairAlpha_nonneg
    {n : Type*} [Fintype n] {X : Matrix n n ℝ}
    (hX : IsDoublyStochastic X) (r s j : n) :
    0 ≤ pairAlpha X r s j := by
  exact add_nonneg (hX.nonnegative r j) (hX.nonnegative s j)

theorem pairAlpha_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : IsDoublyStochastic X)
    {r s : n} (hrs : r ≠ s) (j : n) :
    pairAlpha X r s j ≤ 1 := by
  rw [← hX.col_sum j]
  calc
    pairAlpha X r s j = ∑ i ∈ ({r, s} : Finset n), X i j := by
      simp [pairAlpha, hrs]
    _ ≤ ∑ i, X i j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun i _ _ ↦ hX.nonnegative i j

theorem exists_ne_ne_of_two_lt_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 < Fintype.card ι) (r s : ι) :
    ∃ t, t ≠ r ∧ t ≠ s := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hcard
  by_cases hx : x ≠ r ∧ x ≠ s
  · exact ⟨x, hx⟩
  by_cases hy : y ≠ r ∧ y ≠ s
  · exact ⟨y, hy⟩
  simp only [not_and_or, not_ne_iff] at hx hy
  rcases hx with hxr | hxs <;> rcases hy with hyr | hys
  · exact False.elim (hxy (hxr.trans hyr.symm))
  · refine ⟨z, ?_, ?_⟩
    · exact fun hzr ↦ hxz (hxr.trans hzr.symm)
    · exact fun hzs ↦ hyz (hys.trans hzs.symm)
  · refine ⟨z, ?_, ?_⟩
    · exact fun hzr ↦ hyz (hyr.trans hzr.symm)
    · exact fun hzs ↦ hxz (hxs.trans hzs.symm)
  · exact False.elim (hxy (hxs.trans hys.symm))

theorem pairAlpha_lt_one_of_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    (hXpos : ∀ i j, 0 < X i j) (hcard : 2 < Fintype.card ι)
    {r s : ι} (hrs : r ≠ s) (j : ι) :
    pairAlpha X r s j < 1 := by
  obtain ⟨t, htr, hts⟩ := exists_ne_ne_of_two_lt_card hcard r s
  calc
    pairAlpha X r s j < pairAlpha X r s j + X t j :=
      lt_add_of_pos_right _ (hXpos t j)
    _ = ∑ i ∈ ({r, s, t} : Finset ι), X i j := by
      simp [pairAlpha, hrs, Ne.symm htr, Ne.symm hts]
      ring
    _ ≤ ∑ i, X i j := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ ↦ hX.nonnegative i j)
    _ = 1 := hX.col_sum j

theorem sum_pairAlpha
    {n : Type*} [Fintype n]
    {X : Matrix n n ℝ} (hX : IsDoublyStochastic X) (r s : n) :
    ∑ j, pairAlpha X r s j = 2 := by
  simp_rw [pairAlpha, Finset.sum_add_distrib, hX.row_sum]
  norm_num

end BeyondBethe
