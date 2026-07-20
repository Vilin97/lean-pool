/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Cases

/-! # IccIcoLems -/


@[expose] public section

open TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


lemma Icc_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n+1) : ℤ), (n + 1 : ℤ)} := by
  ext a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega


lemma trex (f : ℤ → ℂ) (N : ℕ) (hn : 1 ≤ N) : ∑ m ∈ Finset.Icc (-N : ℤ) N, f m =
  f N + f (-N : ℤ) + ∑ m ∈ Finset.Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction N with
  | zero => aesop
  | succ N ih =>
    zify
    rw [Icc_succ, Finset.sum_union]
    · ring_nf
      rw [add_assoc]
      congr
      rw [Finset.sum_pair]
      · ring
      omega
    simp


lemma Icc_sum_even (f : ℤ → ℂ) (hf : ∀ n, f n = f (-n)) (N : ℕ) :
    ∑ m ∈ Finset.Icc (-N : ℤ) N, f m = 2 * ∑ m ∈ Finset.range (N + 1), f m - f 0 := by
  induction N with
  | zero =>
    simp only [CharP.cast_eq_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton,
      zero_add, Finset.range_one]
    ring
  | succ N ih =>
    have := Icc_succ N
    simp only [neg_add_rev, Int.reduceNeg, Nat.cast_add, Nat.cast_one] at *
    rw [this, Finset.sum_union, Finset.sum_pair, ih]
    · nth_rw 2 [Finset.sum_range_succ]
      have HF:= hf (N + 1)
      simp only [neg_add_rev, Int.reduceNeg] at HF
      rw [← HF]
      ring_nf
      norm_cast
    · omega
    simp only [Int.reduceNeg, Finset.disjoint_insert_right, Finset.mem_Icc, le_add_iff_nonneg_left,
      Left.nonneg_neg_iff, Int.reduceLE, add_neg_le_iff_le_add, false_and, not_false_eq_true,
      Finset.disjoint_singleton_right, add_le_iff_nonpos_right, and_false, and_self]



lemma verga2 : Tendsto (fun N : ℕ => Finset.Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)

lemma int_add_abs_self_nonneg (n : ℤ) : 0 ≤ n + |n| := by
  rcases abs_cases n with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

lemma verga : Tendsto (fun N : ℕ => Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  intro x
  refine ⟨x.natAbs + 1, ?_⟩
  simp only [Nat.cast_add, Int.natCast_natAbs, Nat.cast_one, neg_add_rev, Int.reduceNeg,
    Finset.mem_Ico, add_neg_le_iff_le_add]
  exact ⟨le_trans (by omega) (int_add_abs_self_nonneg x), Int.lt_add_one_iff.mpr (le_abs_self x)⟩

lemma fsb (b : ℕ) : Finset.Ico (-(b+1) : ℤ) (b+1) = Finset.Ico (-(b : ℤ)) (b) ∪
    {-((b+1) : ℤ), (b : ℤ)} := by
  ext n
  simp
  omega
