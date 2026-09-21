/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Projection-valued measures

This file defines real projection-valued measures through strong-operator countable additivity
and proves monotonicity of their associated scalar quadratic forms.
-/

open Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A projection-valued measure on `ℝ`, countably additive in the strong operator topology.
Laws hold for measurable sets only. -/
structure PVM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  proj : Set ℝ → (E →L[ℂ] E)
  isOrthogonalProjection : ∀ S, MeasurableSet S →
    IsSelfAdjoint (proj S) ∧ IsIdempotentElem (proj S)
  empty : proj ∅ = 0
  univ : proj Set.univ = 1
  inter : ∀ S T, MeasurableSet S → MeasurableSet T →
    proj (S ∩ T) = proj S * proj T
  countably_additive : ∀ (S : ℕ → Set ℝ),
    (∀ i, MeasurableSet (S i)) →
    Pairwise (Disjoint on S) →
    ∀ x, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, proj (S i) x)
      Filter.atTop (nhds (proj (⋃ i, S i) x))

/-- Inclusion of measurable sets makes the real scalar quadratic form of a PVM projection
monotone. -/
theorem PVM.monotone (E_pvm : PVM E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (h : S ⊆ T) (x : E) :
    (@inner ℂ E _ (E_pvm.proj S x) x).re ≤ (@inner ℂ E _ (E_pvm.proj T x) x).re :=
  by
    have hST : S ∩ T = S := Set.inter_eq_left.mpr h
    have hTS : T ∩ S = S := Set.inter_eq_right.mpr h
    have hprojST : E_pvm.proj S * E_pvm.proj T = E_pvm.proj S := by
      rw [← E_pvm.inter S T hS hT, hST]
    have hprojTS : E_pvm.proj T * E_pvm.proj S = E_pvm.proj S := by
      rw [← E_pvm.inter T S hT hS, hTS]
    have hdiff_idempotent :
        IsIdempotentElem (E_pvm.proj T - E_pvm.proj S) :=
      (E_pvm.isOrthogonalProjection S hS).2.sub
        (E_pvm.isOrthogonalProjection T hT).2 hprojST hprojTS
    have hdiff_selfAdjoint :
        IsSelfAdjoint (E_pvm.proj T - E_pvm.proj S) :=
      (E_pvm.isOrthogonalProjection T hT).1.sub
        (E_pvm.isOrthogonalProjection S hS).1
    have hnonneg :=
      ((ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        hdiff_idempotent).mpr hdiff_selfAdjoint).re_inner_nonneg_left x
    rw [sub_apply, inner_sub_left, map_sub, sub_nonneg] at hnonneg
    exact hnonneg

/-- A PVM sends the union of two disjoint measurable sets to the sum of their projections. -/
theorem PVM.proj_union (E_pvm : PVM E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    E_pvm.proj (S ∪ T) = E_pvm.proj S + E_pvm.proj T := by
  let sets : ℕ → Set ℝ
    | 0 => S
    | 1 => T
    | _ => ∅
  have hmeas : ∀ i, MeasurableSet (sets i) := by
    rintro (_ | (_ | _))
    · exact hS
    · exact hT
    · exact MeasurableSet.empty
  have hpairwise : Pairwise (Disjoint on sets) := by
    rintro i j hij
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j)
    · exact (hij rfl).elim
    · exact hdisj
    · exact disjoint_bot_right
    · exact hdisj.symm
    · exact (hij rfl).elim
    · exact disjoint_bot_right
    · exact disjoint_bot_left
    · exact disjoint_bot_left
    · exact disjoint_bot_left
  have hunion : (⋃ i, sets i) = S ∪ T := by
    ext t
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      rcases i with _ | (_ | i)
      · exact Set.mem_union_left T hi
      · exact Set.mem_union_right S hi
      · exact False.elim hi
    · intro ht
      rcases ht with ht | ht
      · rw [Set.mem_iUnion]
        exact ⟨0, ht⟩
      · rw [Set.mem_iUnion]
        exact ⟨1, ht⟩
  apply ContinuousLinearMap.ext
  intro x
  have hlim := E_pvm.countably_additive sets hmeas hpairwise x
  rw [hunion] at hlim
  have hsets (n : ℕ) (hn : 2 ≤ n) : sets n = ∅ := by
    rcases n with _ | (_ | n)
    · omega
    · omega
    · rfl
  have hsum : ∀ n ≥ 2,
      (∑ i ∈ Finset.range n, E_pvm.proj (sets i) x) =
        E_pvm.proj S x + E_pvm.proj T x := by
    intro n hn
    obtain ⟨k, rfl⟩ := exists_add_of_le hn
    induction k with
    | zero =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        change 0 + E_pvm.proj S x + E_pvm.proj T x = _
        rw [zero_add]
    | succ k ih =>
        rw [show 2 + (k + 1) = (2 + k) + 1 by omega, Finset.sum_range_succ,
          ih (by omega), hsets (2 + k) (by omega)]
        rw [E_pvm.empty, zero_apply, add_zero]
  have hconst : Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, E_pvm.proj (sets i) x)
      Filter.atTop (nhds (E_pvm.proj S x + E_pvm.proj T x)) :=
    tendsto_atTop_of_eventually_const hsum
  exact tendsto_nhds_unique hlim hconst

/-- A PVM sends a finite pairwise-disjoint union of measurable sets to the sum of their
projections. -/
theorem PVM.proj_biUnion_finset {I : Type*} (E_pvm : PVM E)
    (s : Finset I) (A : I → Set ℝ) (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hpair : (↑s : Set I).PairwiseDisjoint A) :
    E_pvm.proj (⋃ i ∈ (↑s : Set I), A i) = ∑ i ∈ s, E_pvm.proj (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, Set.biUnion_empty, Finset.sum_empty, E_pvm.empty]
  | @insert a s ha ih =>
      have hpair_s : (↑s : Set I).PairwiseDisjoint A :=
        Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert a s)) hpair
      have hmeas_s : ∀ i ∈ s, MeasurableSet (A i) :=
        fun i hi => hmeas i (Finset.mem_insert_of_mem hi)
      have hmeas_a : MeasurableSet (A a) :=
        hmeas a (Finset.mem_insert_self a s)
      have hmeas_union : MeasurableSet (⋃ i ∈ (↑s : Set I), A i) :=
        MeasurableSet.biUnion s.countable_toSet (fun i hi => hmeas_s i hi)
      have hadisj : Disjoint (A a) (⋃ i ∈ (↑s : Set I), A i) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        rw [Set.disjoint_iUnion_right]
        intro hi
        exact hpair (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (fun hai => ha (hai ▸ hi))
      rw [Finset.coe_insert, Set.biUnion_insert,
        E_pvm.proj_union hmeas_a hmeas_union hadisj,
        Finset.sum_insert ha, ih hmeas_s hpair_s]
