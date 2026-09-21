/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib.Tactic
import Mathlib.Topology.Connected.Basic

/-!
# ClosureOverlap

Supporting results for the classification of compact one-dimensional manifolds.
-/

open Set TopologicalSpace

universe u
variable {α : Type u}
variable {X : Type u} [TopologicalSpace X]
variable {U V : Set X}

lemma nonempty_closure_inter_diff
  (hVconn : IsConnected V) (hUopen : IsOpen U) (hVopen : IsOpen V)
  (hUV : (U ∩ V).Nonempty) (hVU : (V \ U).Nonempty) :
  ((closure U) ∩ (V \ U)).Nonempty := by
  -- prove by contradiction that `closure U ∩ (V \ U)` can't be empty.
  by_contra h
  push Not at h
  let A := U ∩ V
  let B := V \ U
  have hVconn' : IsPreconnected (V : Set X) := IsConnected.isPreconnected hVconn
  have openA : IsOpen (A : Set X) := IsOpen.inter hUopen hVopen
  have openB : IsOpen (B : Set X) := by
    have : (V \ U) = (V \ (closure U)) := by
      ext x
      simp only [mem_sdiff, and_congr_right_iff]
      intro hv
      constructor
      · intro hu
        have : x ∈ V \ U := mem_sdiff_of_mem hv hu
        by_contra hcu
        have : x ∈ closure U ∩ (V \ U) := by exact mem_inter hcu this
        rw [h] at this
        exact this
      · intro hcu
        exact notMem_of_notMem_closure hcu
    dsimp [B] -- this is needed?
    rw [this]
    exact IsOpen.sdiff hVopen isClosed_closure
  have coverAB : V ⊆ A ∪ B := by
    rintro x hx
    simp only [mem_union]
    by_cases hxU : x ∈ U
    · left
      exact mem_inter hxU hx
    · right
      exact mem_sdiff_of_mem hx hxU
  have nonemptyVA : (V ∩ A).Nonempty := by
    have : (V ∩ (U ∩ V)) = U ∩ V := by
      simp only [inter_eq_right, inter_subset_right]
    rw [this]
    exact hUV
  have nonemptyVB : (V ∩ B).Nonempty := by
    have : (V ∩ (V \ U)) = (V \ U) := by
      simp only [inter_eq_right]
      exact sdiff_subset
    rw [this]
    exact hVU
  have disjointAB : A ∩ B = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hx
    apply notMem_sdiff_of_mem
    exact mem_of_mem_inter_left hx
  have nonemptyVAB : (V ∩ (A ∩ B)).Nonempty := hVconn' A B openA openB coverAB nonemptyVA nonemptyVB
  rw [disjointAB] at nonemptyVAB
  simp only [inter_empty, Set.not_nonempty_empty] at nonemptyVAB
