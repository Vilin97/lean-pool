/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMClassification
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrandEndpointNegative

/-!
# Endpoint-aware classification for Theorem 3.9

The two core vertices of a banana have one coordinate presentation on every
strand.  The paper's phrase `α = β` is therefore not an invariant condition
when a mark is an endpoint.  This file states the corrected theorem directly
for the two marked *vertices*.  The exceptional alternatives retain their
coordinate descriptions only for genuinely interior marks.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The endpoint-aware exceptional alternatives in corrected Theorem 3.9.
The first three clauses are the same-strand endpoint cases, stated as vertex
equalities.  The final clause is the corrected interior classification. -/
def NSMForBananaException {g : ℕ} (B : Banana g) (u v : B.graph.V) : Prop :=
    (u = leftEndpoint B ∧ v = rightEndpoint B) ∨
    (u = rightEndpoint B ∧ v = leftEndpoint B) ∨
    (∃ (α : Fin (g + 1)) (p : B.PathPosition α), B.IsInteriorPosition α p ∧
      ((u = leftEndpoint B ∧ v = strandVertex B α p ∧ p.val + 1 = B.length α) ∨
       (u = rightEndpoint B ∧ v = strandVertex B α p ∧ p.val = 1) ∨
       (v = leftEndpoint B ∧ u = strandVertex B α p ∧ p.val + 1 = B.length α) ∨
       (v = rightEndpoint B ∧ u = strandVertex B α p ∧ p.val = 1))) ∨
    (∃ (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β),
      B.IsInteriorPosition α i ∧ B.IsInteriorPosition β j ∧
      u = strandVertex B α i ∧ v = strandVertex B β j ∧
      NSMForBananaInteriorException B α β i j)

/-- TeX label: `thm-NSMForBanana` (Theorem 3.9), fully endpoint-aware and
corrected.

For any two banana vertices, either they are in one of the invariant
exceptional families above, or an explicit divisor has negative marked rank
difference.  In particular this incorporates the missing length-two midpoint
exception discovered during formalization. -/
theorem nsmForBanana_classification
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β) :
    NSMForBananaException B (strandVertex B α i) (strandVertex B β j) ∨
      ∃ D : CFDiv B.graph,
        rankDelta (mark B.graph (strandVertex B α i) (strandVertex B β j)) D < 0 := by
  by_cases hi : B.IsInteriorPosition α i
  · by_cases hj : B.IsInteriorPosition β j
    · rcases nsmForBanana_interior_classification hg B α β i j hi hj with h | h
      · left
        exact Or.inr (Or.inr (Or.inr ⟨α, β, i, j, hi, hj, rfl, rfl, h⟩))
      · exact Or.inr h
    · change ¬ (0 < j.val ∧ j.val < B.length β) at hj
      change 0 < i.val ∧ i.val < B.length α at hi
      have hjEnds : j.val = 0 ∨ j.val = B.length β := by
        have hjBound : j.val ≤ B.length β := Nat.le_of_lt_succ j.isLt
        omega
      rcases hjEnds with hjZero | hjLength
      · have hV : strandVertex B β j = leftEndpoint B := by
          have hpos : j = ⟨0, by omega⟩ := Fin.ext hjZero
          rw [hpos, strandVertex_zero]
        by_cases hiFar : i.val + 1 < B.length α
        · right
          rcases exists_rankDelta_neg_leftEndpoint_same_strand (by omega) B α i hi hiFar with
            ⟨D, hD⟩
          refine ⟨D, ?_⟩
          rw [hV, rankDelta_swap_marks]
          exact hD
        · left
          have hiPenult : i.val + 1 = B.length α := by omega
          exact Or.inr (Or.inr (Or.inl ⟨α, i, hi,
            Or.inr (Or.inr (Or.inl ⟨hV, rfl, hiPenult⟩))⟩))
      · have hV : strandVertex B β j = rightEndpoint B := by
          have hpos : j = ⟨B.length β, by omega⟩ := Fin.ext hjLength
          rw [hpos, strandVertex_length]
        by_cases hiOne : i.val = 1
        · left
          exact Or.inr (Or.inr (Or.inl ⟨α, i, hi,
            Or.inr (Or.inr (Or.inr ⟨hV, rfl, hiOne⟩))⟩))
        · right
          rcases exists_rankDelta_neg_rightEndpoint_same_strand (by omega) B α i hi (by omega) with
            ⟨D, hD⟩
          refine ⟨D, ?_⟩
          rw [hV, rankDelta_swap_marks]
          exact hD
  · by_cases hj : B.IsInteriorPosition β j
    · change ¬ (0 < i.val ∧ i.val < B.length α) at hi
      change 0 < j.val ∧ j.val < B.length β at hj
      have hiEnds : i.val = 0 ∨ i.val = B.length α := by
        have hiBound : i.val ≤ B.length α := Nat.le_of_lt_succ i.isLt
        omega
      rcases hiEnds with hiZero | hiLength
      · have hU : strandVertex B α i = leftEndpoint B := by
          have hpos : i = ⟨0, by omega⟩ := Fin.ext hiZero
          rw [hpos, strandVertex_zero]
        by_cases hjFar : j.val + 1 < B.length β
        · right
          rw [hU]
          exact exists_rankDelta_neg_leftEndpoint_same_strand (by omega) B β j hj hjFar
        · left
          have hjPenult : j.val + 1 = B.length β := by omega
          exact Or.inr (Or.inr (Or.inl ⟨β, j, hj,
            Or.inl ⟨hU, rfl, hjPenult⟩⟩))
      · have hU : strandVertex B α i = rightEndpoint B := by
          have hpos : i = ⟨B.length α, by omega⟩ := Fin.ext hiLength
          rw [hpos, strandVertex_length]
        by_cases hjOne : j.val = 1
        · left
          exact Or.inr (Or.inr (Or.inl ⟨β, j, hj,
            Or.inr (Or.inl ⟨hU, rfl, hjOne⟩)⟩))
        · right
          rw [hU]
          exact exists_rankDelta_neg_rightEndpoint_same_strand (by omega) B β j hj (by omega)
    · change ¬ (0 < i.val ∧ i.val < B.length α) at hi
      change ¬ (0 < j.val ∧ j.val < B.length β) at hj
      have hiEnds : i.val = 0 ∨ i.val = B.length α := by
        have hiBound : i.val ≤ B.length α := Nat.le_of_lt_succ i.isLt
        omega
      have hjEnds : j.val = 0 ∨ j.val = B.length β := by
        have hjBound : j.val ≤ B.length β := Nat.le_of_lt_succ j.isLt
        omega
      rcases hiEnds with hiZero | hiLength <;> rcases hjEnds with hjZero | hjLength
      · right
        have hU : strandVertex B α i = leftEndpoint B := by
          have hpos : i = ⟨0, by omega⟩ := Fin.ext hiZero
          rw [hpos, strandVertex_zero]
        have hV : strandVertex B β j = leftEndpoint B := by
          have hpos : j = ⟨0, by omega⟩ := Fin.ext hjZero
          rw [hpos, strandVertex_zero]
        rw [hU, hV]
        exact ⟨oneChip (leftEndpoint B), rankDelta_one_chip_self_lt_zero (by omega) B _⟩
      · left
        have hU : strandVertex B α i = leftEndpoint B := by
          have hpos : i = ⟨0, by omega⟩ := Fin.ext hiZero
          rw [hpos, strandVertex_zero]
        have hV : strandVertex B β j = rightEndpoint B := by
          have hpos : j = ⟨B.length β, by omega⟩ := Fin.ext hjLength
          rw [hpos, strandVertex_length]
        exact Or.inl ⟨hU, hV⟩
      · left
        have hU : strandVertex B α i = rightEndpoint B := by
          have hpos : i = ⟨B.length α, by omega⟩ := Fin.ext hiLength
          rw [hpos, strandVertex_length]
        have hV : strandVertex B β j = leftEndpoint B := by
          have hpos : j = ⟨0, by omega⟩ := Fin.ext hjZero
          rw [hpos, strandVertex_zero]
        exact Or.inr (Or.inl ⟨hU, hV⟩)
      · right
        have hU : strandVertex B α i = rightEndpoint B := by
          have hpos : i = ⟨B.length α, by omega⟩ := Fin.ext hiLength
          rw [hpos, strandVertex_length]
        have hV : strandVertex B β j = rightEndpoint B := by
          have hpos : j = ⟨B.length β, by omega⟩ := Fin.ext hjLength
          rw [hpos, strandVertex_length]
        rw [hU, hV]
        exact ⟨oneChip (rightEndpoint B), rankDelta_one_chip_self_lt_zero (by omega) B _⟩

end Bananas
