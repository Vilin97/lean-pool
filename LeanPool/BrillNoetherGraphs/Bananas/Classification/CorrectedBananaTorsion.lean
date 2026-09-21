/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaTorsionSlopes
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.MidpointTorsion
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMFullClassification

/-!
# Corrected high-genus banana torsion dichotomy

This is the one remaining non-Section-6 input to the corrected Corollary 6.4.
The paper's exceptional family is corrected here: one of the two marked
midpoint strands need only have length two; the other may have any even
length.
-/

namespace Bananas

open Utilities

/-- The completed corrected Theorem 3.9 gives the first reduction for
Proposition 4.19: all-divisor submodularity forces one of its explicit
endpoint-aware exceptional families. -/
theorem allSubmodular_implies_nsmForBananaException
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hSub : AllSubmodular
      (mark B.graph (strandVertex B α i) (strandVertex B β j))) :
    NSMForBananaException B (strandVertex B α i) (strandVertex B β j) := by
  rcases nsmForBanana_classification hg B α β i j with hException | hNeg
  · exact hException
  · rcases hNeg with ⟨D, hD⟩
    have hNonneg : 0 ≤ rankDelta
        (mark B.graph (strandVertex B α i) (strandVertex B β j)) D :=
      (allSubmodular_iff_rankDelta_nonneg _).mp hSub D
    exact False.elim (not_le_of_gt hD hNonneg)

/-- If a coordinate represents the same vertex as a known interior
coordinate, it too is interior.  This lets us transport the invariant
classification back to the coordinates in the proposition statement. -/
private theorem isInteriorPosition_of_strandVertex_eq_interior
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hj : B.IsInteriorPosition β j)
    (h : strandVertex B α i = strandVertex B β j) :
    B.IsInteriorPosition α i := by
  change 0 < i.val ∧ i.val < B.length α
  have hiBound : i.val ≤ B.length α := Nat.le_of_lt_succ i.isLt
  constructor
  · by_contra hnot
    have hiZero : i.val = 0 := by omega
    have hi : i = ⟨0, by omega⟩ := Fin.ext hiZero
    rw [hi, strandVertex_zero] at h
    exact (strandVertex_ne_leftEndpoint B β j hj.1) h.symm
  · by_contra hnot
    have hiLength : i.val = B.length α := by omega
    have hi : i = ⟨B.length α, by omega⟩ := Fin.ext hiLength
    rw [hi, strandVertex_length] at h
    exact (strandVertex_ne_rightEndpoint B β j hj.2) h.symm

/-- The corrected midpoint exception is unchanged by ordering the marks. -/
private theorem correctedMidpointException_swap
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (h : CorrectedMidpointException B β α j i) :
    CorrectedMidpointException B α β i j := by
  rcases h with ⟨hβα, hjMid, hiMid, hβTwo | hαTwo⟩
  · exact ⟨hβα.symm, hiMid, hjMid, Or.inr hβTwo⟩
  · exact ⟨hβα.symm, hiMid, hjMid, Or.inl hαTwo⟩

/-- Corrected Proposition 4.19 (`prop-bananTorsion`).

Outside the corrected midpoint family, every exact torsion order compatible
with all-divisor submodularity is at least the genus.  The proof combines the
completed Theorem 3.9 classification with the endpoint and near-opposite
slope bounds and the reduced-divisor midpoint lemma `lem-midpointTorsion`.
The statement is deliberately separate from the Section 6 assembly so that
no later theorem can silently use an unrecorded
classification assumption. -/
theorem corrected_banana_torsion_dichotomy
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k)
    (hSub : AllSubmodular
      (mark B.graph (strandVertex B α i) (strandVertex B β j))) :
    (CorrectedMidpointException B α β i j ∧ k = 2) ∨ g ≤ k := by
  have hException :=
    allSubmodular_implies_nsmForBananaException hg B α β i j hSub
  rcases hException with hLR | hRest
  · rcases hLR with ⟨hu, hv⟩
    have hTO' := hTO
    have hSub' := hSub
    rw [hu, hv] at hTO' hSub'
    exact Or.inr (Nat.le_of_lt
      (endpoint_marking_torsionOrder_gt_genus B hSub' hTO'))
  · rcases hRest with hRL | hRest
    · rcases hRL with ⟨hu, hv⟩
      have hTO' := hTO
      have hSub' := hSub
      rw [hu, hv] at hTO' hSub'
      have hTOSwap := isTorsionOrder_swap_marks
        (rightEndpoint B) (leftEndpoint B) hTO'
      have hSubSwap := (allSubmodular_swap_iff
        (leftEndpoint B) (rightEndpoint B)).mp hSub'
      exact Or.inr (Nat.le_of_lt
        (endpoint_marking_torsionOrder_gt_genus B hSubSwap hTOSwap))
    · rcases hRest with hNear | hInterior
      · rcases hNear with ⟨γ, p, hp, hCase⟩
        rcases hCase with hLeft | hRight | hLeftSwap | hRightSwap
        · rcases hLeft with ⟨hu, hv, hpLast⟩
          have hTO' := hTO
          rw [hu, hv] at hTO'
          exact Or.inr (Nat.le_of_lt
            (leftEndpoint_penultimate_torsionOrder_gt_genus
              B γ p hp hpLast hTO'))
        · rcases hRight with ⟨hu, hv, hpOne⟩
          have hTO' := hTO
          rw [hu, hv] at hTO'
          exact Or.inr (Nat.le_of_lt
            (rightEndpoint_one_torsionOrder_gt_genus
              B γ p hp hpOne hTO'))
        · rcases hLeftSwap with ⟨hv, hu, hpLast⟩
          have hTO' := hTO
          rw [hu, hv] at hTO'
          have hTOSwap := isTorsionOrder_swap_marks
            (strandVertex B γ p) (leftEndpoint B) hTO'
          exact Or.inr (Nat.le_of_lt
            (leftEndpoint_penultimate_torsionOrder_gt_genus
              B γ p hp hpLast hTOSwap))
        · rcases hRightSwap with ⟨hv, hu, hpOne⟩
          have hTO' := hTO
          rw [hu, hv] at hTO'
          have hTOSwap := isTorsionOrder_swap_marks
            (strandVertex B γ p) (rightEndpoint B) hTO'
          exact Or.inr (Nat.le_of_lt
            (rightEndpoint_one_torsionOrder_gt_genus
              B γ p hp hpOne hTOSwap))
      · rcases hInterior with
          ⟨γ, δ, p, q, hp, hq, hu, hv, hInteriorException⟩
        have hi := isInteriorPosition_of_strandVertex_eq_interior
          B α γ i p hp hu
        have hj := isInteriorPosition_of_strandVertex_eq_interior
          B β δ j q hq hv
        have hαγ := strand_eq_of_interior_vertex_eq B α γ i p hi hp hu
        have hβδ := strand_eq_of_interior_vertex_eq B β δ j q hj hq hv
        subst γ
        subst δ
        have hip : i = p := strandVertex_injective B α hu
        have hjq : j = q := strandVertex_injective B β hv
        subst p
        subst q
        rcases hInteriorException with ⟨hαβ, hCase⟩
        rcases hCase with hOneLast | hLastOne | hLengthTwo | hLengthTwoSwap
        · exact cross_oneOff_torsion_dichotomy (by omega) B α β i j
            hαβ hi hj hOneLast.1 hOneLast.2 hTO
        · have hTOSwap := isTorsionOrder_swap_marks
            (strandVertex B α i) (strandVertex B β j) hTO
          rcases cross_oneOff_torsion_dichotomy (by omega) B β α j i
              hαβ.symm hj hi hLastOne.2 hLastOne.1 hTOSwap with
            hExceptional | hLarge
          · exact Or.inl ⟨correctedMidpointException_swap B α β i j
                hExceptional.1, hExceptional.2⟩
          · exact Or.inr hLarge
        · exact length_two_cross_torsion_dichotomy (by omega) B α β i j
            hαβ hi hj hLengthTwo.1 hLengthTwo.2 hTO
        · have hTOSwap := isTorsionOrder_swap_marks
            (strandVertex B α i) (strandVertex B β j) hTO
          rcases length_two_cross_torsion_dichotomy (by omega) B β α j i
              hαβ.symm hj hi hLengthTwoSwap.1 hLengthTwoSwap.2 hTOSwap with
            hExceptional | hLarge
          · exact Or.inl ⟨correctedMidpointException_swap B α β i j
                hExceptional.1, hExceptional.2⟩
          · exact Or.inr hLarge

end Bananas
