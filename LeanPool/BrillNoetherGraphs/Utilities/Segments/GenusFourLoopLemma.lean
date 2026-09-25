/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.GenusFourPseudocore
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexReachability
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.EffectiveDifference
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionCorner

/-!
# A loop-split interface for the genus-four loop lemma

Atanasov--Ranganathan contract two topological loops, use genus two on the
contracted graph, and then lift the resulting degree-three divisor back across
the loops.  In the certificate model a topological loop is represented by a
bivalent core marker joined to its base by two subdivided edge slots.

This file formalizes the rank-theoretic end of that argument.  The embedded
core is already known to be a strong separator, so it is enough to reach the
original core vertices and the loop markers.  Reaching a marker can in turn
be split into two small pieces: a representative carrying two chips at the
loop base and the standard degree-two reflection move on the loop.

The remaining geometric input for the full loop lemma is deliberately visible
in the hypotheses of `bnExists_three_of_two_loop_split_witness`: one must
construct the two-chip representatives after contracting the loops and prove
the reflection move uniformly for two subdivided paths of arbitrary positive
lengths.  Neither assertion is silently delegated to generated data here.
-/

namespace Utilities.Certificate.GenusFourLoopLemma

open Finset
open GenusFourPseudocore

variable {G : CFGraph}

/-- The divisor class of `D` has an effective representative carrying two
chips at `base`.  This is the exact pointed input needed to enter an attached
topological loop. -/
def HasTwoChipsRepresentative (D : CFDiv G) (base : G.V) : Prop :=
  ∃ E : CFDiv G,
    effective E ∧ linearEquiv G D E ∧ 2 ≤ E base

/-- The genus-two algebraic heart of the Atanasov--Ranganathan loop lemma.
For any two prospective loop bases, one degree-three class has effective
representatives carrying two chips at either base. -/
theorem exists_common_two_chip_class_genus_two
    (hConnected : graphConnected G) (hGenus : genus G = 2)
    (first second : G.V) :
    ∃ D : CFDiv G,
      effective D ∧ deg D = 3 ∧ rank G D ≥ 1 ∧
      HasTwoChipsRepresentative D first ∧
      HasTwoChipsRepresentative D second := by
  let gamma : CFDiv G :=
    (2 : ℤ) • oneChip first - (2 : ℤ) • oneChip second
  have hGammaDegree : deg gamma = 0 := by
    dsimp [gamma]
    rw [deg.map_sub, map_zsmul, map_zsmul, deg_one_chip, deg_one_chip]
    ring
  obtain ⟨E, F, hEEffective, hFEffective, hEDegree, hFDegree, hDifference⟩ :=
    exists_effective_difference_of_deg_zero hConnected (by omega)
      gamma hGammaDegree
  let D : CFDiv G := (2 : ℤ) • oneChip first + E
  let Dsecond : CFDiv G := (2 : ℤ) • oneChip second + F
  have hDEffective : effective D := by
    exact (Eff G).add_mem
      ((Eff G).nsmul_mem (eff_one_chip first) 2)
      hEEffective
  have hDsecondEffective : effective Dsecond := by
    exact (Eff G).add_mem
      ((Eff G).nsmul_mem (eff_one_chip second) 2)
      hFEffective
  have hDDegree : deg D = 3 := by
    dsimp [D]
    rw [deg.map_add, map_zsmul, deg_one_chip, hEDegree, hGenus]
    norm_num
  have hDsecondDegree : deg Dsecond = 3 := by
    dsimp [Dsecond]
    rw [deg.map_add, map_zsmul, deg_one_chip, hFDegree, hGenus]
    norm_num
  have hEquivSecond : linearEquiv G D Dsecond := by
    unfold linearEquiv at hDifference ⊢
    have hRewrite :
        Dsecond - D = -(gamma - (F - E)) := by
      dsimp [D, Dsecond, gamma]
      abel
    rw [hRewrite]
    exact AddSubgroup.neg_mem (principalDivisors G) hDifference
  have hFirstTwo : 2 ≤ D first := by
    have := hEEffective first
    simp only [zsmul_eq_mul, Int.cast_ofNat, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply, oneChip,
      ↓reduceIte, mul_one, le_add_iff_nonneg_right, ge_iff_le, D]
    omega
  have hSecondTwo : 2 ≤ Dsecond second := by
    have := hFEffective second
    simp only [zsmul_eq_mul, Int.cast_ofNat, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply, oneChip,
      ↓reduceIte, mul_one, le_add_iff_nonneg_right, ge_iff_le, Dsecond]
    omega
  have hRank : rank G D ≥ 1 := by
    have hRiemann := rank_ge_deg_sub_genus hConnected D
    rw [hDDegree, hGenus] at hRiemann
    exact hRiemann
  exact ⟨D, hDEffective, hDDegree, hRank,
    ⟨D, hDEffective, linearEquiv.refl G D, hFirstTwo⟩,
    ⟨Dsecond, hDsecondEffective, hEquivSecond, hSecondTwo⟩⟩

/-- A two-chip reflection move from `base` through `target`.  On a cycle,
the second output chip is the reflection of `target` in `base`.  Writing the
move as an exact principal divisor keeps this interface independent of any
particular cycle coordinates. -/
def TwoChipReflection (base target : G.V) : Prop :=
  ∃ (reflected : G.V) (script : firingScript G),
    prin G script =
      (-2 : ℤ) • oneChip base + oneChip target + oneChip reflected

/-- Borrow once at a loop marker.  When the marker is joined to its base by
two unit edges and has no other neighbors, this is the complete two-chip
reflection script. -/
def markerBorrowScript (target : G.V) : firingScript G :=
  fun vertex => if vertex = target then -1 else 0

/-- The split model's unsubdivided double edge realizes a two-chip reflection:
borrowing at its bivalent marker moves two chips from the base to the marker.
This is the length-one endpoint of the arbitrary-length cycle bridge still
needed for the full loop lemma. -/
theorem twoChipReflection_of_doubleEdgeMarker
    {base target : G.V} (hDistinct : base ≠ target)
    (hDouble : numEdges G base target = 2)
    (hNoOther : ∀ vertex : G.V, vertex ≠ base →
      numEdges G target vertex = 0) :
    TwoChipReflection base target := by
  refine ⟨target, markerBorrowScript target, ?_⟩
  funext vertex
  by_cases hTarget : vertex = target
  · subst vertex
    change
      (∑ neighbor : G.V,
        (markerBorrowScript target neighbor -
          markerBorrowScript target target) *
          (numEdges G target neighbor : ℤ)) = _
    have hSum :
        (∑ neighbor : G.V,
          (markerBorrowScript target neighbor -
            markerBorrowScript target target) *
            (numEdges G target neighbor : ℤ)) =
          (numEdges G target base : ℤ) := by
      classical
      calc
        _ = (markerBorrowScript target base -
              markerBorrowScript target target) *
              (numEdges G target base : ℤ) := by
          apply Fintype.sum_eq_single base
          intro neighbor hNeighbor
          have hZero := hNoOther neighbor hNeighbor
          by_cases hNeighborTarget : neighbor = target
          · subst neighbor
            simp [markerBorrowScript]
          · simp [markerBorrowScript, hNeighborTarget, hZero]
        _ = _ := by simp [markerBorrowScript, hDistinct]
    rw [hSum, num_edges_symmetric, hDouble]
    simp [oneChip, hDistinct.symm]
  · by_cases hBase : vertex = base
    · subst vertex
      change
        (∑ neighbor : G.V,
          (markerBorrowScript target neighbor -
            markerBorrowScript target base) *
            (numEdges G base neighbor : ℤ)) = _
      have hSum :
          (∑ neighbor : G.V,
            (markerBorrowScript target neighbor -
              markerBorrowScript target base) *
              (numEdges G base neighbor : ℤ)) =
            -(numEdges G base target : ℤ) := by
        classical
        calc
          _ = (markerBorrowScript target target -
                markerBorrowScript target base) *
                (numEdges G base target : ℤ) := by
            apply Fintype.sum_eq_single target
            intro neighbor hNeighbor
            simp [markerBorrowScript, hNeighbor, hDistinct]
          _ = _ := by simp [markerBorrowScript, hDistinct]
      rw [hSum, hDouble]
      simp [oneChip, hDistinct]
    · change
        (∑ neighbor : G.V,
          (markerBorrowScript target neighbor -
            markerBorrowScript target vertex) *
            (numEdges G vertex neighbor : ℤ)) = _
      have hVertexTargetZero : numEdges G vertex target = 0 := by
        rw [num_edges_symmetric]
        exact hNoOther vertex hBase
      have hSum :
          (∑ neighbor : G.V,
            (markerBorrowScript target neighbor -
              markerBorrowScript target vertex) *
              (numEdges G vertex neighbor : ℤ)) = 0 := by
        classical
        apply Finset.sum_eq_zero
        intro neighbor _hNeighbor
        by_cases hNeighborTarget : neighbor = target
        · subst neighbor
          simp [markerBorrowScript, hTarget, hVertexTargetZero]
        · simp [markerBorrowScript, hTarget, hNeighborTarget]
      rw [hSum]
      simp [oneChip, hTarget, hBase]

/-! ## Reflection through two arbitrarily subdivided paths -/

/-- The core potential used to move two chips from a loop base towards its
marker.  Its depth is the length of the shorter path. -/
def loopRampPotential {n : ℕ} (marker : Fin n) (depth : ℕ) : Fin n → ℤ :=
  fun vertex => if vertex = marker then -(depth : ℤ) else 0

/-- Two parallel oriented core slots, with no other slot incident to their
common head, realize the standard two-chip reflection.  The reflected chip
lands at the marker when the paths have equal length; otherwise it lands on
the longer path at the same distance from the base as the marker is along the
shorter path.

This is the arbitrary-length metric statement left implicit in the published
Atanasov--Ranganathan loop argument. -/
theorem twoChipReflection_of_two_oriented_paths
    {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (base marker : Fin n) (first second : Fin p)
    (hFirstSecond : first ≠ second)
    (hFirstTail : spec.core.tail first = base)
    (hFirstHead : spec.core.head first = marker)
    (hSecondTail : spec.core.tail second = base)
    (hSecondHead : spec.core.head second = marker)
    (hOnly : ∀ edge : Fin p,
      spec.core.tail edge = marker ∨ spec.core.head edge = marker →
        edge = first ∨ edge = second)
    (hLengthOrder : spec.length first ≤ spec.length second) :
    TwoChipReflection (G := spec.graph)
      (spec.coreVertex base) (spec.coreVertex marker) := by
  classical
  have hBaseMarker : base ≠ marker := by
    intro h
    apply spec.core_loopless first
    rw [hFirstTail, hFirstHead, h]
  let potential : Fin n → ℤ :=
    loopRampPotential marker (spec.length first)
  let script : firingScript spec.graph := spec.interpolatedScript potential
  have hFirstRise :
      spec.coreRise potential first = -(spec.length first : ℤ) := by
    simp [SubdivisionGraph.Spec.coreRise, potential, loopRampPotential,
      hFirstTail, hFirstHead, hBaseMarker]
  have hSecondRise :
      spec.coreRise potential second = -(spec.length first : ℤ) := by
    simp [SubdivisionGraph.Spec.coreRise, potential, loopRampPotential,
      hSecondTail, hSecondHead, hBaseMarker]
  have hOtherRise (edge : Fin p) (hEF : edge ≠ first)
      (hES : edge ≠ second) : spec.coreRise potential edge = 0 := by
    have hTail : spec.core.tail edge ≠ marker := by
      intro h
      rcases hOnly edge (Or.inl h) with h | h
      · exact hEF h
      · exact hES h
    have hHead : spec.core.head edge ≠ marker := by
      intro h
      rcases hOnly edge (Or.inr h) with h | h
      · exact hEF h
      · exact hES h
    simp [SubdivisionGraph.Spec.coreRise, potential, loopRampPotential,
      hTail, hHead]
  have hFirstStep (i : ℕ) :
      SubdivisionArithmetic.step (spec.length first)
          (spec.coreRise potential first) i =
        if i < spec.length first then -1 else 0 := by
    rw [hFirstRise]
    exact SubdivisionArithmetic.step_neg_eq_ite
      (spec.length_pos first) (le_refl _)
  have hSecondStep (i : ℕ) :
      SubdivisionArithmetic.step (spec.length second)
          (spec.coreRise potential second) i =
        if i < spec.length first then -1 else 0 := by
    rw [hSecondRise]
    exact SubdivisionArithmetic.step_neg_eq_ite
      (spec.length_pos first) hLengthOrder
  have hFirstInitial :
      SubdivisionArithmetic.step (spec.length first)
          (spec.coreRise potential first) 0 = -1 := by
    rw [hFirstStep]
    simp [spec.length_pos first]
  have hFirstFinal :
      SubdivisionArithmetic.step (spec.length first)
        (spec.coreRise potential first) (spec.length first - 1) = -1 := by
    have hLast : spec.length first - 1 < spec.length first :=
      Nat.sub_lt (spec.length_pos first) (by omega)
    simpa [hLast] using hFirstStep (spec.length first - 1)
  have hSecondInitial :
      SubdivisionArithmetic.step (spec.length second)
        (spec.coreRise potential second) 0 = -1 := by
    rw [hSecondStep]
    rw [if_pos (spec.length_pos first)]
  have sum_two_ite (A B : ℤ) :
      (∑ edge : Fin p,
        if edge = first then A else if edge = second then B else 0) = A + B := by
    calc
      _ = ∑ edge : Fin p,
          ((if edge = first then A else 0) +
            (if edge = second then B else 0)) := by
        apply Finset.sum_congr rfl
        intro edge _
        by_cases hEF : edge = first <;> by_cases hES : edge = second
        · subst edge
          exact (hFirstSecond hES).elim
        · simp [hEF, hFirstSecond]
        · simp [hES, hFirstSecond.symm]
        · simp [hEF, hES]
      _ = A + B := by
        rw [Finset.sum_add_distrib]
        simp only [Fintype.sum_ite_eq']
  by_cases hEqual : spec.length first = spec.length second
  · refine ⟨spec.coreVertex marker, script, ?_⟩
    funext vertex
    rcases vertex with vertex | interior
    · dsimp [script]
      change prin spec.graph (spec.interpolatedScript potential)
        (spec.coreVertex vertex) = _
      rw [spec.prin_interpolatedScript_core_eq_endpointSum]
      have hTerm (edge : Fin p) :
          ((if spec.core.tail edge = vertex then
              SubdivisionArithmetic.step (spec.length edge)
                (spec.coreRise potential edge) 0 else 0) +
            (if spec.core.head edge = vertex then
              -SubdivisionArithmetic.step (spec.length edge)
                (spec.coreRise potential edge)
                (spec.length edge - 1) else 0)) =
            if edge = first then
              (if vertex = base then -1 else 0) +
                (if vertex = marker then 1 else 0)
            else if edge = second then
              (if vertex = base then -1 else 0) +
                (if vertex = marker then 1 else 0)
            else 0 := by
        by_cases hEF : edge = first
        · subst edge
          simp only [if_pos]
          simp only [hFirstTail, hFirstHead, hFirstInitial,
            hFirstFinal, neg_neg, eq_comm]
        · by_cases hES : edge = second
          · subst edge
            simp only [if_pos]
            have hLast : spec.length second - 1 < spec.length first := by
              rw [hEqual]
              exact Nat.sub_lt (spec.length_pos second) (by omega)
            have hSecondFinal :
                SubdivisionArithmetic.step (spec.length second)
                    (spec.coreRise potential second)
                    (spec.length second - 1) = -1 := by
              rw [hSecondStep]
              simp [hLast]
            simp [hSecondTail, hSecondHead, hSecondInitial,
              hSecondFinal, hFirstSecond.symm, eq_comm]
          · simp only [if_neg hEF, if_neg hES]
            rw [hOtherRise edge hEF hES]
            have hLast : spec.length edge - 1 < spec.length edge :=
              Nat.sub_lt (spec.length_pos edge) (by omega)
            simp [SubdivisionArithmetic.step_zero_of_lt
              (spec.length_pos edge),
              SubdivisionArithmetic.step_zero_of_lt hLast]
      simp_rw [hTerm]
      rw [sum_two_ite]
      by_cases hVB : vertex = base <;> by_cases hVM : vertex = marker <;>
        simp_all [oneChip, SubdivisionGraph.Spec.coreVertex]
    · obtain ⟨edge, offset⟩ := interior
      dsimp [script]
      change prin spec.graph (spec.interpolatedScript potential)
        (spec.interiorVertex edge offset) = _
      rw [spec.prin_interpolatedScript_interior_eq_stepDifference]
      by_cases hEF : edge = first
      · subst edge
        have hOffset : offset.val + 1 < spec.length first := by
          have := offset.isLt
          omega
        have hOffset' : offset.val < spec.length first := by omega
        rw [hFirstStep, hFirstStep]
        simp [hOffset, hOffset', oneChip,
          SubdivisionGraph.Spec.coreVertex]
      · by_cases hES : edge = second
        · subst edge
          have hOffset : offset.val + 1 < spec.length first := by
            have := offset.isLt
            omega
          have hOffset' : offset.val < spec.length first := by omega
          rw [hSecondStep, hSecondStep]
          simp [hOffset, hOffset', oneChip,
            SubdivisionGraph.Spec.coreVertex]
        · rw [hOtherRise edge hEF hES]
          have hNext : offset.val + 1 < spec.length edge := by
            have := offset.isLt
            omega
          have hHere : offset.val < spec.length edge := by omega
          rw [SubdivisionArithmetic.step_zero_of_lt (L := spec.length edge)
            (i := offset.val + 1) hNext]
          rw [SubdivisionArithmetic.step_zero_of_lt (L := spec.length edge)
            (i := offset.val) hHere]
          simp [oneChip, SubdivisionGraph.Spec.coreVertex]
  · have hStrict : spec.length first < spec.length second :=
      lt_of_le_of_ne hLengthOrder hEqual
    have hFirstLength := spec.length_pos first
    let offset : Fin (spec.length second - 1) :=
      ⟨spec.length first - 1, by omega⟩
    refine ⟨spec.interiorVertex second offset, script, ?_⟩
    funext vertex
    rcases vertex with vertex | interior
    · dsimp [script]
      change prin spec.graph (spec.interpolatedScript potential)
        (spec.coreVertex vertex) = _
      rw [spec.prin_interpolatedScript_core_eq_endpointSum]
      have hTerm (edge : Fin p) :
          ((if spec.core.tail edge = vertex then
              SubdivisionArithmetic.step (spec.length edge)
                (spec.coreRise potential edge) 0 else 0) +
            (if spec.core.head edge = vertex then
              -SubdivisionArithmetic.step (spec.length edge)
                (spec.coreRise potential edge)
                (spec.length edge - 1) else 0)) =
            if edge = first then
              (if vertex = base then -1 else 0) +
                (if vertex = marker then 1 else 0)
            else if edge = second then
              (if vertex = base then -1 else 0)
            else 0 := by
        by_cases hEF : edge = first
        · subst edge
          simp only [if_pos]
          simp only [hFirstTail, hFirstHead, hFirstInitial,
            hFirstFinal, neg_neg, eq_comm]
        · by_cases hES : edge = second
          · subst edge
            simp only [if_pos]
            have hLast : ¬ spec.length second - 1 < spec.length first := by
              omega
            have hSecondFinal :
                SubdivisionArithmetic.step (spec.length second)
                    (spec.coreRise potential second)
                    (spec.length second - 1) = 0 := by
              rw [hSecondStep]
              simp [hLast]
            have hNot : second ≠ first := hFirstSecond.symm
            simp [hSecondTail, hSecondHead, hSecondInitial,
              hSecondFinal, hNot, eq_comm]
          · simp only [if_neg hEF, if_neg hES]
            rw [hOtherRise edge hEF hES]
            have hLast : spec.length edge - 1 < spec.length edge :=
              Nat.sub_lt (spec.length_pos edge) (by omega)
            simp [SubdivisionArithmetic.step_zero_of_lt
              (spec.length_pos edge),
              SubdivisionArithmetic.step_zero_of_lt hLast]
      simp_rw [hTerm]
      rw [sum_two_ite]
      by_cases hVB : vertex = base <;> by_cases hVM : vertex = marker <;>
        simp_all [oneChip, SubdivisionGraph.Spec.coreVertex,
          SubdivisionGraph.Spec.interiorVertex]
    · obtain ⟨edge, interiorOffset⟩ := interior
      dsimp [script]
      change prin spec.graph (spec.interpolatedScript potential)
        (spec.interiorVertex edge interiorOffset) = _
      rw [spec.prin_interpolatedScript_interior_eq_stepDifference]
      by_cases hEF : edge = first
      · subst edge
        have hOffset : interiorOffset.val + 1 < spec.length first :=
          by have := interiorOffset.isLt; omega
        have hOffset' : interiorOffset.val < spec.length first := by omega
        rw [hFirstStep, hFirstStep]
        simp [hOffset, hOffset', oneChip, hFirstSecond,
          SubdivisionGraph.Spec.coreVertex,
          SubdivisionGraph.Spec.interiorVertex]
      · by_cases hES : edge = second
        · subst edge
          by_cases hOffset : interiorOffset = offset
          · subst interiorOffset
            rw [hSecondStep, hSecondStep]
            have hDepth : spec.length first - 1 + 1 = spec.length first := by
              omega
            simp [offset, hFirstLength, hDepth,
              SubdivisionGraph.Spec.coreVertex,
              SubdivisionGraph.Spec.interiorVertex]
          · have hValNe : interiorOffset.val ≠ spec.length first - 1 := by
              intro hVal
              apply hOffset
              apply Fin.ext
              exact hVal
            have hEither :
                interiorOffset.val + 1 < spec.length first ∨
                  spec.length first ≤ interiorOffset.val := by
              omega
            rcases hEither with hBefore | hAfter
            · have hBefore' : interiorOffset.val < spec.length first := by omega
              rw [hSecondStep, hSecondStep]
              simp [hBefore, hBefore', hOffset,
                SubdivisionGraph.Spec.coreVertex,
                SubdivisionGraph.Spec.interiorVertex]
            · have hAfter' : ¬ interiorOffset.val + 1 < spec.length first := by
                omega
              have hAfter'' : ¬ interiorOffset.val < spec.length first := by
                omega
              rw [hSecondStep, hSecondStep]
              simp [hAfter', hAfter'', hOffset,
                SubdivisionGraph.Spec.coreVertex,
                SubdivisionGraph.Spec.interiorVertex]
        · rw [hOtherRise edge hEF hES]
          have hNext : interiorOffset.val + 1 < spec.length edge := by
            have := interiorOffset.isLt
            omega
          have hHere : interiorOffset.val < spec.length edge := by omega
          rw [SubdivisionArithmetic.step_zero_of_lt (L := spec.length edge)
            (i := interiorOffset.val + 1) hNext]
          rw [SubdivisionArithmetic.step_zero_of_lt (L := spec.length edge)
            (i := interiorOffset.val) hHere]
          simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex, hES]

/-- Order-free form of `twoChipReflection_of_two_oriented_paths`. -/
theorem twoChipReflection_of_two_paths
    {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (base marker : Fin n) (first second : Fin p)
    (hFirstSecond : first ≠ second)
    (hFirstTail : spec.core.tail first = base)
    (hFirstHead : spec.core.head first = marker)
    (hSecondTail : spec.core.tail second = base)
    (hSecondHead : spec.core.head second = marker)
    (hOnly : ∀ edge : Fin p,
      spec.core.tail edge = marker ∨ spec.core.head edge = marker →
        edge = first ∨ edge = second) :
    TwoChipReflection (G := spec.graph)
      (spec.coreVertex base) (spec.coreVertex marker) := by
  rcases le_total (spec.length first) (spec.length second) with h | h
  · exact twoChipReflection_of_two_oriented_paths spec base marker first second
      hFirstSecond hFirstTail hFirstHead hSecondTail hSecondHead hOnly h
  · apply twoChipReflection_of_two_oriented_paths spec base marker second first
      hFirstSecond.symm hSecondTail hSecondHead hFirstTail hFirstHead
    · intro edge hIncident
      rcases hOnly edge hIncident with hEdge | hEdge
      · exact Or.inr hEdge
      · exact Or.inl hEdge
    · exact h

/-- Removing two chips at one vertex from an effective divisor that carries
at least two there remains effective. -/
theorem effective_sub_two_chips
    {E : CFDiv G} {base : G.V}
    (hEffective : effective E) (hTwo : 2 ≤ E base) :
    effective (E - (2 : ℤ) • oneChip base) := by
  intro vertex
  by_cases hVertex : vertex = base
  · subst vertex
    simp only [zsmul_eq_mul, Int.cast_ofNat, Pi.sub_apply, Pi.mul_apply, Pi.ofNat_apply, oneChip,
      ↓reduceIte, mul_one, Int.sub_nonneg]
    omega
  · simp [oneChip, hVertex, hEffective vertex]

/-- A two-chip representative and a loop reflection make the divisor reach
the chosen loop vertex. -/
theorem reaches_of_twoChipsRepresentative_of_twoChipReflection
    {D : CFDiv G} {base target : G.V}
    (hRepresentative : HasTwoChipsRepresentative D base)
    (hReflection : TwoChipReflection base target) :
    StrongSeparator.Reaches G D target := by
  obtain ⟨E, hEEffective, hDE, hTwo⟩ := hRepresentative
  obtain ⟨reflected, script, hScript⟩ := hReflection
  let F : CFDiv G :=
    E - (2 : ℤ) • oneChip base + oneChip reflected
  have hFEffective : effective F := by
    exact (Eff G).add_mem
      (effective_sub_two_chips hEEffective hTwo)
      (eff_one_chip reflected)
  have hRewrite :
      E - oneChip target + prin G script = F := by
    rw [hScript]
    dsimp [F]
    abel
  have hSubEquiv :
      linearEquiv G (D - oneChip target) (E - oneChip target) :=
    StrongSeparator.linearEquiv_sub_one_chip hDE target
  have hFireEquiv :
      linearEquiv G (E - oneChip target)
        (E - oneChip target + prin G script) :=
    StrongSeparator.linearEquiv_add_prin (E - oneChip target) script
  rw [hRewrite] at hFireEquiv
  exact ⟨F, hFEffective, hSubEquiv.trans hFireEquiv⟩

/-- A direct strong-separator wrapper: reaching every embedded core vertex of
a connected positive subdivision proves rank one.  This statement is useful
independently of loops and avoids forcing callers through the affine-potential
certificate format. -/
theorem bnExists_of_reaches_coreVertices
    {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (hConnected : graphConnected spec.graph)
    (D : CFDiv spec.graph) (degree : ℤ)
    (hDegree : deg D = degree)
    (hReaches : ∀ vertex : Fin n,
      StrongSeparator.Reaches spec.graph D (spec.coreVertex vertex)) :
    BNExists spec.graph 1 degree :=
  CoreVertexReachability.bnExists_of_reaches_coreVertices
    spec hConnected D degree hDegree hReaches

/-- The concrete positive subdivision carried by valid loop-split metadata. -/
def splitSubdivisionSpec {n : ℕ} {core : Pseudocore n}
    (data : Pseudocore.SplitMetadata core)
    (hValid : data.Valid)
    (length : Fin core.splitEdgeCount → ℕ)
    (hLength : ∀ edge, 0 < length edge) :
    SubdivisionGraph.Spec (n + core.loopCount) core.splitEdgeCount where
  core := data.splitCore
  length := length
  core_nonempty := by
    have hn := core.vertexCount_pos_of_valid hValid.1
    omega
  core_loopless := data.splitCore_loopless_of_valid hValid
  length_pos := hLength

/-- A compact, honest split-model form of the genus-four two-loop lemma.

The marker count identifies the two-loop configurations covered by the
theorem.  Original vertices are discharged by `hBaseReaches`.  For each semantic
loop, `hLoopWitness` supplies the two independent ingredients formalized
above, after which the embedded-core strong-separator theorem handles every
subdivision-interior vertex automatically. -/
theorem bnExists_three_of_two_loop_split_witness
    {n : ℕ} (core : Pseudocore n)
    (data : Pseudocore.SplitMetadata core)
    (hValid : data.Valid) (_hTwoLoops : 2 ≤ core.loopCount)
    (length : Fin core.splitEdgeCount → ℕ)
    (hLength : ∀ edge, 0 < length edge)
    (D : CFDiv (splitSubdivisionSpec data hValid length hLength).graph)
    (hDegree : deg D = 3)
    (hBaseReaches : ∀ base : Fin n,
      StrongSeparator.Reaches
        (splitSubdivisionSpec data hValid length hLength).graph D
        ((splitSubdivisionSpec data hValid length hLength).coreVertex
          (core.baseVertex base)))
    (hLoopWitness : ∀ marker : Fin core.loopCount,
      HasTwoChipsRepresentative D
          ((splitSubdivisionSpec data hValid length hLength).coreVertex
            (core.baseVertex (data.markerBase marker))) ∧
        TwoChipReflection
          (G := (splitSubdivisionSpec data hValid length hLength).graph)
          ((splitSubdivisionSpec data hValid length hLength).coreVertex
            (core.baseVertex (data.markerBase marker)))
          ((splitSubdivisionSpec data hValid length hLength).coreVertex
            (core.markerVertex marker))) :
    BNExists (splitSubdivisionSpec data hValid length hLength).graph 1 3 := by
  let spec := splitSubdivisionSpec data hValid length hLength
  have hConnected : graphConnected spec.graph := by
    exact spec.graph_connected_of_coreConnected
      (data.splitCore_connected_of_valid hValid)
  apply bnExists_of_reaches_coreVertices spec hConnected D 3 hDegree
  intro vertex
  let part : Fin n ⊕ Fin core.loopCount :=
    (@finSumFinEquiv n core.loopCount).symm vertex
  rcases hPart : part with base | marker
  · have hVertex : core.baseVertex base = vertex := by
      have hApply := (@finSumFinEquiv n core.loopCount).apply_symm_apply vertex
      rw [show (@finSumFinEquiv n core.loopCount).symm vertex = Sum.inl base by
        exact hPart] at hApply
      simpa [Pseudocore.baseVertex] using hApply
    rw [← hVertex]
    exact hBaseReaches base
  · have hVertex : core.markerVertex marker = vertex := by
      have hApply := (@finSumFinEquiv n core.loopCount).apply_symm_apply vertex
      rw [show (@finSumFinEquiv n core.loopCount).symm vertex = Sum.inr marker by
        exact hPart] at hApply
      simpa [Pseudocore.markerVertex] using hApply
    rw [← hVertex]
    exact reaches_of_twoChipsRepresentative_of_twoChipReflection
      (hLoopWitness marker).1 (hLoopWitness marker).2

end Utilities.Certificate.GenusFourLoopLemma
