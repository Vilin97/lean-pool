/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
import LeanPool.BrillNoetherGraphs.Utilities.Segments.SegmentReflection

/-!
# Elementary geometry of normalized banana coordinates

The reusable subdivision representation stores each parallel core edge with an
arbitrary orientation.  These lemmas certify that `strandVertex` repairs that
choice and agrees with the paper's common two-endpoint coordinates.
-/

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

theorem fin_two_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- A loopless slot in a two-vertex core has the other vertex as its head. -/
theorem head_eq_other_of_tail
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hTail : B.core.tail α = 0) : B.core.head α = 1 := by
  rcases fin_two_eq_zero_or_one (B.core.head α) with hHead | hHead
  · exfalso
    apply B.core_loopless α
    simp [hTail, hHead]
  · exact hHead

/-- A loopless slot in a two-vertex core has the other vertex as its tail. -/
theorem tail_eq_other_of_head
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (hHead : B.core.head α = 0) : B.core.tail α = 1 := by
  rcases fin_two_eq_zero_or_one (B.core.tail α) with hTail | hTail
  · exfalso
    apply B.core_loopless α
    simp [hTail, hHead]
  · exact hTail

/-- Coordinate zero on every strand is the common left endpoint. -/
theorem strandVertex_zero {g : ℕ} (B : Banana g) (α : Fin (g + 1)) :
    strandVertex B α ⟨0, by omega⟩ = leftEndpoint B := by
  unfold strandVertex
  by_cases hTail : B.core.tail α = 0
  · simpa [hTail, leftEndpoint] using B.pathVertex_zero α
  · have hTail' : B.core.tail α = 1 := by
      rcases fin_two_eq_zero_or_one (B.core.tail α) with h | h
      · exact (hTail h).elim
      · exact h
    have hHead : B.core.head α = 0 := by
      rcases fin_two_eq_zero_or_one (B.core.head α) with h | h
      · exact h
      · exfalso
        apply B.core_loopless α
        simp [hTail', h]
    simp [hTail, hHead, leftEndpoint]

/-- Coordinate `length α` on every strand is the common right endpoint. -/
theorem strandVertex_length {g : ℕ} (B : Banana g) (α : Fin (g + 1)) :
    strandVertex B α ⟨B.length α, by omega⟩ = rightEndpoint B := by
  unfold strandVertex
  by_cases hTail : B.core.tail α = 0
  · have hHead := head_eq_other_of_tail B α hTail
    simp [hTail, hHead, rightEndpoint]
  · have hTail' : B.core.tail α = 1 := by
      rcases fin_two_eq_zero_or_one (B.core.tail α) with h | h
      · exact (hTail h).elim
      · exact h
    simpa [hTail, hTail', rightEndpoint] using B.pathVertex_zero α

/-- The stored path position corresponding to a normalized strand position.
`SubdivisionGraph.Spec` allows a slot to be stored in either orientation;
this picks out whichever raw path position `strandVertex` actually reads
from. -/
def normalizedPathPosition {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) : B.PathPosition α :=
  if B.core.tail α = 0 then i else
    ⟨B.length α - i.val, by
      have hi := i.isLt
      omega⟩

/-- `strandVertex` is `pathVertex` at the corresponding stored position. -/
theorem strandVertex_eq_pathVertex_normalized {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (i : B.PathPosition α) :
    strandVertex B α i = B.pathVertex α (normalizedPathPosition B α i) := by
  rfl

/-- Interior normalized positions remain interior after changing storage
orientation. -/
theorem normalizedPathPosition_isInterior {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (i : B.PathPosition α)
    (hi : 0 < i.val ∧ i.val < B.length α) :
    B.IsInteriorPosition α (normalizedPathPosition B α i) := by
  unfold normalizedPathPosition SubdivisionGraph.Spec.IsInteriorPosition
  split <;> simp_all
  omega

/-- Bundled form of `normalizedPathPosition`: a normalized strand position
always has a raw path-position witness that agrees with `strandVertex` and
transports interiority. -/
theorem exists_normalized_pathPosition {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (i : B.PathPosition α) :
    ∃ p : B.PathPosition α, strandVertex B α i = B.pathVertex α p ∧
      (B.IsInteriorPosition α i → B.IsInteriorPosition α p) :=
  ⟨normalizedPathPosition B α i, strandVertex_eq_pathVertex_normalized B α i,
    fun hi => normalizedPathPosition_isInterior B α i
      (by change 0 < i.val ∧ i.val < B.length α at hi; exact hi)⟩

/-- On a fixed strand, normalized positions name distinct vertices. -/
theorem strandVertex_injective {g : ℕ} (B : Banana g) (α : Fin (g + 1)) :
    Function.Injective (strandVertex B α) := by
  intro i j h
  unfold strandVertex at h
  by_cases hTail : B.core.tail α = 0
  · simp only [hTail, ↓reduceIte] at h
    exact B.pathVertex_injective α h
  · simp only [hTail, ↓reduceIte] at h
    have hPositions := B.pathVertex_injective α h
    apply Fin.ext
    have hValues := congrArg Fin.val hPositions
    have hi : i.val ≤ B.length α := Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ B.length α := Nat.le_of_lt_succ j.isLt
    have hReflect := congrArg (fun q : ℕ => B.length α - q) hValues
    simpa only [Nat.sub_sub_self hi, Nat.sub_sub_self hj] using hReflect

/-- A strictly positive normalized position is not the left endpoint. -/
theorem strandVertex_ne_leftEndpoint {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (hi : 0 < i.val) :
    strandVertex B α i ≠ leftEndpoint B := by
  intro h
  have hPositions : i = ⟨0, by omega⟩ := by
    apply strandVertex_injective B α
    calc
      strandVertex B α i = leftEndpoint B := h
      _ = strandVertex B α ⟨0, by omega⟩ := (strandVertex_zero B α).symm
  have hValue : i.val = 0 := congrArg Fin.val hPositions
  omega

/-- A position strictly before the end is not the right endpoint. -/
theorem strandVertex_ne_rightEndpoint {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (hi : i.val < B.length α) :
    strandVertex B α i ≠ rightEndpoint B := by
  intro h
  have hPositions : i = ⟨B.length α, by omega⟩ := by
    apply strandVertex_injective B α
    calc
      strandVertex B α i = rightEndpoint B := h
      _ = strandVertex B α ⟨B.length α, by omega⟩ := (strandVertex_length B α).symm
  have hValue : i.val = B.length α := congrArg Fin.val hPositions
  omega

/-- The two multivalent vertices of a banana are distinct.  (`coreVertex` is
`Sum.inl` on the nose, so this is `(0 : Fin 2) ≠ 1`.) -/
theorem leftEndpoint_ne_rightEndpoint {g : ℕ} (B : Banana g) :
    leftEndpoint B ≠ rightEndpoint B := by
  intro h
  simp [leftEndpoint, rightEndpoint, SubdivisionGraph.Spec.coreVertex] at h

/-- On every strand, the sum of the two endpoints is linearly equivalent to
the sum of a normalized position and its reflected position. -/
theorem endpoint_sum_linearEquiv_strand_reflection
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (i : B.PathPosition α) :
    linearEquiv B.graph
      (oneChip (leftEndpoint B) + oneChip (rightEndpoint B))
      (oneChip (strandVertex B α i) + oneChip (strandVertex B α (strandMirror B α i))) := by
  unfold linearEquiv
  apply (principal_iff_eq_prin B.graph _).mpr
  by_cases hTail : B.core.tail α = 0
  · refine ⟨SegmentReflection.script B α i, ?_⟩
    rw [SegmentReflection.prin_script_eq_reflectionDivisor]
    have hHead := head_eq_other_of_tail B α hTail
    have hSymm : SegmentReflection.symmetricPosition B α i = strandMirror B α i := by
      apply Fin.ext
      rfl
    rw [hSymm]
    ext x
    simp [leftEndpoint, rightEndpoint, strandVertex, strandMirror,
      hTail, hHead]
    ring
  · have hTail' : B.core.tail α = 1 := by
      rcases fin_two_eq_zero_or_one (B.core.tail α) with h | h
      · exact (hTail h).elim
      · exact h
    have hHead : B.core.head α = 0 := by
      rcases fin_two_eq_zero_or_one (B.core.head α) with h | h
      · exact h
      · exfalso
        apply B.core_loopless α
        simp [hTail', h]
    let p : B.PathPosition α := strandMirror B α i
    refine ⟨SegmentReflection.script B α p, ?_⟩
    rw [SegmentReflection.prin_script_eq_reflectionDivisor]
    have hSymm : SegmentReflection.symmetricPosition B α p = i := by
      apply Fin.ext
      dsimp [p, strandMirror]
      exact Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)
    rw [hSymm]
    ext x
    simp [leftEndpoint, rightEndpoint, strandVertex, strandMirror,
      hTail', hHead, p]
    have hPath :
        B.pathVertex α
          ⟨B.length α - (B.length α - i.val), by
            have hi := i.isLt
            omega⟩ = B.pathVertex α i := by
      congr 1
    rw [hPath]
    ring_nf

/-- Every physical vertex of a banana graph lies at some normalized
position on some strand: `strandVertex` is (jointly, over all strands)
surjective. -/
theorem strandVertex_surjective {g : ℕ} (B : Banana g) (x : B.graph.V) :
    ∃ (alpha : Fin (g + 1)) (i : B.PathPosition alpha),
      strandVertex B alpha i = x := by
  set alpha0 : Fin (g + 1) := ⟨0, by omega⟩
  rcases x with c | interior
  · rcases fin_two_eq_zero_or_one c with rfl | rfl
    · exact ⟨alpha0, ⟨0, by omega⟩, strandVertex_zero B alpha0⟩
    · exact ⟨alpha0, ⟨B.length alpha0, by omega⟩, strandVertex_length B alpha0⟩
  · obtain ⟨edge, offset⟩ := interior
    have hoffset := offset.isLt
    let p0 : B.PathPosition edge := ⟨offset.val + 1, by omega⟩
    have hInterior : B.IsInteriorPosition edge p0 := by
      constructor <;> (show _ ; simp only [p0]; omega)
    have hInvol :
        normalizedPathPosition B edge (normalizedPathPosition B edge p0) = p0 := by
      unfold normalizedPathPosition
      by_cases hTail : B.core.tail edge = 0
      · simp [hTail]
      · simp only [hTail, ↓reduceIte]
        apply Fin.ext
        have hp0le : p0.val ≤ B.length edge := Nat.le_of_lt_succ p0.isLt
        show B.length edge - (B.length edge - p0.val) = p0.val
        omega
    refine ⟨edge, normalizedPathPosition B edge p0, ?_⟩
    rw [strandVertex_eq_pathVertex_normalized, hInvol,
      B.pathVertex_eq_interiorVertex edge p0 hInterior]
    simp only [SubdivisionGraph.Spec.interiorVertex]
    congr 1

end Bananas
