/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.GenericFarWitness

/-!
# Normalized coordinates for the far-mark construction

`SameStrand` and `GenericRankWitness` deliberately state their Dhar lemmas in
the stored `pathVertex` coordinates.  The paper, and the far-mark statements,
use the normalized `strandVertex` coordinates instead.  This file is the
small adapter between those two interfaces.  In particular, it does not
attempt the far-mark case split itself: it exposes the rank-zero and
rank-minus-one three-chip facts that each case consumes.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec


/-! The normalized/raw coordinate adapter (`normalizedPathPosition`,
`strandVertex_eq_pathVertex_normalized`, `normalizedPathPosition_isInterior`)
now lives in `BananaBasics.lean`, since several files need it. -/

/-- Far normalized positions remain far after changing the stored path
orientation.  This is the arithmetic part of the paper's far-mark
construction; it is independent of the choice of auxiliary chips. -/
theorem normalizedPathPosition_far {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (i : B.PathPosition α)
    (hi : 2 ≤ i.val ∧ i.val + 2 ≤ B.length α) :
    2 ≤ (normalizedPathPosition B α i).val ∧
      (normalizedPathPosition B α i).val + 2 ≤ B.length α := by
  unfold normalizedPathPosition
  split
  · exact hi
  · simp only []
    omega

/-- Package a normalized far mark as the raw path vertex and coordinate
facts consumed by the path-firing lemmas. -/
theorem far_mark_to_raw {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (i : B.PathPosition α) (x : B.graph.V)
    (hx : strandVertex B α i = x)
    (hi : 2 ≤ i.val ∧ i.val + 2 ≤ B.length α) :
    ∃ p : B.PathPosition α,
      B.pathVertex α p = x ∧
      2 ≤ p.val ∧ p.val + 2 ≤ B.length α := by
  refine ⟨normalizedPathPosition B α i, ?_, normalizedPathPosition_far B α i hi⟩
  simpa [strandVertex_eq_pathVertex_normalized] using hx

private theorem normalized_ne_of_strand_ne {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β)
    (h : strandVertex B α i ≠ strandVertex B β j) :
    B.pathVertex α (normalizedPathPosition B α i) ≠
      B.pathVertex β (normalizedPathPosition B β j) := by
  intro h'
  apply h
  rw [strandVertex_eq_pathVertex_normalized,
    strandVertex_eq_pathVertex_normalized]
  exact h'

/-- Three interior chips on two distinct normalized strands leave rank `-1`
after deleting a distinct third interior chip.  The third chip may be on
either of the two marked strands; this is the form used by the far-mark
construction after a path slide. -/
theorem rank_strand_pair_sub_of_distinct_interior
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : 0 < i.val ∧ i.val < B.length α)
    (hj : 0 < j.val ∧ j.val < B.length β)
    (hq : 0 < q.val ∧ q.val < B.length γ)
    (hαβ : α ≠ β)
    (hqx : strandVertex B γ q ≠ strandVertex B α i)
    (hqy : strandVertex B γ q ≠ strandVertex B β j) :
    rank B.graph
      (oneChip (strandVertex B α i) + oneChip (strandVertex B β j) -
        oneChip (strandVertex B γ q)) = -1 := by
  let pα := normalizedPathPosition B α i
  let pβ := normalizedPathPosition B β j
  let pγ := normalizedPathPosition B γ q
  have hpα : B.IsInteriorPosition α pα := by
    exact normalizedPathPosition_isInterior B α i hi
  have hpβ : B.IsInteriorPosition β pβ := by
    exact normalizedPathPosition_isInterior B β j hj
  have hpγ : B.IsInteriorPosition γ pγ := by
    exact normalizedPathPosition_isInterior B γ q hq
  have hqx' : B.pathVertex γ pγ ≠ B.pathVertex α pα := by
    exact normalized_ne_of_strand_ne B γ α q i hqx
  have hqy' : B.pathVertex γ pγ ≠ B.pathVertex β pβ := by
    exact normalized_ne_of_strand_ne B γ β q j hqy
  have hRaw := cross_strand_rank_zero_three_chip_witness
    hg B α β γ pα pβ pγ hpα hpβ hpγ hαβ hqx' hqy'
  simpa [pα, pβ, pγ, strandVertex_eq_pathVertex_normalized] using hRaw.2

/-- The positive two-chip companion of
`rank_strand_pair_sub_of_distinct_interior`. -/
theorem rank_strand_pair_zero_of_distinct_interior
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : 0 < i.val ∧ i.val < B.length α)
    (hj : 0 < j.val ∧ j.val < B.length β)
    (hq : 0 < q.val ∧ q.val < B.length γ)
    (hαβ : α ≠ β)
    (hqx : strandVertex B γ q ≠ strandVertex B α i)
    (hqy : strandVertex B γ q ≠ strandVertex B β j) :
    rank B.graph
      (oneChip (strandVertex B α i) + oneChip (strandVertex B β j)) = 0 := by
  let pα := normalizedPathPosition B α i
  let pβ := normalizedPathPosition B β j
  let pγ := normalizedPathPosition B γ q
  have hpα : B.IsInteriorPosition α pα := by
    exact normalizedPathPosition_isInterior B α i hi
  have hpβ : B.IsInteriorPosition β pβ := by
    exact normalizedPathPosition_isInterior B β j hj
  have hpγ : B.IsInteriorPosition γ pγ := by
    exact normalizedPathPosition_isInterior B γ q hq
  have hqx' : B.pathVertex γ pγ ≠ B.pathVertex α pα := by
    exact normalized_ne_of_strand_ne B γ α q i hqx
  have hqy' : B.pathVertex γ pγ ≠ B.pathVertex β pβ := by
    exact normalized_ne_of_strand_ne B γ β q j hqy
  have hRaw := cross_strand_rank_zero_three_chip_witness
    hg B α β γ pα pβ pγ hpα hpβ hpγ hαβ hqx' hqy'
  simpa [pα, pβ, pγ, strandVertex_eq_pathVertex_normalized] using hRaw.1

end Bananas
