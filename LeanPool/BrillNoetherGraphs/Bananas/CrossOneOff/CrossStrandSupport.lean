/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.FarMarkAPI
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffDelta

/-!
# The support of a cross-strand two-chip divisor

Paper source: `cor:suppUV` (Corollary 3.8).  Two chips at interior points of
distinct strands of a banana have rank support exactly at those two points.

`ThetaNonrecurrence` proves this for `Banana 2`, as the geometric input to the
non-recurrence argument.  This file gives the general-genus statement.  The
interior half is `FarMarkAPI.rank_strand_pair_sub_of_distinct_interior`; what
had to be added is the two multivalent vertices, which the banana normal form
handles directly: deleting an endpoint from a semibreak divisor puts a `-1`
endpoint coefficient into the normal form, and such a divisor has rank `-1`.
-/

@[expose] public section

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Every interior vertex is a normalized strand position.

`strandVertex` stores a strand in either orientation, so the position
realizing a given interior offset depends on `B.core.tail`. -/
theorem exists_interior_strandVertex {g : ℕ} (B : Banana g)
    (γ : Fin (g + 1)) (o : Fin (B.length γ - 1)) :
    ∃ q : B.PathPosition γ, B.IsInteriorPosition γ q ∧
      strandVertex B γ q = B.interiorVertex γ o := by
  have ho := o.isLt
  have hpos := B.length_pos γ
  have hp : B.IsInteriorPosition γ (⟨o.val + 1, by omega⟩ : B.PathPosition γ) := by
    change 0 < o.val + 1 ∧ o.val + 1 < B.length γ
    omega
  have hpv : B.pathVertex γ (⟨o.val + 1, by omega⟩ : B.PathPosition γ) =
      B.interiorVertex γ o := by
    rw [B.pathVertex_eq_interiorVertex γ _ hp]
    congr 1
  by_cases htail : B.core.tail γ = 0
  · refine ⟨⟨o.val + 1, by omega⟩, hp, ?_⟩
    unfold strandVertex
    rw [if_pos htail]
    exact hpv
  · refine ⟨⟨B.length γ - (o.val + 1), by omega⟩, ?_, ?_⟩
    · change 0 < B.length γ - (o.val + 1) ∧ B.length γ - (o.val + 1) < B.length γ
      omega
    · unfold strandVertex
      rw [if_neg htail]
      rw [show (⟨B.length γ - (B.length γ - (o.val + 1)), by omega⟩ :
          B.PathPosition γ) = (⟨o.val + 1, by omega⟩ : B.PathPosition γ) from
        Fin.ext (by simp; omega)]
      exact hpv

/-- TeX label: `cor:suppUV` (Corollary 3.8), general genus.

Two chips at interior points of distinct strands have rank support exactly at
those two points. -/
theorem rankSupport_two_interior_distinct_strands
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) :
    rankSupport B.graph
        (oneChip (strandVertex B α i) + oneChip (strandVertex B β j)) =
      {strandVertex B α i, strandVertex B β j} := by
  classical
  -- Keep the divisor written out: introducing a local abbreviation here can
  -- make `rw`/`rintro` unfold concrete vertex equality at substantial cost.
  have hgz : (2 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
  have hSemi : IsSemibreak B
      (oneChip (strandVertex B α i) + oneChip (strandVertex B β j)) :=
    isSemibreak_two_distinct_strand_chips B α β i j hi hj hαβ
  have hdegE : deg (oneChip (strandVertex B α i) +
      oneChip (strandVertex B β j)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  -- Deleting either multivalent vertex leaves a normal form with a negative
  -- endpoint coefficient, hence rank `-1`.
  have hLeft : rank B.graph (oneChip (strandVertex B α i) +
      oneChip (strandVertex B β j) - oneChip (leftEndpoint B)) = -1 := by
    have hform : oneChip (strandVertex B α i) + oneChip (strandVertex B β j) -
        oneChip (leftEndpoint B) =
        bananaNormalForm B (-1) 0 (oneChip (strandVertex B α i) +
          oneChip (strandVertex B β j)) := by
      rw [bananaNormalForm, neg_one_zsmul, zero_zsmul]
      abel
    rw [hform]
    exact (rank_bananaNormalForm_neg_iff B (-1) 0 _ hSemi le_rfl
      (by rw [hdegE]; omega)).2 (by omega)
  have hRight : rank B.graph (oneChip (strandVertex B α i) +
      oneChip (strandVertex B β j) - oneChip (rightEndpoint B)) = -1 := by
    have hform : oneChip (strandVertex B α i) + oneChip (strandVertex B β j) -
        oneChip (rightEndpoint B) =
        bananaNormalForm B 0 (-1) (oneChip (strandVertex B α i) +
          oneChip (strandVertex B β j)) := by
      rw [bananaNormalForm, zero_zsmul, neg_one_zsmul]
      abel
    rw [hform]
    apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
    · exact q_reduced_bananaNormalForm_right B 0 (-1) _ hSemi le_rfl
        (by rw [hdegE]; omega)
    · rw [bananaNormalForm_rightEndpoint B 0 (-1) _ hSemi]
      omega
  have heff : ∀ w : B.graph.V, 0 ≤ rank B.graph (oneChip w) := by
    intro w
    exact (rank_geq_iff B.graph (oneChip w) 0).mp
      ((rank_nonneg_iff_winnable B.graph (oneChip w)).mpr
        (winnable_of_effective B.graph (oneChip w) (eff_one_chip w)))
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx0
    -- `mem_rankSupport_iff` is `Iff.rfl`, so this is a defeq restatement.
    have hx : 0 ≤ rank B.graph (oneChip (strandVertex B α i) +
        oneChip (strandVertex B β j) - oneChip x) := hx0
    by_contra hne
    push Not at hne
    obtain ⟨hxu, hxv⟩ := hne
    have hneg : rank B.graph (oneChip (strandVertex B α i) +
        oneChip (strandVertex B β j) - oneChip x) = -1 := by
      rcases x with c | ⟨γ, o⟩
      · rcases fin_two_eq_zero_or_one c with rfl | rfl
        · exact hLeft
        · exact hRight
      · obtain ⟨q, hq, hqv⟩ := exists_interior_strandVertex B γ o
        rw [show (Sum.inr ⟨γ, o⟩ : B.graph.V) = strandVertex B γ q from hqv.symm]
        exact rank_strand_pair_sub_of_distinct_interior hg B α β γ i j q hi hj hq
          hαβ (by rw [hqv]; exact hxu) (by rw [hqv]; exact hxv)
    rw [hneg] at hx
    omega
  · rintro (rfl | rfl)
    · show 0 ≤ rank B.graph (oneChip (strandVertex B α i) +
        oneChip (strandVertex B β j) - oneChip (strandVertex B α i))
      rw [add_sub_cancel_left]
      exact heff _
    · show 0 ≤ rank B.graph (oneChip (strandVertex B α i) +
        oneChip (strandVertex B β j) - oneChip (strandVertex B β j))
      rw [add_comm (oneChip (strandVertex B α i))
        (oneChip (strandVertex B β j)), add_sub_cancel_left]
      exact heff _

/-- TeX label: `cor:suppUV` (Corollary 3.8), **general genus**.

Two chips at interior points of distinct strands of a banana of genus at least
two have rank support exactly at those two points.

`FarMarkAPI` already supplied `r(u + v - w) = -1` for every *interior* `w`
distinct from both marks; what completes the statement is the two multivalent
vertices, which the banana normal form handles directly: `u + v` is a
semibreak, so deleting an endpoint from it is a normal form with a negative
endpoint coefficient, and those have rank `-1`. -/
theorem suppUV
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) :
    rankSupport B.graph
        (oneChip (strandVertex B α i) + oneChip (strandVertex B β j)) =
      {strandVertex B α i, strandVertex B β j} :=
  rankSupport_two_interior_distinct_strands hg B α β i j hi hj hαβ

end Bananas
