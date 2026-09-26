/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.GenericRankWitness
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBasics

/-!
# Same-strand interior witnesses in arbitrary genus

This is the same-strand branch of the corrected Theorem 3.9.  The paper
refers back to the theta calculation, but the witness and its four rank
values are in fact genus-independent once there are at least three strands.

For normalized interior coordinates `i < j`, put `k = j - i` and
`D = v_i + v_k`.  The pair `v_i + v_k` is non-reflected and has rank zero;
after deleting `v_j` it slides to one of the two endpoint chips.  The two
other deletions are respectively one chip and a nonprincipal degree-zero
divisor.  Thus `rankDelta D = -1`.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

section Generic

variable {G : CFGraph}

private theorem add_sub_right_divisor (A C : CFDiv G) : A + C - C = A := by
  abel

private theorem add_sub_left_divisor (A C : CFDiv G) : A + C - A = C := by
  abel

private theorem pair_sub_first_sub_third (A C E : CFDiv G) :
    A + C - A - E = C - E := by
  abel

end Generic

private theorem length_lt_mirror_sum {n i k j : ℕ}
    (hi : i < n) (hk : k < n) (hij : i + k = j) (hj : j < n) :
    n < (n - i) + (n - k) := by
  omega

/-- Distinct vertices on a positive-genus banana determine a nonprincipal
degree-zero divisor, hence a divisor of rank `-1`. -/
theorem rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana_generic
    {g : ℕ} (hg : 1 ≤ g) (B : Banana g) (x y : B.graph.V) (hxy : x ≠ y) :
    rank B.graph (oneChip x - oneChip y) = -1 := by
  apply rank_eq_neg_one_of_degree_zero_not_linear_equiv B.graph
  · simp [deg.map_sub, deg_one_chip]
  · exact marks_not_linearEquiv hg B hxy

/-- Corrected Theorem 3.9, same-strand interior branch.

On a banana of genus at least two, any two distinct normalized interior marks
on one strand admit the explicit negative-rank-difference witness
`D = v_i + v_(j-i)`.  The theorem is stated for genus at least two because
that is the natural range of the rank calculation; Theorem 3.9 uses it with
`3 ≤ g`. -/
theorem exists_rankDelta_neg_same_strand_interior_generic
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val) :
    ∃ D : CFDiv B.graph,
      rankDelta (mark B.graph (strandVertex B alpha i)
        (strandVertex B alpha j)) D < 0 := by
  let k : B.PathPosition alpha := ⟨j.val - i.val, by
    have hSubLe : j.val - i.val ≤ j.val := Nat.sub_le _ _
    omega⟩
  have hk : B.IsInteriorPosition alpha k := by
    change 0 < j.val - i.val ∧ j.val - i.val < B.length alpha
    exact ⟨Nat.sub_pos_of_lt hij,
      lt_of_le_of_lt (Nat.sub_le _ _) hj.2⟩
  have hIK : i.val + k.val = j.val := by
    dsimp [k]
    rw [Nat.add_sub_of_le (Nat.le_of_lt hij)]
  have hkLtJ : k.val < j.val := by
    dsimp [k]
    exact Nat.sub_lt (lt_trans hi.1 hij) hi.1
  have hKJ : strandVertex B alpha k ≠ strandVertex B alpha j := by
    intro h
    have hVal := congrArg Fin.val (strandVertex_injective B alpha h)
    exact (ne_of_lt hkLtJ) hVal
  let D : CFDiv B.graph :=
    oneChip (strandVertex B alpha i) + oneChip (strandVertex B alpha k)
  have hRankD : rank B.graph D = 0 := by
    by_cases hTail : B.core.tail alpha = 0
    · have hI : strandVertex B alpha i = B.pathVertex alpha i := by
        unfold strandVertex
        rw [ite_eq_left hTail]
      have hK : strandVertex B alpha k = B.pathVertex alpha k := by
        unfold strandVertex
        rw [ite_eq_left hTail]
      dsimp [D]
      rw [hI, hK]
      apply rank_same_strand_pair_zero_of_not_reflection_generic hg
      intro hSum
      rw [hIK] at hSum
      exact (ne_of_lt hj.2) hSum
    · have hI : strandVertex B alpha i =
          B.pathVertex alpha (strandMirror B alpha i) := by
        unfold strandVertex strandMirror
        rw [ite_eq_right hTail]
      have hK : strandVertex B alpha k =
          B.pathVertex alpha (strandMirror B alpha k) := by
        unfold strandVertex strandMirror
        rw [ite_eq_right hTail]
      dsimp [D]
      rw [hI, hK]
      apply rank_same_strand_pair_zero_of_not_reflection_generic hg
      simp only [strandMirror]
      exact ne_of_gt (length_lt_mirror_sum hi.2 hk.2 hIK hj.2)
  have hRankU : rank B.graph
      (D - oneChip (strandVertex B alpha i)) = 0 := by
    have hCancel :
        D - oneChip (strandVertex B alpha i) =
          oneChip (G := B.graph) (strandVertex B alpha k) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact rank_one_chip_zero_of_banana (by omega) B _
  have hRankV : rank B.graph
      (D - oneChip (strandVertex B alpha j)) = 0 := by
    by_cases hTail : B.core.tail alpha = 0
    · have hI : strandVertex B alpha i = B.pathVertex alpha i := by
        unfold strandVertex
        rw [ite_eq_left hTail]
      have hK : strandVertex B alpha k = B.pathVertex alpha k := by
        unfold strandVertex
        rw [ite_eq_left hTail]
      have hJ : strandVertex B alpha j = B.pathVertex alpha j := by
        unfold strandVertex
        rw [ite_eq_left hTail]
      have hSlide := path_pair_linearEquiv_tail_sum B alpha i k hi.1 hk.1
        (by rw [hIK]; exact hj.2)
      have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
        hSlide (B.pathVertex alpha j)
      have hRankEq := rank_eq_of_linear_equiv B.graph hShift
      have hRight : rank B.graph
          (oneChip (B.coreVertex (B.core.tail alpha)) +
              oneChip (B.pathVertex alpha ⟨i.val + k.val, by omega⟩) -
            oneChip (B.pathVertex alpha j)) = 0 := by
        have hPath : B.pathVertex alpha ⟨i.val + k.val, by omega⟩ =
            B.pathVertex alpha j := by
          rw [B.pathVertex_eq_iff_val_eq]
          exact hIK
        rw [hPath, add_sub_right_divisor]
        exact rank_one_chip_zero_of_banana (by omega) B _
      rw [hRight] at hRankEq
      dsimp [D]
      rw [hI, hK, hJ]
      exact hRankEq
    · let i' := strandMirror B alpha i
      let k' := strandMirror B alpha k
      let j' := strandMirror B alpha j
      have hi' : B.IsInteriorPosition alpha i' := by
        change 0 < B.length alpha - i.val ∧
          B.length alpha - i.val < B.length alpha
        omega
      have hk' : B.IsInteriorPosition alpha k' := by
        change 0 < B.length alpha - k.val ∧
          B.length alpha - k.val < B.length alpha
        omega
      have hI : strandVertex B alpha i = B.pathVertex alpha i' := by
        unfold strandVertex
        rw [ite_eq_right hTail]
        rfl
      have hK : strandVertex B alpha k = B.pathVertex alpha k' := by
        unfold strandVertex
        rw [ite_eq_right hTail]
        rfl
      have hJ : strandVertex B alpha j = B.pathVertex alpha j' := by
        unfold strandVertex
        rw [ite_eq_right hTail]
        rfl
      have hPast : B.length alpha < i'.val + k'.val := by
        dsimp [i', k', strandMirror]
        exact length_lt_mirror_sum hi.2 hk.2 hIK hj.2
      have hSlide := path_pair_linearEquiv_head_excess B alpha i' k'
        hi'.2 hk'.2 hPast
      have hShift := Certificate.StrongSeparator.linearEquiv_sub_one_chip
        hSlide (B.pathVertex alpha j')
      have hRankEq := rank_eq_of_linear_equiv B.graph hShift
      have hExcess : B.pathVertex alpha
            ⟨i'.val + k'.val - B.length alpha, by omega⟩ =
          B.pathVertex alpha j' := by
        rw [B.pathVertex_eq_iff_val_eq]
        dsimp [i', k', j', strandMirror]
        omega
      have hRight : rank B.graph
          (oneChip (B.pathVertex alpha
              ⟨i'.val + k'.val - B.length alpha, by omega⟩) +
              oneChip (B.coreVertex (B.core.head alpha)) -
            oneChip (B.pathVertex alpha j')) = 0 := by
        rw [hExcess, add_sub_left_divisor]
        exact rank_one_chip_zero_of_banana (by omega) B _
      rw [hRight] at hRankEq
      dsimp [D]
      rw [hI, hK, hJ]
      exact hRankEq
  have hRankUV : rank B.graph
      (D - oneChip (strandVertex B alpha i) -
        oneChip (strandVertex B alpha j)) = -1 := by
    have hRank := rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana_generic
      (by omega) B (strandVertex B alpha k) (strandVertex B alpha j) hKJ
    have hCancel :
        D - oneChip (strandVertex B alpha i) -
            oneChip (strandVertex B alpha j) =
          oneChip (strandVertex B alpha k) -
            oneChip (strandVertex B alpha j) := by
      dsimp [D]
      exact pair_sub_first_sub_third _ _ _
    rw [hCancel]
    exact hRank
  refine ⟨D, ?_⟩
  unfold rankDelta mark
  rw [hRankD, hRankU, hRankV, hRankUV]
  norm_num

/-- Equal interior marks also admit a negative rank-difference witness in
positive genus.  Here the witness is the marked chip plus the normalized
left endpoint; deleting the (repeated) mark leaves one endpoint chip, while
deleting it twice leaves a nonprincipal degree-zero divisor. -/
theorem exists_rankDelta_neg_same_strand_interior_self_generic
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (i : B.PathPosition alpha) (hi : B.IsInteriorPosition alpha i) :
    ∃ D : CFDiv B.graph,
      rankDelta (mark B.graph (strandVertex B alpha i)
        (strandVertex B alpha i)) D < 0 := by
  let z : B.PathPosition alpha := ⟨0, by omega⟩
  have hZ : strandVertex B alpha z = leftEndpoint B := by
    simpa [z] using strandVertex_zero B alpha
  have hIZ : strandVertex B alpha i ≠ leftEndpoint B := by
    intro h
    have hEq : strandVertex B alpha i = strandVertex B alpha z := by
      rw [hZ]
      exact h
    have hVal := congrArg Fin.val (strandVertex_injective B alpha hEq)
    dsimp [z] at hVal
    exact (Nat.ne_of_gt hi.1) hVal
  let D : CFDiv B.graph :=
    oneChip (strandVertex B alpha i) + oneChip (leftEndpoint B)
  have hRankD : rank B.graph D = 0 := by
    by_cases hTail : B.core.tail alpha = 0
    · have hI : strandVertex B alpha i = B.pathVertex alpha i := by
        unfold strandVertex
        rw [ite_eq_left hTail]
      have hLeft : leftEndpoint B = B.pathVertex alpha z := by
        rw [← hZ]
        unfold strandVertex
        rw [ite_eq_left hTail]
      dsimp [D]
      rw [hI, hLeft]
      apply rank_same_strand_pair_zero_of_not_reflection_generic hg
      dsimp [z]
      exact ne_of_lt hi.2
    · have hI : strandVertex B alpha i =
          B.pathVertex alpha (strandMirror B alpha i) := by
        unfold strandVertex strandMirror
        rw [ite_eq_right hTail]
      have hLeft : leftEndpoint B = B.pathVertex alpha
          ⟨B.length alpha, by omega⟩ := by
        rw [B.pathVertex_length]
        unfold leftEndpoint
        have hHead : B.core.head alpha = 0 := by
          apply Fin.ext
          have hTailVal : (B.core.tail alpha).val ≠ 0 := by
            intro h
            apply hTail
            apply Fin.ext
            exact h
          have hLoopVal : (B.core.tail alpha).val ≠ (B.core.head alpha).val := by
            intro h
            exact B.core_loopless alpha (Fin.ext h)
          have ht := (B.core.tail alpha).isLt
          have hh := (B.core.head alpha).isLt
          omega
        rw [hHead]
      dsimp [D]
      rw [hI, hLeft]
      apply rank_same_strand_pair_zero_of_not_reflection_generic hg
      simp only [strandMirror]
      have hPos : 0 < B.length alpha - i.val := Nat.sub_pos_of_lt hi.2
      omega
  have hRankU : rank B.graph
      (D - oneChip (strandVertex B alpha i)) = 0 := by
    have hCancel :
        D - oneChip (strandVertex B alpha i) =
          oneChip (G := B.graph) (leftEndpoint B) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact rank_one_chip_zero_of_banana (by omega) B _
  have hRankUU : rank B.graph
      (D - oneChip (strandVertex B alpha i) -
        oneChip (strandVertex B alpha i)) = -1 := by
    have hRank := rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana_generic
      (by omega) B (leftEndpoint B) (strandVertex B alpha i) hIZ.symm
    have hCancel :
        D - oneChip (strandVertex B alpha i) -
            oneChip (strandVertex B alpha i) =
          oneChip (leftEndpoint B) -
            oneChip (strandVertex B alpha i) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact hRank
  refine ⟨D, ?_⟩
  unfold rankDelta mark
  rw [hRankD, hRankU, hRankUU]
  norm_num

/-- The marked rank difference is symmetric in the two marked vertices. -/
private theorem rankDelta_swap_marks_generic
    (G : CFGraph) (u v : G.V) (D : CFDiv G) :
    rankDelta (mark G u v) D = rankDelta (mark G v u) D := by
  have hSub : D - oneChip u - oneChip v =
      D - oneChip v - oneChip u := by
    abel
  unfold rankDelta mark
  rw [hSub]
  ring

/-- Full same-strand interior branch of corrected Theorem 3.9, including
both coordinate orders and coincident marks. -/
theorem exists_rankDelta_neg_same_strand_interior_any_order
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (alpha : Fin (g + 1))
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j) :
    ∃ D : CFDiv B.graph,
      rankDelta (mark B.graph (strandVertex B alpha i)
        (strandVertex B alpha j)) D < 0 := by
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact exists_rankDelta_neg_same_strand_interior_generic
      hg B alpha i j hi hj hij
  · have hIJ : i = j := Fin.ext hij
    subst j
    exact exists_rankDelta_neg_same_strand_interior_self_generic hg B alpha i hi
  · obtain ⟨D, hD⟩ := exists_rankDelta_neg_same_strand_interior_generic
      hg B alpha j i hj hi hij
    refine ⟨D, ?_⟩
    rw [rankDelta_swap_marks_generic]
    exact hD

end Bananas
