/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrand
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossStrandSupport
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrandEndpointNegative
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaExceptionalArithmetic

/-!
# Boundary submodularity on theta graphs

The interior part of paper Theorem 3.4 was already formalized in
`ThetaExceptionalArithmetic`.  This file treats the genuinely informative
boundary cases.  We first work in the subdivision spec's stored path
coordinates; normalized-coordinate wrappers are supplied below.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

section Generic

/-- Projection-clean wrapper around the genus-two one-chip reduction.  Keeping
this lemma abstract prevents the elaborator from unfolding `oneChip` on a
concrete subdivision vertex type merely to compare `mark G u v` with `G`. -/
theorem exists_vertex_rep_of_rankDelta_neg_genus_two
    (G : CFGraph) (u v : G.V) (D : CFDiv G)
    (hConn : _root_.graphConnected G) (hGenus : genus G = 2)
    (hDistinct : ¬ linearEquiv G (oneChip u - oneChip v) 0)
    (hNeg : rankDelta (mark G u v) D < 0) :
    ∃ w : G.V,
      linearEquiv G (D - oneChip u) (oneChip w) ∧
      qReduced G v (oneChip w) ∧
      w ≠ v ∧
      rank G (oneChip w + oneChip u - oneChip v) = 0 := by
  have hBase :=
    exists_qReduced_vertex_rep_of_rankDelta_neg_genus_two
      (mark G u v) D hConn hGenus hDistinct hNeg
  change ∃ w : G.V,
    linearEquiv G (D - oneChip u) (oneChip w) ∧
    qReduced G v (oneChip w) ∧
    w ≠ v ∧ rank G (oneChip w + oneChip u - oneChip v) = 0 at hBase
  exact hBase

/-- Abstract `mark` wrapper for the pointwise form of all-divisor
submodularity. -/
theorem allSubmodular_mark_of_rankDelta_nonneg
    (G : CFGraph) (u v : G.V)
    (h : ∀ D : CFDiv G, 0 ≤ rankDelta (mark G u v) D) :
    AllSubmodular (mark G u v) := by
  exact (allSubmodular_iff_rankDelta_nonneg (mark G u v)).mpr h

theorem rankDelta_mark_swap_boundary
    (G : CFGraph) (u v : G.V) (D : CFDiv G) :
    rankDelta (mark G u v) D = rankDelta (mark G v u) D := by
  have hSub : D - oneChip u - oneChip v =
      D - oneChip v - oneChip u := by
    abel
  unfold rankDelta mark
  rw [hSub]
  ring

/-- All-divisor submodularity is symmetric in the two marks.  This local
generic wrapper avoids unfolding concrete banana divisors during transport. -/
theorem allSubmodular_mark_swap
    (G : CFGraph) (u v : G.V)
    (h : AllSubmodular (mark G u v)) :
    AllSubmodular (mark G v u) := by
  apply allSubmodular_mark_of_rankDelta_nonneg
  intro D
  have hNonneg := (allSubmodular_iff_rankDelta_nonneg (mark G u v)).mp h D
  rw [← rankDelta_mark_swap_boundary G u v D]
  exact hNonneg

end Generic

/-- Distinct strictly interior theta strands give an all-submodular marking.
This is the first case of Corollary 3.6, kept here independently of the
statement ledger so the complete iff below has no circular import. -/
theorem theta_allSubmodular_of_distinct_interior_strands
    (B : Banana 2) (alpha beta : Fin 3) (i : B.PathPosition alpha)
    (j : B.PathPosition beta) (hab : alpha ≠ beta)
    (hi : 0 < i.val ∧ i.val < B.length alpha)
    (hj : 0 < j.val ∧ j.val < B.length beta) :
    AllSubmodular
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) := by
  rw [allSubmodular_iff_rankDelta_nonneg]
  intro D
  by_contra hNeg
  have hNeg' : rankDelta
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) D < 0 := by
    omega
  let p : B.PathPosition alpha := normalizedPathPosition B alpha i
  let q : B.PathPosition beta := normalizedPathPosition B beta j
  have hp : B.IsInteriorPosition alpha p :=
    normalizedPathPosition_isInterior B alpha i hi
  have hq : B.IsInteriorPosition beta q :=
    normalizedPathPosition_isInterior B beta j hj
  have hu : strandVertex B alpha i = B.pathVertex alpha p :=
    strandVertex_eq_pathVertex_normalized B alpha i
  have hv : strandVertex B beta j = B.pathVertex beta q :=
    strandVertex_eq_pathVertex_normalized B beta j
  have huv : strandVertex B alpha i ≠ strandVertex B beta j := by
    intro huv
    rw [hu, hv] at huv
    have hab' := (interior_and_strand_eq_of_pathVertex_eq_interior B alpha beta
      p q hq huv).2
    exact hab hab'
  obtain ⟨w, hw, _hred, hwv, hPair⟩ :=
    exists_qReduced_vertex_rep_of_rankDelta_neg_genus_two
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) D
      (graphConnected B) B.genus_graph
      (marks_not_linearEquiv (by omega) B huv) hNeg'
  let wB : B.graph.V := (show B.graph.V from w)
  have hDRank : rank
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)).graph D = 0 :=
    rank_eq_zero_of_rankDelta_neg_genus_two
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) D
      (graphConnected B) B.genus_graph
      (marks_not_linearEquiv (by omega) B huv) hNeg'
  have hPair' : rank
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)).graph
      (oneChip w + oneChip (B.pathVertex alpha p)) = 0 := by
    have hShift : linearEquiv
        (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)).graph D
        (oneChip w + oneChip
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)).u) := by
      unfold linearEquiv at hw ⊢
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hw
    have hRankShift := rank_eq_of_linear_equiv
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)).graph hShift
    rw [hDRank] at hRankShift
    have hPairMark : rank
        (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)).graph
        (oneChip w + oneChip
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)).u) = 0 := by
      omega
    simpa [mark, hu] using hPairMark
  have hwvPath : wB ≠ B.pathVertex beta q := by
    intro h
    apply hwv
    change w = B.pathVertex beta q
    rw [hv]
    exact h
  have hPairB : rank B.graph
      (oneChip wB + oneChip (B.pathVertex alpha p)) = 0 := by
    exact hPair'
  have hNotZero := rank_aux_add_mark_sub_distinct_mark_ne_zero
    B alpha beta p q hp hq hab wB hwvPath hPairB
  apply hNotZero
  have hPairB' : rank B.graph
      (oneChip wB + oneChip (strandVertex B alpha i) -
        oneChip (strandVertex B beta j)) = 0 := by
    exact hPair
  simpa [hu, hv, add_comm, add_left_comm, add_assoc] using hPairB'

/-- Paper sources: `thm-NonSubmodGenus2` (Theorem 3.4) and
`cor-allSubmodSameStrand` (Corollary 3.6), boundary pair `(0,n-1)`.

On a theta strand of length at least two, marking the stored-coordinate
initial endpoint and the penultimate vertex makes every divisor submodular.
The proof follows the paper's genus-two reduction.  A hypothetical negative
rank difference gives a one-chip auxiliary vertex `w`; the same-strand
interval theorem forces `w` to be either the penultimate vertex or the other
endpoint, while the reduction excludes both. -/
theorem theta_allSubmodular_path_zero_penultimate
    (B : Banana 2) (alpha : Fin 3) (hlen : 2 ≤ B.length alpha) :
    AllSubmodular
      (mark B.graph
        (B.pathVertex alpha ⟨0, by omega⟩)
        (B.pathVertex alpha ⟨B.length alpha - 1, by omega⟩)) := by
  apply allSubmodular_mark_of_rankDelta_nonneg
  intro D
  by_contra hNot
  have hNeg : rankDelta
      (mark B.graph
        (B.pathVertex alpha ⟨0, by omega⟩)
        (B.pathVertex alpha ⟨B.length alpha - 1, by omega⟩)) D < 0 := by
    omega
  let i : B.PathPosition alpha := ⟨0, by omega⟩
  let j : B.PathPosition alpha := ⟨B.length alpha - 1, by omega⟩
  have hij : i.val < j.val := by
    dsimp [i, j]
    omega
  have huv : B.pathVertex alpha i ≠ B.pathVertex alpha j := by
    intro h
    have hval := congrArg Fin.val (B.pathVertex_injective alpha h)
    exact (ne_of_lt hij) hval
  have hDistinct : ¬ linearEquiv B.graph
      (oneChip (B.pathVertex alpha i) - oneChip (B.pathVertex alpha j)) 0 :=
    marks_not_linearEquiv (by omega) B huv
  have hNeg' : rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D < 0 := by
    simpa [i, j] using hNeg
  obtain ⟨w, hw, _hwReduced, hwv, hSub⟩ :=
    exists_vertex_rep_of_rankDelta_neg_genus_two B.graph
      (B.pathVertex alpha i) (B.pathVertex alpha j) D
      (graphConnected B) B.genus_graph hDistinct hNeg'
  have hDRank : rank B.graph D = 0 :=
    rank_eq_zero_of_rankDelta_neg_genus_two
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D
      (graphConnected B) B.genus_graph hDistinct hNeg'
  have hDPair : linearEquiv B.graph D
      (oneChip w + oneChip (B.pathVertex alpha i)) := by
    unfold linearEquiv at hw ⊢
    have hEq :
        (oneChip w + oneChip (B.pathVertex alpha i)) - D =
          oneChip w - (D - oneChip (B.pathVertex alpha i)) := by
      abel
    rw [hEq]
    exact hw
  have hPair : rank B.graph
      (oneChip w + oneChip (B.pathVertex alpha i)) = 0 := by
    rw [← rank_eq_of_linear_equiv B.graph hDPair]
    exact hDRank
  have hNoOnStrand (k : B.PathPosition alpha)
      (hwk : w = B.pathVertex alpha k) : False := by
    have hPair' : rank B.graph
        (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k)) = 0 := by
      rw [← hwk]
      simpa [add_comm] using hPair
    have hSub' : rank B.graph
        (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k) -
          oneChip (B.pathVertex alpha j)) = 0 := by
      rw [← hwk]
      simpa [add_comm] using hSub
    obtain ⟨hkReflect, hkLower, _hkUpper⟩ :=
      same_strand_pair_sub_zero_forces_interval_general
        B alpha i j k hij hPair' hSub'
    have hkNotJ : k ≠ j := by
      intro hkj
      apply hwv
      rw [hwk, hkj]
    have hkNotJVal : k.val ≠ j.val := by
      intro hval
      exact hkNotJ (Fin.ext hval)
    have hkBound := k.isLt
    dsimp [i, j] at hkReflect hkLower hkNotJVal
    omega
  rcases w with e | ⟨gamma, offset⟩
  · obtain hEnd | hEnd := coreVertex_eq_pathVertex_zero_or_length B alpha e
    · exact hNoOnStrand ⟨0, by omega⟩ hEnd
    · exact hNoOnStrand ⟨B.length alpha, by omega⟩ hEnd
  · let k : B.PathPosition gamma := ⟨offset.val + 1, by
      have hoff := offset.isLt
      have hlenGamma := B.length_pos gamma
      omega⟩
    have hk : B.IsInteriorPosition gamma k := by
      change 0 < offset.val + 1 ∧ offset.val + 1 < B.length gamma
      have hoff := offset.isLt
      have hlenGamma := B.length_pos gamma
      omega
    have hwPath : B.interiorVertex gamma offset = B.pathVertex gamma k := by
      rw [B.pathVertex_eq_interiorVertex gamma k hk]
      congr 1
    have hwDef :
        (Sum.inr ⟨gamma, offset⟩ : B.graph.V) =
          B.interiorVertex gamma offset := rfl
    rw [hwDef] at hPair hSub hwv
    by_cases hgamma : gamma = alpha
    · subst gamma
      exact hNoOnStrand k hwPath
    · have hj : B.IsInteriorPosition alpha j := by
        change 0 < B.length alpha - 1 ∧ B.length alpha - 1 < B.length alpha
        omega
      have hCore : B.pathVertex alpha i = B.coreVertex (B.core.tail alpha) := by
        dsimp [i]
        exact B.pathVertex_zero alpha
      have hNeZero := rank_coreVertex_add_distinct_interior_path_marks_ne_zero
        B (B.core.tail alpha) gamma alpha k j hk hj hgamma
      apply hNeZero
      rw [← hwPath, ← hCore]
      simpa [add_comm] using hSub

/-- Paper sources: `thm-NonSubmodGenus2` (Theorem 3.4) and
`cor-allSubmodSameStrand` (Corollary 3.6), boundary pair `(1,n)`.

On a theta strand of length at least two, marking the first interior vertex
and the stored-coordinate terminal endpoint makes every divisor submodular.
For an auxiliary vertex on another strand, `cor:suppUV` rules out the needed
rank-zero deletion at the endpoint; the on-strand case is again excluded by
the interval calculation. -/
theorem theta_allSubmodular_path_one_length
    (B : Banana 2) (alpha : Fin 3) (hlen : 2 ≤ B.length alpha) :
    AllSubmodular
      (mark B.graph
        (B.pathVertex alpha ⟨1, by omega⟩)
        (B.pathVertex alpha ⟨B.length alpha, by omega⟩)) := by
  apply allSubmodular_mark_of_rankDelta_nonneg
  intro D
  by_contra hNot
  have hNeg : rankDelta
      (mark B.graph
        (B.pathVertex alpha ⟨1, by omega⟩)
        (B.pathVertex alpha ⟨B.length alpha, by omega⟩)) D < 0 := by
    omega
  let i : B.PathPosition alpha := ⟨1, by omega⟩
  let j : B.PathPosition alpha := ⟨B.length alpha, by omega⟩
  have hij : i.val < j.val := by
    dsimp [i, j]
    omega
  have hi : B.IsInteriorPosition alpha i := by
    change 0 < i.val ∧ i.val < B.length alpha
    dsimp [i]
    omega
  have huv : B.pathVertex alpha i ≠ B.pathVertex alpha j := by
    intro h
    have hval := congrArg Fin.val (B.pathVertex_injective alpha h)
    exact (ne_of_lt hij) hval
  have hDistinct : ¬ linearEquiv B.graph
      (oneChip (B.pathVertex alpha i) - oneChip (B.pathVertex alpha j)) 0 :=
    marks_not_linearEquiv (by omega) B huv
  have hNeg' : rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D < 0 := by
    simpa [i, j] using hNeg
  obtain ⟨w, hw, _hwReduced, hwv, hSub⟩ :=
    exists_vertex_rep_of_rankDelta_neg_genus_two B.graph
      (B.pathVertex alpha i) (B.pathVertex alpha j) D
      (graphConnected B) B.genus_graph hDistinct hNeg'
  have hDRank : rank B.graph D = 0 :=
    rank_eq_zero_of_rankDelta_neg_genus_two
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D
      (graphConnected B) B.genus_graph hDistinct hNeg'
  have hDPair : linearEquiv B.graph D
      (oneChip w + oneChip (B.pathVertex alpha i)) := by
    unfold linearEquiv at hw ⊢
    have hEq :
        (oneChip w + oneChip (B.pathVertex alpha i)) - D =
          oneChip w - (D - oneChip (B.pathVertex alpha i)) := by
      abel
    rw [hEq]
    exact hw
  have hPair : rank B.graph
      (oneChip w + oneChip (B.pathVertex alpha i)) = 0 := by
    rw [← rank_eq_of_linear_equiv B.graph hDPair]
    exact hDRank
  have hNoOnStrand (k : B.PathPosition alpha)
      (hwk : w = B.pathVertex alpha k) : False := by
    have hPair' : rank B.graph
        (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k)) = 0 := by
      rw [← hwk]
      simpa [add_comm] using hPair
    have hSub' : rank B.graph
        (oneChip (B.pathVertex alpha i) + oneChip (B.pathVertex alpha k) -
          oneChip (B.pathVertex alpha j)) = 0 := by
      rw [← hwk]
      simpa [add_comm] using hSub
    obtain ⟨hkReflect, hkLower, _hkUpper⟩ :=
      same_strand_pair_sub_zero_forces_interval_general
        B alpha i j k hij hPair' hSub'
    have hkNotJ : k ≠ j := by
      intro hkj
      apply hwv
      rw [hwk, hkj]
    have hkNotJVal : k.val ≠ j.val := by
      intro hval
      exact hkNotJ (Fin.ext hval)
    have hkBound := k.isLt
    dsimp [i, j] at hkReflect hkLower hkNotJVal
    omega
  rcases w with e | ⟨gamma, offset⟩
  · obtain hEnd | hEnd := coreVertex_eq_pathVertex_zero_or_length B alpha e
    · exact hNoOnStrand ⟨0, by omega⟩ hEnd
    · exact hNoOnStrand ⟨B.length alpha, by omega⟩ hEnd
  · have hwDef :
        (Sum.inr ⟨gamma, offset⟩ : B.graph.V) =
          B.interiorVertex gamma offset := rfl
    rw [hwDef] at hPair hSub hwv
    by_cases hgamma : gamma = alpha
    · subst gamma
      let k : B.PathPosition alpha := ⟨offset.val + 1, by
        have hoff := offset.isLt
        have hlenAlpha := B.length_pos alpha
        omega⟩
      have hk : B.IsInteriorPosition alpha k := by
        change 0 < offset.val + 1 ∧ offset.val + 1 < B.length alpha
        have hoff := offset.isLt
        have hlenAlpha := B.length_pos alpha
        omega
      have hwPath : B.interiorVertex alpha offset = B.pathVertex alpha k := by
        rw [B.pathVertex_eq_interiorVertex alpha k hk]
        congr 1
      exact hNoOnStrand k hwPath
    · obtain ⟨q, hq, hqVertex⟩ := exists_interior_strandVertex B gamma offset
      let firstOffset : Fin (B.length alpha - 1) := ⟨0, by omega⟩
      have hiOffset : B.pathVertex alpha i =
          B.interiorVertex alpha firstOffset := by
        rw [B.pathVertex_eq_interiorVertex alpha i hi]
        congr 1
      obtain ⟨p, hp, hpVertex⟩ :=
        exists_interior_strandVertex B alpha firstOffset
      have hSub' : rank B.graph
          (oneChip (strandVertex B gamma q) +
            oneChip (strandVertex B alpha p) -
            oneChip (B.pathVertex alpha j)) = 0 := by
        rw [hqVertex, hpVertex, ← hiOffset]
        exact hSub
      have hSupport := rankSupport_two_interior_distinct_strands
        (by omega : 2 ≤ 2) B gamma alpha q p hq hp hgamma
      have hjMem : B.pathVertex alpha j ∈
          rankSupport B.graph
            (oneChip (strandVertex B gamma q) +
              oneChip (strandVertex B alpha p)) := by
        exact hSub'.ge
      rw [hSupport] at hjMem
      have hjEndpoint : B.pathVertex alpha j =
          B.coreVertex (B.core.head alpha) := by
        dsimp [j]
        exact B.pathVertex_length alpha
      have hjNeQ : B.pathVertex alpha j ≠ strandVertex B gamma q := by
        rw [hqVertex, hjEndpoint]
        simp [SubdivisionGraph.Spec.coreVertex,
          SubdivisionGraph.Spec.interiorVertex]
      have hjNeP : B.pathVertex alpha j ≠ strandVertex B alpha p := by
        rw [hpVertex, hjEndpoint]
        simp [SubdivisionGraph.Spec.coreVertex,
          SubdivisionGraph.Spec.interiorVertex]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hjMem
      exact (hjMem.elim hjNeQ hjNeP).elim

/-- Paper sources: `thm-NonSubmodGenus2` (Theorem 3.4) and
`cor-allSubmodSameStrand` (Corollary 3.6), endpoint pair `(0,n)`.

The two endpoints of a theta graph make every divisor submodular.  When the
auxiliary vertex lies on a strand stored in the same direction as the marked
strand, the exceptional-position interval is empty.  In the opposite stored
direction, the elementary endpoint-path rank calculation gives rank `-1`
directly. -/
theorem theta_allSubmodular_path_endpoints
    (B : Banana 2) (alpha : Fin 3) :
    AllSubmodular
      (mark B.graph
        (B.pathVertex alpha ⟨0, by omega⟩)
        (B.pathVertex alpha ⟨B.length alpha, by omega⟩)) := by
  apply allSubmodular_mark_of_rankDelta_nonneg
  intro D
  by_contra hNot
  have hNeg : rankDelta
      (mark B.graph
        (B.pathVertex alpha ⟨0, by omega⟩)
        (B.pathVertex alpha ⟨B.length alpha, by omega⟩)) D < 0 := by
    omega
  let i : B.PathPosition alpha := ⟨0, by omega⟩
  let j : B.PathPosition alpha := ⟨B.length alpha, by omega⟩
  have hij : i.val < j.val := by
    dsimp [i, j]
    exact B.length_pos alpha
  have huv : B.pathVertex alpha i ≠ B.pathVertex alpha j := by
    intro h
    have hval := congrArg Fin.val (B.pathVertex_injective alpha h)
    exact (ne_of_lt hij) hval
  have hDistinct : ¬ linearEquiv B.graph
      (oneChip (B.pathVertex alpha i) - oneChip (B.pathVertex alpha j)) 0 :=
    marks_not_linearEquiv (by omega) B huv
  have hNeg' : rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D < 0 := by
    simpa [i, j] using hNeg
  obtain ⟨w, hw, _hwReduced, hwv, hSub⟩ :=
    exists_vertex_rep_of_rankDelta_neg_genus_two B.graph
      (B.pathVertex alpha i) (B.pathVertex alpha j) D
      (graphConnected B) B.genus_graph hDistinct hNeg'
  have hDRank : rank B.graph D = 0 :=
    rank_eq_zero_of_rankDelta_neg_genus_two
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D
      (graphConnected B) B.genus_graph hDistinct hNeg'
  have hDPair : linearEquiv B.graph D
      (oneChip w + oneChip (B.pathVertex alpha i)) := by
    unfold linearEquiv at hw ⊢
    have hEq :
        (oneChip w + oneChip (B.pathVertex alpha i)) - D =
          oneChip w - (D - oneChip (B.pathVertex alpha i)) := by
      abel
    rw [hEq]
    exact hw
  have hPair : rank B.graph
      (oneChip w + oneChip (B.pathVertex alpha i)) = 0 := by
    rw [← rank_eq_of_linear_equiv B.graph hDPair]
    exact hDRank
  have hNoForward (gamma : Fin 3) (k : B.PathPosition gamma)
      (hu : B.pathVertex alpha i = B.pathVertex gamma ⟨0, by omega⟩)
      (hv : B.pathVertex alpha j =
        B.pathVertex gamma ⟨B.length gamma, by omega⟩)
      (hwk : w = B.pathVertex gamma k) : False := by
    let iGamma : B.PathPosition gamma := ⟨0, by omega⟩
    let jGamma : B.PathPosition gamma := ⟨B.length gamma, by omega⟩
    have hijGamma : iGamma.val < jGamma.val := by
      dsimp [iGamma, jGamma]
      exact B.length_pos gamma
    have hPair' : rank B.graph
        (oneChip (B.pathVertex gamma iGamma) +
          oneChip (B.pathVertex gamma k)) = 0 := by
      rw [← hwk, ← hu]
      simpa [iGamma, add_comm] using hPair
    have hSub' : rank B.graph
        (oneChip (B.pathVertex gamma iGamma) +
          oneChip (B.pathVertex gamma k) -
          oneChip (B.pathVertex gamma jGamma)) = 0 := by
      rw [← hwk, ← hu, ← hv]
      simpa [iGamma, jGamma, add_comm] using hSub
    obtain ⟨hkReflect, hkLower, _hkUpper⟩ :=
      same_strand_pair_sub_zero_forces_interval_general
        B gamma iGamma jGamma k hijGamma hPair' hSub'
    have hkBound := k.isLt
    dsimp [iGamma, jGamma] at hkReflect hkLower
    omega
  rcases w with e | ⟨gamma, offset⟩
  · obtain hEnd | hEnd := coreVertex_eq_pathVertex_zero_or_length B alpha e
    · exact hNoForward alpha ⟨0, by omega⟩ rfl rfl hEnd
    · exact hNoForward alpha ⟨B.length alpha, by omega⟩ rfl rfl hEnd
  · have hwDef :
        (Sum.inr ⟨gamma, offset⟩ : B.graph.V) =
          B.interiorVertex gamma offset := rfl
    rw [hwDef] at hPair hSub hwv
    let k : B.PathPosition gamma := ⟨offset.val + 1, by
      have hoff := offset.isLt
      have hlenGamma := B.length_pos gamma
      omega⟩
    have hk : B.IsInteriorPosition gamma k := by
      change 0 < offset.val + 1 ∧ offset.val + 1 < B.length gamma
      have hoff := offset.isLt
      have hlenGamma := B.length_pos gamma
      omega
    have hwPath : B.interiorVertex gamma offset = B.pathVertex gamma k := by
      rw [B.pathVertex_eq_interiorVertex gamma k hk]
      congr 1
    by_cases hTail : B.core.tail gamma = B.core.tail alpha
    · have hHead : B.core.head gamma = B.core.head alpha := by
        apply Fin.ext
        have htGamma := (B.core.tail gamma).isLt
        have hhGamma := (B.core.head gamma).isLt
        have htAlpha := (B.core.tail alpha).isLt
        have hhAlpha := (B.core.head alpha).isLt
        have hLoopGamma := B.core_loopless gamma
        have hLoopAlpha := B.core_loopless alpha
        have hTailVal := congrArg Fin.val hTail
        omega
      have hu : B.pathVertex alpha i = B.pathVertex gamma ⟨0, by omega⟩ := by
        calc
          B.pathVertex alpha i = B.coreVertex (B.core.tail alpha) := by
            dsimp [i]
            exact B.pathVertex_zero alpha
          _ = B.coreVertex (B.core.tail gamma) :=
            congrArg B.coreVertex hTail.symm
          _ = B.pathVertex gamma ⟨0, by omega⟩ :=
            (B.pathVertex_zero gamma).symm
      have hv : B.pathVertex alpha j =
          B.pathVertex gamma ⟨B.length gamma, by omega⟩ := by
        calc
          B.pathVertex alpha j = B.coreVertex (B.core.head alpha) := by
            dsimp [j]
            exact B.pathVertex_length alpha
          _ = B.coreVertex (B.core.head gamma) :=
            congrArg B.coreVertex hHead.symm
          _ = B.pathVertex gamma ⟨B.length gamma, by omega⟩ :=
            (B.pathVertex_length gamma).symm
      exact hNoForward gamma k hu hv (hwDef.trans hwPath)
    · have hTailRev : B.core.tail gamma = B.core.head alpha := by
        apply Fin.ext
        have htGamma := (B.core.tail gamma).isLt
        have htAlpha := (B.core.tail alpha).isLt
        have hhAlpha := (B.core.head alpha).isLt
        have hLoopAlpha := B.core_loopless alpha
        have hTailNeVal : (B.core.tail gamma).val ≠ (B.core.tail alpha).val := by
          intro h
          exact hTail (Fin.ext h)
        omega
      have hHeadRev : B.core.head gamma = B.core.tail alpha := by
        apply Fin.ext
        have htGamma := (B.core.tail gamma).isLt
        have hhGamma := (B.core.head gamma).isLt
        have htAlpha := (B.core.tail alpha).isLt
        have hLoopGamma := B.core_loopless gamma
        have hTailRevVal := congrArg Fin.val hTailRev
        omega
      have hu : B.pathVertex alpha i =
          B.pathVertex gamma ⟨B.length gamma, by omega⟩ := by
        calc
          B.pathVertex alpha i = B.coreVertex (B.core.tail alpha) := by
            dsimp [i]
            exact B.pathVertex_zero alpha
          _ = B.coreVertex (B.core.head gamma) :=
            congrArg B.coreVertex hHeadRev.symm
          _ = B.pathVertex gamma ⟨B.length gamma, by omega⟩ :=
            (B.pathVertex_length gamma).symm
      have hv : B.pathVertex alpha j = B.pathVertex gamma ⟨0, by omega⟩ := by
        calc
          B.pathVertex alpha j = B.coreVertex (B.core.head alpha) := by
            dsimp [j]
            exact B.pathVertex_length alpha
          _ = B.coreVertex (B.core.tail gamma) :=
            congrArg B.coreVertex hTailRev.symm
          _ = B.pathVertex gamma ⟨0, by omega⟩ :=
            (B.pathVertex_zero gamma).symm
      have hSub' : rank B.graph
          (oneChip (B.pathVertex gamma k) +
            oneChip (B.pathVertex gamma ⟨B.length gamma, by omega⟩) -
            oneChip (B.pathVertex gamma ⟨0, by omega⟩)) = 0 := by
        rw [← hwPath, ← hu, ← hv]
        exact hSub
      have hNegReverse := rank_same_strand_add_path_length_sub_of_lt
        (by omega : 2 ≤ 2) B gamma k ⟨0, by omega⟩ hk.1
      rw [hNegReverse] at hSub'
      omega

/-! ## Normalized-coordinate boundary theorems -/

/-- Corollary 3.6 boundary `(0,n-1)`, in the paper's normalized strand
coordinates, independent of the subdivision slot's stored orientation. -/
theorem theta_allSubmodular_zero_penultimate
    (B : Banana 2) (alpha : Fin 3) (hlen : 2 ≤ B.length alpha) :
    AllSubmodular
      (mark B.graph
        (strandVertex B alpha ⟨0, by omega⟩)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) := by
  by_cases hTail : B.core.tail alpha = 0
  · have hZero : strandVertex B alpha ⟨0, by omega⟩ =
        B.pathVertex alpha ⟨0, by omega⟩ := by
      unfold strandVertex
      rw [if_pos hTail]
    have hPenultimate :
        strandVertex B alpha ⟨B.length alpha - 1, by omega⟩ =
          B.pathVertex alpha ⟨B.length alpha - 1, by omega⟩ := by
      unfold strandVertex
      rw [if_pos hTail]
    rw [hZero, hPenultimate]
    exact theta_allSubmodular_path_zero_penultimate B alpha hlen
  · have hZero : strandVertex B alpha ⟨0, by omega⟩ =
        B.pathVertex alpha ⟨B.length alpha, by omega⟩ := by
      unfold strandVertex
      rw [if_neg hTail]
      congr 1
    have hPenultimate :
        strandVertex B alpha ⟨B.length alpha - 1, by omega⟩ =
          B.pathVertex alpha ⟨1, by omega⟩ := by
      unfold strandVertex
      rw [if_neg hTail]
      apply congrArg (B.pathVertex alpha)
      apply Fin.ext
      change B.length alpha - (B.length alpha - 1) = 1
      omega
    rw [hZero, hPenultimate]
    exact allSubmodular_mark_swap B.graph
      (B.pathVertex alpha ⟨1, by omega⟩)
      (B.pathVertex alpha ⟨B.length alpha, by omega⟩)
      (theta_allSubmodular_path_one_length B alpha hlen)

/-- Corollary 3.6 boundary `(1,n)`, in normalized strand coordinates. -/
theorem theta_allSubmodular_one_length
    (B : Banana 2) (alpha : Fin 3) (hlen : 2 ≤ B.length alpha) :
    AllSubmodular
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B alpha ⟨B.length alpha, by omega⟩)) := by
  by_cases hTail : B.core.tail alpha = 0
  · have hOne : strandVertex B alpha ⟨1, by omega⟩ =
        B.pathVertex alpha ⟨1, by omega⟩ := by
      unfold strandVertex
      rw [if_pos hTail]
    have hLength : strandVertex B alpha ⟨B.length alpha, by omega⟩ =
        B.pathVertex alpha ⟨B.length alpha, by omega⟩ := by
      unfold strandVertex
      rw [if_pos hTail]
    rw [hOne, hLength]
    exact theta_allSubmodular_path_one_length B alpha hlen
  · have hOne : strandVertex B alpha ⟨1, by omega⟩ =
        B.pathVertex alpha ⟨B.length alpha - 1, by omega⟩ := by
      unfold strandVertex
      rw [if_neg hTail]
    have hLength : strandVertex B alpha ⟨B.length alpha, by omega⟩ =
        B.pathVertex alpha ⟨0, by omega⟩ := by
      unfold strandVertex
      rw [if_neg hTail]
      apply congrArg (B.pathVertex alpha)
      apply Fin.ext
      change B.length alpha - B.length alpha = 0
      omega
    rw [hOne, hLength]
    exact allSubmodular_mark_swap B.graph
      (B.pathVertex alpha ⟨0, by omega⟩)
      (B.pathVertex alpha ⟨B.length alpha - 1, by omega⟩)
      (theta_allSubmodular_path_zero_penultimate B alpha hlen)

/-- The endpoint pair, in normalized coordinates. -/
theorem theta_allSubmodular_zero_length
    (B : Banana 2) (alpha : Fin 3) :
    AllSubmodular
      (mark B.graph
        (strandVertex B alpha ⟨0, by omega⟩)
        (strandVertex B alpha ⟨B.length alpha, by omega⟩)) := by
  by_cases hTail : B.core.tail alpha = 0
  · have hZero : strandVertex B alpha ⟨0, by omega⟩ =
        B.pathVertex alpha ⟨0, by omega⟩ := by
      unfold strandVertex
      rw [if_pos hTail]
    have hLength : strandVertex B alpha ⟨B.length alpha, by omega⟩ =
        B.pathVertex alpha ⟨B.length alpha, by omega⟩ := by
      unfold strandVertex
      rw [if_pos hTail]
    rw [hZero, hLength]
    exact theta_allSubmodular_path_endpoints B alpha
  · have hZero : strandVertex B alpha ⟨0, by omega⟩ =
        B.pathVertex alpha ⟨B.length alpha, by omega⟩ := by
      unfold strandVertex
      rw [if_neg hTail]
      congr 1
    have hLength : strandVertex B alpha ⟨B.length alpha, by omega⟩ =
        B.pathVertex alpha ⟨0, by omega⟩ := by
      unfold strandVertex
      rw [if_neg hTail]
      congr 1
      apply Fin.ext
      simp
    rw [hZero, hLength]
    exact allSubmodular_mark_swap B.graph
      (B.pathVertex alpha ⟨0, by omega⟩)
      (B.pathVertex alpha ⟨B.length alpha, by omega⟩)
      (theta_allSubmodular_path_endpoints B alpha)

/-- Corollary 3.6, endpoint/penultimate boundary in intrinsic endpoint
notation. -/
theorem theta_allSubmodular_leftEndpoint_penultimate
    (B : Banana 2) (alpha : Fin 3) (hlen : 2 ≤ B.length alpha) :
    AllSubmodular
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) := by
  rw [← strandVertex_zero B alpha]
  exact theta_allSubmodular_zero_penultimate B alpha hlen

/-- Corollary 3.6, first-interior/endpoint boundary in intrinsic endpoint
notation. -/
theorem theta_allSubmodular_one_rightEndpoint
    (B : Banana 2) (alpha : Fin 3) (hlen : 2 ≤ B.length alpha) :
    AllSubmodular
      (mark B.graph (strandVertex B alpha ⟨1, by omega⟩)
        (rightEndpoint B)) := by
  rw [← strandVertex_length B alpha]
  exact theta_allSubmodular_one_length B alpha hlen

/-- Corollary 3.6, the two multivalent endpoints. -/
theorem theta_allSubmodular_endpoints (B : Banana 2) :
    AllSubmodular (mark B.graph (leftEndpoint B) (rightEndpoint B)) := by
  let alpha : Fin 3 := 0
  rw [← strandVertex_zero B alpha, ← strandVertex_length B alpha]
  exact theta_allSubmodular_zero_length B alpha

/-! ## The complete same-strand classification -/

/-- Corollary 3.6, same-strand case, with the paper's `i < j`
normalization.  These are exactly the three all-submodular boundary pairs. -/
theorem theta_allSubmodular_same_strand_iff_boundary
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val) :
    AllSubmodular
        (mark B.graph (strandVertex B alpha i) (strandVertex B alpha j)) ↔
      ((i.val = 0 ∧
          (j.val + 1 = B.length alpha ∨ j.val = B.length alpha)) ∨
        (i.val = 1 ∧ j.val = B.length alpha)) := by
  constructor
  · intro hSub
    rcases nsmForBanana_same_strand_classification
        (by omega : 2 ≤ 2) B alpha i j with hExceptional | ⟨D, hD⟩
    · unfold NSMForBananaSameStrandException at hExceptional
      rcases hExceptional with h | h | h | h | h | h
      · exact Or.inl ⟨h.1, Or.inr h.2⟩
      · omega
      · exact Or.inr h
      · omega
      · exact Or.inl ⟨h.1, Or.inl h.2⟩
      · omega
    · have hNonneg :=
        (allSubmodular_iff_rankDelta_nonneg _).mp hSub D
      omega
  · rintro (⟨hiZero, hjNear | hjLength⟩ | ⟨hiOne, hjLength⟩)
    · have hlen : 2 ≤ B.length alpha := by omega
      have hi : i = ⟨0, by omega⟩ := Fin.ext hiZero
      have hj : j = ⟨B.length alpha - 1, by omega⟩ := by
        apply Fin.ext
        change j.val = B.length alpha - 1
        omega
      simpa only [hi, hj] using
        theta_allSubmodular_zero_penultimate B alpha hlen
    · have hi : i = ⟨0, by omega⟩ := Fin.ext hiZero
      have hj : j = ⟨B.length alpha, by omega⟩ := Fin.ext hjLength
      simpa only [hi, hj] using theta_allSubmodular_zero_length B alpha
    · have hlen : 2 ≤ B.length alpha := by omega
      have hi : i = ⟨1, by omega⟩ := Fin.ext hiOne
      have hj : j = ⟨B.length alpha, by omega⟩ := Fin.ext hjLength
      simpa only [hi, hj] using theta_allSubmodular_one_length B alpha hlen

/-- Theorem 3.4, existence equivalence for arbitrary ordered positions on
one theta strand, including all three boundary cases.  This removes the
interiority restriction of the earlier ledger theorem. -/
theorem theta_nonSubmodular_iff_same_strand
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val) :
    (∃ D : CFDiv B.graph,
        rankDelta
          (mark B.graph (strandVertex B alpha i) (strandVertex B alpha j)) D < 0) ↔
      Set.Nonempty (thetaExceptionalPositions B alpha i j) := by
  calc
    (∃ D : CFDiv B.graph,
        rankDelta
          (mark B.graph (strandVertex B alpha i) (strandVertex B alpha j)) D < 0) ↔
        ¬ AllSubmodular
          (mark B.graph (strandVertex B alpha i) (strandVertex B alpha j)) :=
      (not_allSubmodular_iff_exists_rankDelta_neg
        (mark B.graph (strandVertex B alpha i) (strandVertex B alpha j))).symm
    _ ↔ ¬ ((i.val = 0 ∧
          (j.val + 1 = B.length alpha ∨ j.val = B.length alpha)) ∨
        (i.val = 1 ∧ j.val = B.length alpha)) :=
      not_congr (theta_allSubmodular_same_strand_iff_boundary B alpha i j hij)
    _ ↔ Set.Nonempty (thetaExceptionalPositions B alpha i j) :=
      (thetaExceptionalPositions_nonempty_iff_not_boundary B alpha i j hij).symm

/-! ## Full endpoint-safe form of Corollary 3.6 -/

/-- The coordinate alternatives in Corollary 3.6, stated so that endpoint
vertices may be presented on any strand.  The first clause is the genuinely
different-strand case (both coordinates must be interior).  The second says
that the two physical marked vertices are, in either order, one of the three
normalized same-strand boundary pairs. -/
def ThetaAllSubmodularCoordinates
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) : Prop :=
  (alpha ≠ beta ∧ B.IsInteriorPosition alpha i ∧
      B.IsInteriorPosition beta j) ∨
    ∃ (gamma : Fin 3) (p q : B.PathPosition gamma),
      p.val < q.val ∧
      ((p.val = 0 ∧
          (q.val + 1 = B.length gamma ∨ q.val = B.length gamma)) ∨
        (p.val = 1 ∧ q.val = B.length gamma)) ∧
      ((strandVertex B alpha i = strandVertex B gamma p ∧
          strandVertex B beta j = strandVertex B gamma q) ∨
        (strandVertex B alpha i = strandVertex B gamma q ∧
          strandVertex B beta j = strandVertex B gamma p))

/-- An all-submodular marking on a positive-genus banana has distinct marks. -/
theorem marks_ne_of_allSubmodular_banana
    {g : ℕ} (hg : 1 ≤ g) (B : Banana g) (u v : B.graph.V)
    (hSub : AllSubmodular (mark B.graph u v)) : u ≠ v := by
  intro huv
  subst v
  have hNonneg := (allSubmodular_iff_rankDelta_nonneg _).mp hSub (oneChip u)
  have hNeg := rankDelta_one_chip_self_lt_zero hg B u
  omega

/-- Corollary 3.6, complete and endpoint-safe.

For arbitrary normalized coordinate presentations of the two marks, every
divisor is submodular exactly when the marks are distinct interior points on
different strands, or their physical vertices form one of the three
same-strand boundary pairs. -/
theorem theta_allSubmodular_iff_coordinates
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) :
    AllSubmodular
        (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) ↔
      ThetaAllSubmodularCoordinates B alpha beta i j := by
  constructor
  · intro hSub
    have huv : strandVertex B alpha i ≠ strandVertex B beta j :=
      marks_ne_of_allSubmodular_banana (by omega) B _ _ hSub
    by_cases hi : B.IsInteriorPosition alpha i
    · by_cases hj : B.IsInteriorPosition beta j
      · by_cases hab : alpha = beta
        · subst beta
          obtain ⟨D, hD⟩ :=
            exists_rankDelta_neg_same_strand_interior_any_order
              (by omega : 2 ≤ 2) B alpha i j hi hj
          have hNonneg := (allSubmodular_iff_rankDelta_nonneg _).mp hSub D
          omega
        · exact Or.inl ⟨hab, hi, hj⟩
      · change ¬ (0 < j.val ∧ j.val < B.length beta) at hj
        have hjEnd : j.val = 0 ∨ j.val = B.length beta := by
          have hjBound : j.val ≤ B.length beta := Nat.le_of_lt_succ j.isLt
          omega
        rcases hjEnd with hjZero | hjLength
        · have hv : strandVertex B beta j = leftEndpoint B := by
            have hjEq : j = ⟨0, by omega⟩ := Fin.ext hjZero
            rw [hjEq, strandVertex_zero]
          let p : B.PathPosition alpha := ⟨0, by omega⟩
          have hpq : p.val < i.val := by
            dsimp [p]
            exact hi.1
          have hpVertex : strandVertex B alpha p = leftEndpoint B := by
            dsimp [p]
            exact strandVertex_zero B alpha
          have hCommon : AllSubmodular
              (mark B.graph (strandVertex B alpha p) (strandVertex B alpha i)) := by
            have hSwap := allSubmodular_mark_swap B.graph
              (strandVertex B alpha i) (strandVertex B beta j) hSub
            simpa only [hpVertex, hv] using hSwap
          have hBoundary :=
            (theta_allSubmodular_same_strand_iff_boundary
              B alpha p i hpq).mp hCommon
          exact Or.inr ⟨alpha, p, i, hpq, hBoundary,
            Or.inr ⟨rfl, hv.trans hpVertex.symm⟩⟩
        · have hv : strandVertex B beta j = rightEndpoint B := by
            have hjEq : j = ⟨B.length beta, by omega⟩ := Fin.ext hjLength
            rw [hjEq, strandVertex_length]
          let q : B.PathPosition alpha := ⟨B.length alpha, by omega⟩
          have hiq : i.val < q.val := by
            dsimp [q]
            exact hi.2
          have hqVertex : strandVertex B alpha q = rightEndpoint B := by
            dsimp [q]
            exact strandVertex_length B alpha
          have hCommon : AllSubmodular
              (mark B.graph (strandVertex B alpha i) (strandVertex B alpha q)) := by
            simpa only [hqVertex, hv] using hSub
          have hBoundary :=
            (theta_allSubmodular_same_strand_iff_boundary
              B alpha i q hiq).mp hCommon
          exact Or.inr ⟨alpha, i, q, hiq, hBoundary,
            Or.inl ⟨rfl, hv.trans hqVertex.symm⟩⟩
    · by_cases hj : B.IsInteriorPosition beta j
      · change ¬ (0 < i.val ∧ i.val < B.length alpha) at hi
        have hiEnd : i.val = 0 ∨ i.val = B.length alpha := by
          have hiBound : i.val ≤ B.length alpha := Nat.le_of_lt_succ i.isLt
          omega
        rcases hiEnd with hiZero | hiLength
        · have hu : strandVertex B alpha i = leftEndpoint B := by
            have hiEq : i = ⟨0, by omega⟩ := Fin.ext hiZero
            rw [hiEq, strandVertex_zero]
          let p : B.PathPosition beta := ⟨0, by omega⟩
          have hpj : p.val < j.val := by
            dsimp [p]
            exact hj.1
          have hpVertex : strandVertex B beta p = leftEndpoint B := by
            dsimp [p]
            exact strandVertex_zero B beta
          have hCommon : AllSubmodular
              (mark B.graph (strandVertex B beta p) (strandVertex B beta j)) := by
            simpa only [hpVertex, hu] using hSub
          have hBoundary :=
            (theta_allSubmodular_same_strand_iff_boundary
              B beta p j hpj).mp hCommon
          exact Or.inr ⟨beta, p, j, hpj, hBoundary,
            Or.inl ⟨hu.trans hpVertex.symm, rfl⟩⟩
        · have hu : strandVertex B alpha i = rightEndpoint B := by
            have hiEq : i = ⟨B.length alpha, by omega⟩ := Fin.ext hiLength
            rw [hiEq, strandVertex_length]
          let q : B.PathPosition beta := ⟨B.length beta, by omega⟩
          have hjq : j.val < q.val := by
            dsimp [q]
            exact hj.2
          have hqVertex : strandVertex B beta q = rightEndpoint B := by
            dsimp [q]
            exact strandVertex_length B beta
          have hSwap := allSubmodular_mark_swap B.graph
            (strandVertex B alpha i) (strandVertex B beta j) hSub
          have hCommon : AllSubmodular
              (mark B.graph (strandVertex B beta j) (strandVertex B beta q)) := by
            simpa only [hqVertex, hu] using hSwap
          have hBoundary :=
            (theta_allSubmodular_same_strand_iff_boundary
              B beta j q hjq).mp hCommon
          exact Or.inr ⟨beta, j, q, hjq, hBoundary,
            Or.inr ⟨hu.trans hqVertex.symm, rfl⟩⟩
      · change ¬ (0 < i.val ∧ i.val < B.length alpha) at hi
        change ¬ (0 < j.val ∧ j.val < B.length beta) at hj
        have hiEnd : i.val = 0 ∨ i.val = B.length alpha := by
          have hiBound : i.val ≤ B.length alpha := Nat.le_of_lt_succ i.isLt
          omega
        have hjEnd : j.val = 0 ∨ j.val = B.length beta := by
          have hjBound : j.val ≤ B.length beta := Nat.le_of_lt_succ j.isLt
          omega
        rcases hiEnd with hiZero | hiLength <;>
          rcases hjEnd with hjZero | hjLength
        · have hu : strandVertex B alpha i = leftEndpoint B := by
            have hiEq : i = ⟨0, by omega⟩ := Fin.ext hiZero
            rw [hiEq, strandVertex_zero]
          have hv : strandVertex B beta j = leftEndpoint B := by
            have hjEq : j = ⟨0, by omega⟩ := Fin.ext hjZero
            rw [hjEq, strandVertex_zero]
          exact (hu.trans hv.symm |> huv).elim
        · have hu : strandVertex B alpha i = leftEndpoint B := by
            have hiEq : i = ⟨0, by omega⟩ := Fin.ext hiZero
            rw [hiEq, strandVertex_zero]
          have hv : strandVertex B beta j = rightEndpoint B := by
            have hjEq : j = ⟨B.length beta, by omega⟩ := Fin.ext hjLength
            rw [hjEq, strandVertex_length]
          let gamma : Fin 3 := 0
          let p : B.PathPosition gamma := ⟨0, by omega⟩
          let q : B.PathPosition gamma := ⟨B.length gamma, by omega⟩
          have hpq : p.val < q.val := B.length_pos gamma
          have hp : strandVertex B gamma p = leftEndpoint B := by
            dsimp [p]
            exact strandVertex_zero B gamma
          have hq : strandVertex B gamma q = rightEndpoint B := by
            dsimp [q]
            exact strandVertex_length B gamma
          have hBoundary :
              (p.val = 0 ∧
                (q.val + 1 = B.length gamma ∨ q.val = B.length gamma)) ∨
                (p.val = 1 ∧ q.val = B.length gamma) := by
            left
            exact ⟨rfl, Or.inr rfl⟩
          exact Or.inr ⟨gamma, p, q, hpq, hBoundary,
            Or.inl ⟨hu.trans hp.symm, hv.trans hq.symm⟩⟩
        · have hu : strandVertex B alpha i = rightEndpoint B := by
            have hiEq : i = ⟨B.length alpha, by omega⟩ := Fin.ext hiLength
            rw [hiEq, strandVertex_length]
          have hv : strandVertex B beta j = leftEndpoint B := by
            have hjEq : j = ⟨0, by omega⟩ := Fin.ext hjZero
            rw [hjEq, strandVertex_zero]
          let gamma : Fin 3 := 0
          let p : B.PathPosition gamma := ⟨0, by omega⟩
          let q : B.PathPosition gamma := ⟨B.length gamma, by omega⟩
          have hpq : p.val < q.val := B.length_pos gamma
          have hp : strandVertex B gamma p = leftEndpoint B := by
            dsimp [p]
            exact strandVertex_zero B gamma
          have hq : strandVertex B gamma q = rightEndpoint B := by
            dsimp [q]
            exact strandVertex_length B gamma
          have hBoundary :
              (p.val = 0 ∧
                (q.val + 1 = B.length gamma ∨ q.val = B.length gamma)) ∨
                (p.val = 1 ∧ q.val = B.length gamma) := by
            left
            exact ⟨rfl, Or.inr rfl⟩
          exact Or.inr ⟨gamma, p, q, hpq, hBoundary,
            Or.inr ⟨hu.trans hq.symm, hv.trans hp.symm⟩⟩
        · have hu : strandVertex B alpha i = rightEndpoint B := by
            have hiEq : i = ⟨B.length alpha, by omega⟩ := Fin.ext hiLength
            rw [hiEq, strandVertex_length]
          have hv : strandVertex B beta j = rightEndpoint B := by
            have hjEq : j = ⟨B.length beta, by omega⟩ := Fin.ext hjLength
            rw [hjEq, strandVertex_length]
          exact (hu.trans hv.symm |> huv).elim
  · rintro (hDistinct | ⟨gamma, p, q, hpq, hBoundary, hMarks⟩)
    · exact theta_allSubmodular_of_distinct_interior_strands B alpha beta i j
        hDistinct.1 hDistinct.2.1 hDistinct.2.2
    · have hBoundarySub :=
        (theta_allSubmodular_same_strand_iff_boundary
          B gamma p q hpq).mpr hBoundary
      rcases hMarks with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · simpa only [hu, hv] using hBoundarySub
      · have hSwap := allSubmodular_mark_swap B.graph
          (strandVertex B gamma p) (strandVertex B gamma q) hBoundarySub
        simpa only [hu, hv] using hSwap

end Bananas
