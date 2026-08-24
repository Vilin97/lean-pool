/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.MajorantArcNesting
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Coordinated ErLV majorants

This file makes the proposed repair to ErLV's Figure 4 precise.  Majorant
witnesses carry actual strict-cover paths, and the two paths are selected
jointly to minimize the moves made by their facing endpoints.  The finite
minimum exists.  The remaining exchange statement is isolated exactly.
-/

namespace LeanPool.Erdos132ConvexK3

namespace K3CoverSequence

/-- A two-left-move path really contains the two successive strict covers. -/
theorem left_left_of_counts
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 2 0) :
    IsLeftCover P i j ∧ IsLeftCover P (cyclicRetreat i 1) j := by
  cases path with
  | left hCover tail =>
      constructor
      · exact hCover
      · cases tail with
        | left hCover' _ => exact hCover'

/-- A two-right-move path really contains the two successive strict covers. -/
theorem right_right_of_counts
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 0 2) :
    IsRightCover P i j ∧ IsRightCover P i (cyclicAdvance j 1) := by
  cases path with
  | right hCover tail =>
      constructor
      · exact hCover
      · cases tail with
        | right hCover' _ => exact hCover'

end K3CoverSequence

/-- The jointly minimal pair has the same exhaustive inner-count partition
as any pair, but now every branch refers to actual cover paths. -/
theorem coordinated_inner_endpoint_budget_partition
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {z x t u : Fin n}
    (pair : CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u) :
    pair.first.rightMoves + pair.second.leftMoves < 3 ∨
      (pair.first.rightMoves = 1 ∧ pair.second.leftMoves = 2) ∨
      (pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 1) ∨
      (pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 2) :=
  k3_inner_endpoint_budget_partition pair.first pair.second

/-- If a jointly minimal pair is exceptional, minimality rigidifies all
possible substitutes in its Cartesian pool.  This is the exact obstruction
to a purely order-theoretic minimization proof. -/
theorem coordinated_exceptional_count_rigidity
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {z x t u : Fin n}
    (pair : CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u)
    (hExceptional : 3 ≤ pair.first.rightMoves + pair.second.leftMoves) :
    ((pair.first.rightMoves = 1 ∧ pair.second.leftMoves = 2) ∧
        (∀ first' : K3MajorantWitness P d₁ d₂ d₃ z x,
          1 ≤ first'.rightMoves) ∧
        (∀ second' : K3MajorantWitness P d₁ d₂ d₃ t u,
          second'.leftMoves = 2 ∧ second'.rightMoves = 0)) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 1) ∧
        (∀ first' : K3MajorantWitness P d₁ d₂ d₃ z x,
          first'.rightMoves = 2 ∧ first'.leftMoves = 0) ∧
        (∀ second' : K3MajorantWitness P d₁ d₂ d₃ t u,
          1 ≤ second'.leftMoves)) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 2) ∧
        (∀ first' : K3MajorantWitness P d₁ d₂ d₃ z x,
          first'.rightMoves = 2 ∧ first'.leftMoves = 0) ∧
        (∀ second' : K3MajorantWitness P d₁ d₂ d₃ t u,
          second'.leftMoves = 2 ∧ second'.rightMoves = 0)) := by
  rcases coordinated_inner_endpoint_budget_partition pair with
    hGood | h12 | h21 | h22
  · omega
  · left
    refine ⟨h12, ?_, ?_⟩
    · intro first'
      have hMin := pair.minimalInnerMoves first' pair.second
      omega
    · intro second'
      have hMin := pair.minimalInnerMoves pair.first second'
      have hBudget := second'.coverBudget
      omega
  · right; left
    refine ⟨h21, ?_, ?_⟩
    · intro first'
      have hMin := pair.minimalInnerMoves first' pair.second
      have hBudget := first'.coverBudget
      omega
    · intro second'
      have hMin := pair.minimalInnerMoves pair.first second'
      omega
  · right; right
    refine ⟨h22, ?_, ?_⟩
    · intro first'
      have hMin := pair.minimalInnerMoves first' pair.second
      have hBudget := first'.coverBudget
      omega
    · intro second'
      have hMin := pair.minimalInnerMoves pair.first second'
      have hBudget := second'.coverBudget
      omega

/-- The selected exceptional cases contain the forced two-move paths that a
geometric exchange proof would have to replace. -/
theorem coordinated_exceptional_forced_paths
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {z x t u : Fin n}
    (pair : CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u)
    (hExceptional : 3 ≤ pair.first.rightMoves + pair.second.leftMoves) :
    ((pair.first.rightMoves = 1 ∧ pair.second.leftMoves = 2) ∧
        IsLeftCover P t u ∧
        IsLeftCover P (cyclicRetreat t 1) u) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 1) ∧
        IsRightCover P z x ∧
        IsRightCover P z (cyclicAdvance x 1)) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 2) ∧
        IsRightCover P z x ∧
        IsRightCover P z (cyclicAdvance x 1) ∧
        IsLeftCover P t u ∧
        IsLeftCover P (cyclicRetreat t 1) u) := by
  rcases coordinated_inner_endpoint_budget_partition pair with
    hGood | h12 | h21 | h22
  · omega
  · left
    have hBeta : pair.second.rightMoves = 0 := by
      have := pair.second.coverBudget
      omega
    have hPath := K3CoverSequence.left_left_of_counts (P := P) (i := t) (j := u)
      (h12.2 ▸ hBeta ▸ pair.second.path)
    exact ⟨h12, hPath⟩
  · right; left
    have hB : pair.first.leftMoves = 0 := by
      have := pair.first.coverBudget
      omega
    have hPath := K3CoverSequence.right_right_of_counts (P := P) (i := z) (j := x)
      (hB ▸ h21.1 ▸ pair.first.path)
    exact ⟨h21, hPath⟩
  · right; right
    have hB : pair.first.leftMoves = 0 := by
      have := pair.first.coverBudget
      omega
    have hBeta : pair.second.rightMoves = 0 := by
      have := pair.second.coverBudget
      omega
    have hFirstPath := K3CoverSequence.right_right_of_counts
      (P := P) (i := z) (j := x) (hB ▸ h22.1 ▸ pair.first.path)
    have hSecondPath := K3CoverSequence.left_left_of_counts
      (P := P) (i := t) (j := u) (h22.2 ▸ hBeta ▸ pair.second.path)
    exact ⟨h22, hFirstPath.1, hFirstPath.2,
      hSecondPath.1, hSecondPath.2⟩

/-- The three exceptional pairs have exactly the endpoint geometry hidden by
ErLV Figure 4: the inner endpoints coincide in `(1,2)` and `(2,1)`, while
they occur in the reverse order in `(2,2)`.  Thus terminal-majorant
nonavoidance is automatic in these branches and supplies no nesting. -/
theorem coordinated_exceptional_inner_endpoints
    {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {z x u : Fin n}
    (pair : CoordinatedK3MajorantPair P d₁ d₂ d₃
      z x (cyclicAdvance x 3) u)
    (hExceptional : 3 ≤ pair.first.rightMoves + pair.second.leftMoves) :
    ((pair.first.rightMoves = 1 ∧ pair.second.leftMoves = 2) ∧
        cyclicAdvance x pair.first.rightMoves =
          cyclicRetreat (cyclicAdvance x 3) pair.second.leftMoves ∧
        cyclicAdvance x pair.first.rightMoves = cyclicAdvance x 1) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 1) ∧
        cyclicAdvance x pair.first.rightMoves =
          cyclicRetreat (cyclicAdvance x 3) pair.second.leftMoves ∧
        cyclicAdvance x pair.first.rightMoves = cyclicAdvance x 2) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 2) ∧
        cyclicAdvance x pair.first.rightMoves = cyclicAdvance x 2 ∧
        cyclicRetreat (cyclicAdvance x 3) pair.second.leftMoves =
          cyclicAdvance x 1) := by
  have h3n : 3 < n := by omega
  rcases coordinated_inner_endpoint_budget_partition pair with
    hGood | h12 | h21 | h22
  · omega
  · left
    refine ⟨h12, ?_, ?_⟩
    · rw [h12.1, h12.2]
      simpa using
        (cyclicRetreat_advance x (k := 3) (m := 2) (by omega) h3n).symm
    · rw [h12.1]
  · right; left
    refine ⟨h21, ?_, ?_⟩
    · rw [h21.1, h21.2]
      simpa using
        (cyclicRetreat_advance x (k := 3) (m := 1) (by omega) h3n).symm
    · rw [h21.1]
  · right; right
    refine ⟨h22, ?_, ?_⟩
    · rw [h22.1]
    · rw [h22.2]
      simpa using cyclicRetreat_advance x (k := 3) (m := 2) (by omega) h3n

/-- Two successive right covers exhaust the three ranks exactly. -/
theorem right_right_cover_rank_ladder
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (path : K3CoverSequence P i j 0 2) :
    sqDist (P i) (P j) = d₃ ∧
      sqDist (P i) (P (cyclicAdvance j 1)) = d₂ ∧
      sqDist (P i) (P (cyclicAdvance j 2)) = d₁ := by
  have hCovers := K3CoverSequence.right_right_of_counts path
  have hMid := right_cover_top_three_adjacent hClasses hStart hCovers.1
  have hEnd' := right_cover_top_three_adjacent hClasses hMid hCovers.2
  have hEnd : TopThreeAdjacent P d₁ d₂ d₃ i (cyclicAdvance j 2) := by
    simpa [cyclicAdvance_add] using hEnd'
  have hGrow₁ : sqDist (P i) (P j) <
      sqDist (P i) (P (cyclicAdvance j 1)) := hCovers.1
  have hGrow₂ : sqDist (P i) (P (cyclicAdvance j 1)) <
      sqDist (P i) (P (cyclicAdvance j 2)) := by
    simpa only [IsRightCover, cyclicAdvance_add, Nat.reduceAdd] using hCovers.2
  have hFinal : sqDist (P i) (P (cyclicAdvance j 2)) = d₁ := by
    exact two_covers_end_at_d₁ hClasses hStart hMid hEnd hGrow₁ hGrow₂
  have hd₃d₂ := hClasses.1
  have hd₂d₁ := hClasses.2.1
  have hStartRank : sqDist (P i) (P j) = d₃ := by
    rcases hStart.2 with h₁ | h₂ | h₃ <;>
      rcases hMid.2 with hm₁ | hm₂ | hm₃ <;> linarith
  have hMidRank : sqDist (P i) (P (cyclicAdvance j 1)) = d₂ := by
    rcases hMid.2 with hm₁ | hm₂ | hm₃ <;> linarith
  exact ⟨hStartRank, hMidRank, hFinal⟩

/-- Two successive left covers exhaust the three ranks exactly. -/
theorem left_left_cover_rank_ladder
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (path : K3CoverSequence P i j 2 0) :
    sqDist (P i) (P j) = d₃ ∧
      sqDist (P (cyclicRetreat i 1)) (P j) = d₂ ∧
      sqDist (P (cyclicRetreat i 2)) (P j) = d₁ := by
  have hCovers := K3CoverSequence.left_left_of_counts path
  have hMid := left_cover_top_three_adjacent hClasses hStart hCovers.1
  have hEnd' := left_cover_top_three_adjacent hClasses hMid hCovers.2
  have hEnd : TopThreeAdjacent P d₁ d₂ d₃ (cyclicRetreat i 2) j := by
    simpa [cyclicRetreat_add] using hEnd'
  have hGrow₁ : sqDist (P i) (P j) <
      sqDist (P (cyclicRetreat i 1)) (P j) := hCovers.1
  have hGrow₂ : sqDist (P (cyclicRetreat i 1)) (P j) <
      sqDist (P (cyclicRetreat i 2)) (P j) := by
    simpa only [IsLeftCover, cyclicRetreat_add, Nat.reduceAdd] using hCovers.2
  have hFinal : sqDist (P (cyclicRetreat i 2)) (P j) = d₁ := by
    exact two_covers_end_at_d₁ hClasses hStart hMid hEnd hGrow₁ hGrow₂
  have hd₃d₂ := hClasses.1
  have hd₂d₁ := hClasses.2.1
  have hStartRank : sqDist (P i) (P j) = d₃ := by
    rcases hStart.2 with h₁ | h₂ | h₃ <;>
      rcases hMid.2 with hm₁ | hm₂ | hm₃ <;> linarith
  have hMidRank : sqDist (P (cyclicRetreat i 1)) (P j) = d₂ := by
    rcases hMid.2 with hm₁ | hm₂ | hm₃ <;> linarith
  exact ⟨hStartRank, hMidRank, hFinal⟩

/-- The intermediate edge of a forced two-right-move chain is not a
majorant: the second move is still a strict right cover.  Thus this edge
cannot be the cheaper terminal substitute suggested by an informal exchange
argument. -/
theorem right_right_intermediate_not_majorant
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 0 2) :
    ¬IsMajorant P i (cyclicAdvance j 1) := by
  intro hMajorant
  exact hMajorant.2 (K3CoverSequence.right_right_of_counts path).2

/-- The intermediate edge of a forced two-left-move chain is not a
majorant: the second move is still a strict left cover. -/
theorem left_left_intermediate_not_majorant
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 2 0) :
    ¬IsMajorant P (cyclicRetreat i 1) j := by
  intro hMajorant
  exact hMajorant.1 (K3CoverSequence.left_left_of_counts path).2

/-- Retreats by two distinct offsets below the polygon size have distinct
endpoints. -/
theorem cyclicRetreat_ne_of_lt
    {n : ℕ} [NeZero n] (i : Fin n) {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cyclicRetreat i a ≠ cyclicRetreat i b := by
  intro heq
  unfold cyclicRetreat at heq
  have hoff : Fin.ofNat n a = Fin.ofNat n b := sub_right_inj.mp heq
  have hval := congrArg Fin.val hoff
  have : a = b := by
    simpa [Fin.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hval
  exact hab this

/-- A `k=3` majorant witness has at most two moves in total, so its inner
endpoint cannot be the vertex three sides away.  Consequently the two cross
edges forced by strict ED in case `(2,2)` are not terminal edges of either
original cover process. -/
theorem three_side_cross_edges_outside_majorant_budget
    {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {z x u : Fin n}
    (first : K3MajorantWitness P d₁ d₂ d₃ z x)
    (second : K3MajorantWitness P d₁ d₂ d₃ (cyclicAdvance x 3) u) :
    cyclicAdvance x first.rightMoves ≠ cyclicAdvance x 3 ∧
      cyclicRetreat (cyclicAdvance x 3) second.leftMoves ≠ x := by
  have hFirstLe : first.rightMoves ≤ 2 := by
    have := first.coverBudget
    omega
  have hSecondLe : second.leftMoves ≤ 2 := by
    have := second.coverBudget
    omega
  constructor
  · exact cyclicAdvance_ne_of_lt x (by omega) (by omega) (by omega)
  · have hne := cyclicRetreat_ne_of_lt (cyclicAdvance x 3)
      (a := second.leftMoves) (b := 3) (by omega) (by omega) (by omega)
    have hretreat : cyclicRetreat (cyclicAdvance x 3) 3 = x := by
      simpa using cyclicRetreat_advance x (k := 3) (m := 3) (by omega) (by omega)
    simpa [hretreat] using hne

/-- Exact kernel boundary in the three exceptional coordinated cases.  Each
forced two-move chain has the only possible rank ladder `d₃ → d₂ → d₁`,
while its named intermediate exchange edge is still covered and therefore
is not a majorant.  In `(2,2)` both failures occur simultaneously.

This theorem does not claim that a full minimum-degree-seven configuration
realizing one of the cases exists.  It records exactly why the local swap
proposed after the rigidification does not produce the cheaper pair required
by `ErLVCoordinatedMajorantExchangeComplete`. -/
theorem coordinated_exceptional_rank_and_exchange_obstruction
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {z x t u : Fin n}
    (hFirstStart : TopThreeAdjacent P d₁ d₂ d₃ z x)
    (hSecondStart : TopThreeAdjacent P d₁ d₂ d₃ t u)
    (pair : CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u)
    (hExceptional : 3 ≤ pair.first.rightMoves + pair.second.leftMoves) :
    ((pair.first.rightMoves = 1 ∧ pair.second.leftMoves = 2) ∧
        sqDist (P t) (P u) = d₃ ∧
        sqDist (P (cyclicRetreat t 1)) (P u) = d₂ ∧
        sqDist (P (cyclicRetreat t 2)) (P u) = d₁ ∧
        ¬IsMajorant P (cyclicRetreat t 1) u) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 1) ∧
        sqDist (P z) (P x) = d₃ ∧
        sqDist (P z) (P (cyclicAdvance x 1)) = d₂ ∧
        sqDist (P z) (P (cyclicAdvance x 2)) = d₁ ∧
        ¬IsMajorant P z (cyclicAdvance x 1)) ∨
      ((pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 2) ∧
        sqDist (P z) (P x) = d₃ ∧
        sqDist (P z) (P (cyclicAdvance x 1)) = d₂ ∧
        sqDist (P z) (P (cyclicAdvance x 2)) = d₁ ∧
        sqDist (P t) (P u) = d₃ ∧
        sqDist (P (cyclicRetreat t 1)) (P u) = d₂ ∧
        sqDist (P (cyclicRetreat t 2)) (P u) = d₁ ∧
        ¬IsMajorant P z (cyclicAdvance x 1) ∧
        ¬IsMajorant P (cyclicRetreat t 1) u) := by
  rcases coordinated_inner_endpoint_budget_partition pair with
    hGood | h12 | h21 | h22
  · omega
  · left
    have hBeta : pair.second.rightMoves = 0 := by
      have := pair.second.coverBudget
      omega
    have hPath : K3CoverSequence P t u 2 0 :=
      h12.2 ▸ hBeta ▸ pair.second.path
    have hRanks := left_left_cover_rank_ladder hClasses hSecondStart hPath
    exact ⟨h12, hRanks.1, hRanks.2.1, hRanks.2.2,
      left_left_intermediate_not_majorant hPath⟩
  · right; left
    have hB : pair.first.leftMoves = 0 := by
      have := pair.first.coverBudget
      omega
    have hPath : K3CoverSequence P z x 0 2 :=
      hB ▸ h21.1 ▸ pair.first.path
    have hRanks := right_right_cover_rank_ladder hClasses hFirstStart hPath
    exact ⟨h21, hRanks.1, hRanks.2.1, hRanks.2.2,
      right_right_intermediate_not_majorant hPath⟩
  · right; right
    have hB : pair.first.leftMoves = 0 := by
      have := pair.first.coverBudget
      omega
    have hBeta : pair.second.rightMoves = 0 := by
      have := pair.second.coverBudget
      omega
    have hFirstPath : K3CoverSequence P z x 0 2 :=
      hB ▸ h22.1 ▸ pair.first.path
    have hSecondPath : K3CoverSequence P t u 2 0 :=
      h22.2 ▸ hBeta ▸ pair.second.path
    have hFirstRanks :=
      right_right_cover_rank_ladder hClasses hFirstStart hFirstPath
    have hSecondRanks :=
      left_left_cover_rank_ladder hClasses hSecondStart hSecondPath
    exact ⟨h22, hFirstRanks.1, hFirstRanks.2.1, hFirstRanks.2.2,
      hSecondRanks.1, hSecondRanks.2.1, hSecondRanks.2.2,
      right_right_intermediate_not_majorant hFirstPath,
      left_left_intermediate_not_majorant hSecondPath⟩

/-- Strict ED does produce a cross top-three edge from two equal avoiding
sides.  It does not say that this diagonal is an immediate endpoint cover,
which is precisely why it does not by itself furnish the required exchange
path. -/
theorem equal_avoiding_edges_force_cross_top_three
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {a b c d : Fin n}
    (hquad : StrictConvexQuad (P a) (P b) (P c) (P d))
    (hab : TopThreeAdjacent P d₁ d₂ d₃ a b)
    (hcd : TopThreeAdjacent P d₁ d₂ d₃ c d)
    (hEqual : sqDist (P a) (P b) = sqDist (P c) (P d)) :
    TopThreeAdjacent P d₁ d₂ d₃ a c ∨
      TopThreeAdjacent P d₁ d₂ d₃ b d := by
  have hEdge := edge_diagonal_inequality hquad
  have habSq := euclideanDist_sq (P a) (P b)
  have hcdSq := euclideanDist_sq (P c) (P d)
  have hacSq := euclideanDist_sq (P a) (P c)
  have hbdSq := euclideanDist_sq (P b) (P d)
  have habNonneg : 0 ≤ euclideanDist (P a) (P b) := dist_nonneg
  have hcdNonneg : 0 ≤ euclideanDist (P c) (P d) := dist_nonneg
  have hacNonneg : 0 ≤ euclideanDist (P a) (P c) := dist_nonneg
  have hbdNonneg : 0 ≤ euclideanDist (P b) (P d) := dist_nonneg
  have hSideEq : euclideanDist (P a) (P b) = euclideanDist (P c) (P d) := by
    nlinarith
  by_cases hacLong : euclideanDist (P a) (P b) < euclideanDist (P a) (P c)
  · left
    apply top_three_adjacent_of_strictly_longer hClasses hab
    nlinarith
  · right
    have hbdLong : euclideanDist (P c) (P d) < euclideanDist (P b) (P d) := by
      have hacLe := le_of_not_gt hacLong
      linarith
    apply top_three_adjacent_of_strictly_longer hClasses hcd
    nlinarith

/-- In the maximal-gap setup the two starting edges `tu` and `zx` occur as
opposite sides of the strict convex quadrilateral `t,u,z,x`.  This is the
exact cyclic order needed to instantiate strict ED in the rigid `(2,2)`
branch. -/
theorem erlv_start_edges_strict_convex_quad
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v)
    (x : Fin n)
    (hMax : ∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
      firstNeighborGap P d₁ d₂ d₃ x) :
    StrictConvexQuad
      (P (cyclicAdvance x 3))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance x 3)))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ x))
      (P x) := by
  let gx := firstNeighborGap P d₁ d₂ d₃ x
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ x).val
  let t := cyclicAdvance x 3
  let gt := firstNeighborGap P d₁ d₂ d₃ t
  let uoff := 3 + gt
  let zoff := n - hx
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (hHigh x)
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ x := by
    have := hHigh x
    omega
  have htdeg : 0 < vertexDegree P d₁ d₂ d₃ t := by
    have := hHigh t
    omega
  have hgtpos : 0 < gt := firstNeighborGap_pos_of_degree_pos htdeg
  have hhxpos : 0 < hx :=
    firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hxbudget := first_neighbor_gap_cw_budget (v := x) (hHigh x)
  have hgtgx : gt ≤ gx := hMax t
  have huoff : 3 < uoff := by
    dsimp [uoff]
    omega
  have huz : uoff < zoff := by
    dsimp [gx, hx, gt, uoff, zoff] at hxbudget hgtgx ⊢
    omega
  have hzoffn : zoff < n := by
    dsimp [zoff]
    omega
  have htIndex : cyclicAdvance x 3 = t := rfl
  have huIndex :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ t =
        cyclicAdvance x uoff := by
    unfold firstCounterclockwiseNeighbor
    rw [cyclicAdvance_add]
  have hzIndex :
      firstClockwiseNeighbor P d₁ d₂ d₃ x = cyclicAdvance x zoff := by
    change cyclicRetreat x hx = cyclicAdvance x zoff
    exact cyclicRetreat_eq_advance_complement x hhxpos (by omega)
  have hxIndex : cyclicAdvance x n = x := by
    simpa using cyclicAdvance_period x 0
  have htPeriod : cyclicAdvance x (n + 3) = cyclicAdvance x 3 := by
    simpa [Nat.add_comm] using cyclicAdvance_period x 3
  rw [htIndex]
  change StrictConvexQuad
    (P t)
    (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃ t))
    (P (firstClockwiseNeighbor P d₁ d₂ d₃ x))
    (P x)
  rw [huIndex, hzIndex]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cyclic_strict_convex_turn_unwrapped hConvex x
      (a := 3) (b := uoff) (c := zoff) huoff huz (by omega)
  · have h := cyclic_strict_convex_turn_unwrapped hConvex x
      (a := 3) (b := uoff) (c := n) huoff (by omega) (by omega)
    simpa [hxIndex] using h
  · have h := cyclic_strict_convex_turn_unwrapped hConvex x
      (a := uoff) (b := zoff) (c := n) huz hzoffn (by omega)
    simpa [hxIndex] using h
  · have h := cyclic_strict_convex_turn_unwrapped hConvex x
      (a := zoff) (b := n) (c := n + 3) hzoffn (by omega) (by omega)
    simpa [hxIndex, htPeriod] using h

/-- In the rigid `(2,2)` case, strict ED is fully exhausted: the two equal
`d₃` starting sides force one of the nonlocal cross edges `zt` or `xu` into
the top-three graph.  These cross edges move an inner endpoint by three
polygon sides; the theorem deliberately does not misidentify either one as
an immediate cover in a two-move majorant path. -/
theorem coordinated_exceptional_22_forces_cross_top_three
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v)
    (x : Fin n)
    (hMax : ∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
      firstNeighborGap P d₁ d₂ d₃ x)
    (pair : CoordinatedK3MajorantPair P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ x) x
      (cyclicAdvance x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance x 3)))
    (h22 : pair.first.rightMoves = 2 ∧ pair.second.leftMoves = 2) :
    TopThreeAdjacent P d₁ d₂ d₃
        (firstClockwiseNeighbor P d₁ d₂ d₃ x) (cyclicAdvance x 3) ∨
      TopThreeAdjacent P d₁ d₂ d₃ x
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance x 3)) := by
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let t := cyclicAdvance x 3
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
  have hFirstStart : TopThreeAdjacent P d₁ d₂ d₃ z x := by
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := hHigh x
    omega
  have hSecondStart : TopThreeAdjacent P d₁ d₂ d₃ t u := by
    apply firstCounterclockwiseNeighbor_adjacent_of_degree_pos
    have := hHigh t
    omega
  have hB : pair.first.leftMoves = 0 := by
    have := pair.first.coverBudget
    omega
  have hBeta : pair.second.rightMoves = 0 := by
    have := pair.second.coverBudget
    omega
  have hFirstPath : K3CoverSequence P z x 0 2 :=
    hB ▸ h22.1 ▸ pair.first.path
  have hSecondPath : K3CoverSequence P t u 2 0 :=
    h22.2 ▸ hBeta ▸ pair.second.path
  have hFirstRanks :=
    right_right_cover_rank_ladder hClasses hFirstStart hFirstPath
  have hSecondRanks :=
    left_left_cover_rank_ladder hClasses hSecondStart hSecondPath
  have hEqual : sqDist (P t) (P u) = sqDist (P z) (P x) := by
    calc
      sqDist (P t) (P u) = d₃ := hSecondRanks.1
      _ = sqDist (P z) (P x) := hFirstRanks.1.symm
  have hquad : StrictConvexQuad (P t) (P u) (P z) (P x) := by
    exact erlv_start_edges_strict_convex_quad hConvex hHigh x hMax
  rcases equal_avoiding_edges_force_cross_top_three hClasses hquad
      hSecondStart hFirstStart hEqual with htz | hux
  · exact Or.inl (topThreeAdjacent_symm htz)
  · exact Or.inr (topThreeAdjacent_symm hux)

/-- Exact exchange claim missing from the printed proof: every exceptional
joint minimum admits another actual pair with fewer facing-endpoint moves.
Neither ErLV89 p.548 nor the 1986 preprint states a selection rule or proves
this replacement. -/
def ErLVCoordinatedMajorantExchangeComplete : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    CyclicStrictConvex P → HasTopThreeDistanceClasses P d₁ d₂ d₃ →
    (∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v) →
    ∀ x : Fin n,
      (∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
        firstNeighborGap P d₁ d₂ d₃ x) →
      let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
      let t := cyclicAdvance x 3
      let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
      ∀ pair : CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u,
        3 ≤ pair.first.rightMoves + pair.second.leftMoves →
        ∃ first' : K3MajorantWitness P d₁ d₂ d₃ z x,
          ∃ second' : K3MajorantWitness P d₁ d₂ d₃ t u,
            first'.rightMoves + second'.leftMoves <
              pair.first.rightMoves + pair.second.leftMoves

/-- A proof of the missing exchange would discharge the coordinated strict
inner order and hence the already-kernelized arc-nesting geometry. -/
theorem erlv_inner_endpoint_separation_complete_of_coordinated_exchange
    (hExchange : ErLVCoordinatedMajorantExchangeComplete) :
    ErLVInnerEndpointSeparationComplete := by
  intro n _ P d₁ d₂ d₃ hConvex hClasses hHigh x hMax
  dsimp only
  have hFirst : Nonempty (K3MajorantWitness P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ x) x) := by
    apply exists_k3_majorant hClasses
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := hHigh x
    omega
  have hSecond : Nonempty (K3MajorantWitness P d₁ d₂ d₃
      (cyclicAdvance x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance x 3))) := by
    apply exists_k3_majorant hClasses
    apply firstCounterclockwiseNeighbor_adjacent_of_degree_pos
    have := hHigh (cyclicAdvance x 3)
    omega
  obtain ⟨pair⟩ := exists_coordinated_k3_majorant_pair hFirst hSecond
  refine ⟨pair, ?_⟩
  by_contra hNot
  have hExceptional : 3 ≤ pair.first.rightMoves + pair.second.leftMoves := by
    omega
  obtain ⟨first', second', hLower⟩ :=
    hExchange P d₁ d₂ d₃ hConvex hClasses hHigh x hMax pair hExceptional
  have hMinimal := pair.minimalInnerMoves first' second'
  omega

end LeanPool.Erdos132ConvexK3
