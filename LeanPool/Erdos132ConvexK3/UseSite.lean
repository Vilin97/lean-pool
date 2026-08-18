/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.CoordinatedMajorants
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# The ErLV reduction at its actual use site

The global proof uses the majorant diagram only inside the contradiction
branch in which every vertex has degree at least seven.  It does not need an
abstract exchange producing a cheaper majorant pair.  This file therefore
keeps `ErLVCoordinatedMajorantExchangeComplete` as the documented stronger
open statement and names the weaker obligation actually needed: an
exceptional jointly minimal pair at the selected maximal-gap vertex is
impossible.

The use-site package keeps only the data consumed by the branch proofs.
-/

namespace LeanPool.Erdos132ConvexK3

/-- All data present where the ErLV diagram is actually invoked: a convex
top-three configuration in the high-minimum-degree contradiction branch, a
maximal-gap vertex `x`, and the jointly minimal pair selected around `x` and
`x+3`. -/
structure ErLVAtVertexUseSite
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  convex : CyclicStrictConvex P
  classes : HasTopThreeDistanceClasses P d₁ d₂ d₃
  highDegree : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v
  /-- Selected vertex with maximal first-neighbor gap. -/
  x : Fin n
  maximalGap : ∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
    firstNeighborGap P d₁ d₂ d₃ x
  /-- Jointly minimal pair of facing majorant paths. -/
  pair : CoordinatedK3MajorantPair P d₁ d₂ d₃
    (firstClockwiseNeighbor P d₁ d₂ d₃ x) x
    (cyclicAdvance x 3)
    (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3))

/-- Package an actual contradiction-branch use site. -/
noncomputable def erlvAtVertexUseSiteOfHighDegree
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v)
    (x : Fin n)
    (hMax : ∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
      firstNeighborGap P d₁ d₂ d₃ x)
    (pair : CoordinatedK3MajorantPair P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ x) x
      (cyclicAdvance x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3))) :
    ErLVAtVertexUseSite P d₁ d₂ d₃ := by
  exact {
    convex := hConvex
    classes := hClasses
    highDegree := hHigh
    x := x
    maximalGap := hMax
    pair := pair }

namespace ErLVAtVertexUseSite

/-- The exceptional branch with inner endpoint move counts `(1,2)`. -/
def Case12
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : Prop :=
  S.pair.first.rightMoves = 1 ∧ S.pair.second.leftMoves = 2

/-- The exceptional branch with inner endpoint move counts `(2,1)`. -/
def Case21
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : Prop :=
  S.pair.first.rightMoves = 2 ∧ S.pair.second.leftMoves = 1

/-- The exceptional branch with inner endpoint move counts `(2,2)`. -/
def Case22
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : Prop :=
  S.pair.first.rightMoves = 2 ∧ S.pair.second.leftMoves = 2

end ErLVAtVertexUseSite

/-- The exact weakened lemma needed at the reduction use site.  A direct
geometric contradiction is enough; no cheaper pair need be constructed. -/
def ErLVAtVertexExceptionalBranchesImpossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃,
      3 ≤ S.pair.first.rightMoves + S.pair.second.leftMoves → False

/-- The `(1,2)` exceptional branch is impossible at the use site. -/
def ErLVAtVertexCase12Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case12 → False

/-- The `(2,1)` exceptional branch is impossible at the use site. -/
def ErLVAtVertexCase21Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case21 → False

/-- The `(2,2)` exceptional branch is impossible at the use site. -/
def ErLVAtVertexCase22Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case22 → False

/-- The at-use-site obligation is exactly the conjunction of the three rigid
branches and nothing stronger. -/
theorem erlv_at_vertex_exceptional_branches_impossible_iff_cases :
    ErLVAtVertexExceptionalBranchesImpossible ↔
      ErLVAtVertexCase12Impossible ∧ ErLVAtVertexCase21Impossible ∧
        ErLVAtVertexCase22Impossible := by
  constructor
  · intro hAll
    refine ⟨?_, ?_, ?_⟩
    · intro n _ P d₁ d₂ d₃ S h12
      apply hAll P d₁ d₂ d₃ S
      dsimp only [ErLVAtVertexUseSite.Case12] at h12
      omega
    · intro n _ P d₁ d₂ d₃ S h21
      apply hAll P d₁ d₂ d₃ S
      dsimp only [ErLVAtVertexUseSite.Case21] at h21
      omega
    · intro n _ P d₁ d₂ d₃ S h22
      apply hAll P d₁ d₂ d₃ S
      dsimp only [ErLVAtVertexUseSite.Case22] at h22
      omega
  · rintro ⟨h12Close, h21Close, h22Close⟩
    intro n _ P d₁ d₂ d₃ S hExceptional
    rcases coordinated_inner_endpoint_budget_partition S.pair with
      hGood | h12 | h21 | h22
    · omega
    · exact h12Close P d₁ d₂ d₃ S h12
    · exact h21Close P d₁ d₂ d₃ S h21
    · exact h22Close P d₁ d₂ d₃ S h22

/-- The old exchange statement implies the narrowed use-site statement, so
the pivot weakens the missing obligation rather than changing the theorem. -/
theorem erlv_at_vertex_exceptional_branches_impossible_of_exchange
    (hExchange : ErLVCoordinatedMajorantExchangeComplete) :
    ErLVAtVertexExceptionalBranchesImpossible := by
  intro n _ P d₁ d₂ d₃ S hExceptional
  obtain ⟨first', second', hLower⟩ :=
    hExchange P d₁ d₂ d₃ S.convex S.classes S.highDegree S.x S.maximalGap
      S.pair hExceptional
  have hMinimal := S.pair.minimalInnerMoves first' second'
  omega

/-- Killing the three branches directly at the use site supplies the strict
inner-endpoint order required by the already-proved nesting geometry. -/
theorem erlv_inner_endpoint_separation_complete_of_at_vertex_closure
    (hClose : ErLVAtVertexExceptionalBranchesImpossible) :
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
  let S := erlvAtVertexUseSiteOfHighDegree
    hConvex hClasses hHigh x hMax pair
  refine ⟨pair, ?_⟩
  by_contra hNot
  have hExceptional : 3 ≤ pair.first.rightMoves + pair.second.leftMoves := by
    omega
  apply hClose P d₁ d₂ d₃ S
  simpa [S, erlvAtVertexUseSiteOfHighDegree] using hExceptional

/-- Use-site branch closure therefore reaches the existing source-facing
arc-nesting interface. -/
theorem erlv_majorant_arc_nesting_complete_of_at_vertex_closure
    (hClose : ErLVAtVertexExceptionalBranchesImpossible) :
    ErLVMajorantArcNestingComplete :=
  erlv_majorant_arc_nesting_complete_of_inner_endpoint_separation
    (erlv_inner_endpoint_separation_complete_of_at_vertex_closure hClose)

namespace K3CoverSequence

/-- Every cover sequence weakly increases squared distance from its starting
edge to its terminal edge. -/
theorem sqDist_le_terminal
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    {leftMoves rightMoves : ℕ}
    (path : K3CoverSequence P i j leftMoves rightMoves) :
    sqDist (P i) (P j) ≤
      sqDist (P (cyclicRetreat i leftMoves))
        (P (cyclicAdvance j rightMoves)) := by
  induction path with
  | nil => simp
  | @left i j leftMoves rightMoves hCover tail ih =>
      have h := le_trans (le_of_lt hCover) ih
      simpa only [cyclicRetreat_add, Nat.add_comm] using h
  | @right i j leftMoves rightMoves hCover tail ih =>
      have h := le_trans (le_of_lt hCover) ih
      simpa only [cyclicAdvance_add, Nat.add_comm] using h

/-- A nonempty cover sequence strictly increases squared distance. -/
theorem sqDist_lt_terminal_of_positive
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    {leftMoves rightMoves : ℕ}
    (path : K3CoverSequence P i j leftMoves rightMoves)
    (hpositive : 0 < leftMoves + rightMoves) :
    sqDist (P i) (P j) <
      sqDist (P (cyclicRetreat i leftMoves))
        (P (cyclicAdvance j rightMoves)) := by
  cases path with
  | nil => omega
  | @left i j leftMoves rightMoves hCover tail =>
      have h := lt_of_lt_of_le hCover (sqDist_le_terminal tail)
      simpa only [cyclicRetreat_add, Nat.add_comm] using h
  | @right i j leftMoves rightMoves hCover tail =>
      have h := lt_of_lt_of_le hCover (sqDist_le_terminal tail)
      simpa only [cyclicAdvance_add, Nat.add_comm] using h

end K3CoverSequence

/-- A positive-length majorant path cannot terminate in the smallest of the
three graph ranks.  Its terminal edge is `d₁` or `d₂`, but one move alone
does not determine which. -/
theorem K3MajorantWitness.terminal_rank_top_two_of_positive
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (W : K3MajorantWitness P d₁ d₂ d₃ i j)
    (hpositive : 0 < W.leftMoves + W.rightMoves) :
    sqDist (P (cyclicRetreat i W.leftMoves))
        (P (cyclicAdvance j W.rightMoves)) = d₁ ∨
      sqDist (P (cyclicRetreat i W.leftMoves))
        (P (cyclicAdvance j W.rightMoves)) = d₂ := by
  have hlt := K3CoverSequence.sqDist_lt_terminal_of_positive W.path hpositive
  rcases W.adjacent.2 with h₁ | h₂ | h₃
  · exact Or.inl h₁
  · exact Or.inr h₂
  · rcases hStart.2 with hs₁ | hs₂ | hs₃ <;>
      have hd₃d₂ := hClasses.1 <;>
      have hd₂d₁ := hClasses.2.1 <;> linarith

theorem ErLVAtVertexUseSite.first_start_adjacent
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) :
    TopThreeAdjacent P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ S.x) S.x := by
  apply topThreeAdjacent_symm
  apply firstClockwiseNeighbor_adjacent_of_degree_pos
  have := S.highDegree S.x
  omega

theorem ErLVAtVertexUseSite.second_start_adjacent
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) :
    TopThreeAdjacent P d₁ d₂ d₃ (cyclicAdvance S.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3)) := by
  apply firstCounterclockwiseNeighbor_adjacent_of_degree_pos
  have := S.highDegree (cyclicAdvance S.x 3)
  omega

/-- Exact shared-tip data in case `(1,2)`.  The second chain supplies a
`d₂` rung at `x+2` and a `d₁` terminal at the common tip `x+1`.  The other
edge incident to that tip is only forced into `d₁ ∨ d₂`; its color is not
fixed.  Thus the rigid branch does not itself supply the claimed forced
`d₂+d₁` pair at the common vertex. -/
theorem erlv_case12_shared_tip_rank_data
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (h12 : S.Case12) :
    let z := firstClockwiseNeighbor P d₁ d₂ d₃ S.x
    let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3)
    sqDist (P (cyclicAdvance S.x 1)) (P u) = d₁ ∧
      (sqDist (P (cyclicRetreat z S.pair.first.leftMoves))
          (P (cyclicAdvance S.x 1)) = d₁ ∨
        sqDist (P (cyclicRetreat z S.pair.first.leftMoves))
          (P (cyclicAdvance S.x 1)) = d₂) ∧
      sqDist (P (cyclicAdvance S.x 2)) (P u) = d₂ := by
  dsimp only
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hBeta : S.pair.second.rightMoves = 0 := by
    have hBudget := S.pair.second.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case12] at h12
    omega
  have hSecondPath : K3CoverSequence P (cyclicAdvance S.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3)) 2 0 :=
    h12.2 ▸ hBeta ▸ S.pair.second.path
  have hSecondRanks := left_left_cover_rank_ladder S.classes
    S.second_start_adjacent hSecondPath
  have hretreatOne :
      cyclicRetreat (cyclicAdvance S.x 3) 1 = cyclicAdvance S.x 2 := by
    simpa using cyclicRetreat_advance S.x (k := 3) (m := 1) (by omega) (by omega)
  have hretreatTwo :
      cyclicRetreat (cyclicAdvance S.x 3) 2 = cyclicAdvance S.x 1 := by
    simpa using cyclicRetreat_advance S.x (k := 3) (m := 2) (by omega) (by omega)
  have hFirstPositive :
      0 < S.pair.first.leftMoves + S.pair.first.rightMoves := by
    dsimp only [ErLVAtVertexUseSite.Case12] at h12
    omega
  have hFirstTopTwo :=
    S.pair.first.terminal_rank_top_two_of_positive S.classes
      S.first_start_adjacent hFirstPositive
  dsimp only [ErLVAtVertexUseSite.Case12] at h12
  rw [h12.1] at hFirstTopTwo
  refine ⟨?_, hFirstTopTwo, ?_⟩
  · simpa [hretreatTwo] using hSecondRanks.2.2
  · simpa [hretreatOne] using hSecondRanks.2.1

/-- Mirror shared-tip data in case `(2,1)`.  Again one incident terminal is
`d₁`, while the other is only `d₁ ∨ d₂`; the forced `d₂` rung is based at
the adjacent vertex `x+1`, not at the common tip `x+2`. -/
theorem erlv_case21_shared_tip_rank_data
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (h21 : S.Case21) :
    let z := firstClockwiseNeighbor P d₁ d₂ d₃ S.x
    let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3)
    sqDist (P z) (P (cyclicAdvance S.x 2)) = d₁ ∧
      (sqDist (P (cyclicAdvance S.x 2))
          (P (cyclicAdvance u S.pair.second.rightMoves)) = d₁ ∨
        sqDist (P (cyclicAdvance S.x 2))
          (P (cyclicAdvance u S.pair.second.rightMoves)) = d₂) ∧
      sqDist (P z) (P (cyclicAdvance S.x 1)) = d₂ := by
  dsimp only
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hB : S.pair.first.leftMoves = 0 := by
    have hBudget := S.pair.first.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case21] at h21
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ S.x) S.x 0 2 :=
    hB ▸ h21.1 ▸ S.pair.first.path
  have hFirstRanks := right_right_cover_rank_ladder S.classes
    S.first_start_adjacent hFirstPath
  have hretreatOne :
      cyclicRetreat (cyclicAdvance S.x 3) 1 = cyclicAdvance S.x 2 := by
    simpa using cyclicRetreat_advance S.x (k := 3) (m := 1) (by omega) (by omega)
  have hSecondPositive :
      0 < S.pair.second.leftMoves + S.pair.second.rightMoves := by
    dsimp only [ErLVAtVertexUseSite.Case21] at h21
    omega
  have hSecondTopTwo :=
    S.pair.second.terminal_rank_top_two_of_positive S.classes
      S.second_start_adjacent hSecondPositive
  dsimp only [ErLVAtVertexUseSite.Case21] at h21
  rw [h21.2, hretreatOne] at hSecondTopTwo
  exact ⟨hFirstRanks.2.2, hSecondTopTwo, hFirstRanks.2.1⟩

/-- Strict ED on two equal `d₃` avoiding sides forces one cross edge into
the top two classes, not merely into the top-three graph. -/
theorem equal_d3_avoiding_edges_force_cross_top_two
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {a b c d : Fin n}
    (hquad : StrictConvexQuad (P a) (P b) (P c) (P d))
    (hab : TopThreeAdjacent P d₁ d₂ d₃ a b)
    (hcd : TopThreeAdjacent P d₁ d₂ d₃ c d)
    (habRank : sqDist (P a) (P b) = d₃)
    (hcdRank : sqDist (P c) (P d) = d₃) :
    (sqDist (P a) (P c) = d₁ ∨ sqDist (P a) (P c) = d₂) ∨
      (sqDist (P b) (P d) = d₁ ∨ sqDist (P b) (P d) = d₂) := by
  have hEdge := edge_diagonal_inequality hquad
  have habSq := euclideanDist_sq (P a) (P b)
  have hcdSq := euclideanDist_sq (P c) (P d)
  have hacSq := euclideanDist_sq (P a) (P c)
  have hbdSq := euclideanDist_sq (P b) (P d)
  have habNonneg : 0 ≤ euclideanDist (P a) (P b) := dist_nonneg
  have hcdNonneg : 0 ≤ euclideanDist (P c) (P d) := dist_nonneg
  have hacNonneg : 0 ≤ euclideanDist (P a) (P c) := dist_nonneg
  have hbdNonneg : 0 ≤ euclideanDist (P b) (P d) := dist_nonneg
  have hSideEq : euclideanDist (P a) (P b) =
      euclideanDist (P c) (P d) := by
    nlinarith
  by_cases hacLong : euclideanDist (P a) (P b) <
      euclideanDist (P a) (P c)
  · left
    have hGrow : sqDist (P a) (P b) < sqDist (P a) (P c) := by
      nlinarith
    have hAdj := top_three_adjacent_of_strictly_longer hClasses hab hGrow
    rcases hAdj.2 with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · linarith
  · right
    have hacLe : euclideanDist (P a) (P c) ≤
        euclideanDist (P a) (P b) := le_of_not_gt hacLong
    have hbdLong : euclideanDist (P c) (P d) <
        euclideanDist (P b) (P d) := by
      linarith
    have hGrow : sqDist (P c) (P d) < sqDist (P b) (P d) := by
      nlinarith
    have hAdj := top_three_adjacent_of_strictly_longer hClasses hcd hGrow
    rcases hAdj.2 with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · linarith

/-- Exact ED output in case `(2,2)`: the inserted cross edge is `d₁ ∨ d₂`.
The kernel does not force the `d₂` color required to enter the terminal
`d₂`-cage directly. -/
theorem erlv_case22_cross_top_two_rank_data
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (h22 : S.Case22) :
    let z := firstClockwiseNeighbor P d₁ d₂ d₃ S.x
    let t := cyclicAdvance S.x 3
    let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
    (sqDist (P z) (P t) = d₁ ∨ sqDist (P z) (P t) = d₂) ∨
      (sqDist (P S.x) (P u) = d₁ ∨ sqDist (P S.x) (P u) = d₂) := by
  dsimp only
  have hB : S.pair.first.leftMoves = 0 := by
    have hBudget := S.pair.first.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case22] at h22
    omega
  have hBeta : S.pair.second.rightMoves = 0 := by
    have hBudget := S.pair.second.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case22] at h22
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ S.x) S.x 0 2 :=
    hB ▸ h22.1 ▸ S.pair.first.path
  have hSecondPath : K3CoverSequence P (cyclicAdvance S.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3)) 2 0 :=
    h22.2 ▸ hBeta ▸ S.pair.second.path
  have hFirstRanks := right_right_cover_rank_ladder S.classes
    S.first_start_adjacent hFirstPath
  have hSecondRanks := left_left_cover_rank_ladder S.classes
    S.second_start_adjacent hSecondPath
  have hquad := erlv_start_edges_strict_convex_quad
    S.convex S.highDegree S.x S.maximalGap
  have hCross := equal_d3_avoiding_edges_force_cross_top_two S.classes hquad
    S.second_start_adjacent S.first_start_adjacent
    hSecondRanks.1 hFirstRanks.1
  rcases hCross with htz | hux
  · exact Or.inl (by simpa only [sqDist_comm] using htz)
  · exact Or.inr (by simpa only [sqDist_comm] using hux)

namespace ErLVAtVertexUseSite

/-- The geometric outer-endpoint localization required to interpret `M` as
the side distance from `u` to the first terminal endpoint.  This is exactly
the missing nesting conclusion, specialized to one selected use-site pair. -/
def OuterLocalized
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : Prop :=
  ∃ M : ℕ, M ≤ S.pair.second.rightMoves ∧
    cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)
        S.pair.first.leftMoves =
      cyclicAdvance
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3)) M

end ErLVAtVertexUseSite

/-- Once an exceptional inner-count branch has the missing outer
localization, its arithmetic is already in the direct short-arc branch.  It
does not produce one of the five exceptional rows. -/
theorem erlv_exceptional_use_site_localization_short_arc
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃)
    (hExceptional : 3 ≤
      S.pair.first.rightMoves + S.pair.second.leftMoves)
    (M : ℕ) (hM : M ≤ S.pair.second.rightMoves) :
    let D := erlvK3MaximalGapSetupOfMajorants
      S.pair.first S.pair.second (S.maximalGap (cyclicAdvance S.x 3)) M hM
    D.yzSides ≤ 5 := by
  let D := erlvK3MaximalGapSetupOfMajorants
    S.pair.first S.pair.second (S.maximalGap (cyclicAdvance S.x 3)) M hM
  change D.yzSides ≤ 5
  have hL : D.L ≤ 3 := maximal_gap_L_le_three D
  have hBM : S.pair.first.leftMoves + M ≤ 2 := by
    rcases coordinated_inner_endpoint_budget_partition S.pair with
      hGood | h12 | h21 | h22
    · omega
    · have hFirstBudget := S.pair.first.coverBudget
      have hSecondBudget := S.pair.second.coverBudget
      omega
    · have hFirstBudget := S.pair.first.coverBudget
      have hSecondBudget := S.pair.second.coverBudget
      omega
    · have hFirstBudget := S.pair.first.coverBudget
      have hSecondBudget := S.pair.second.coverBudget
      omega
  have hBMInt :
      (S.pair.first.leftMoves : ℤ) + (M : ℤ) ≤ 2 := by
    exact_mod_cast hBM
  change D.L + (M : ℤ) + (S.pair.first.leftMoves : ℤ) ≤ 5
  omega

/-- Kernel check against the five-row enumeration: after outer localization,
none of the rigid `(1,2)/(2,1)/(2,2)` inner-count cases realizes a table row.
The two partitions concern different variables. -/
theorem erlv_exceptional_use_site_localization_avoids_five_rows
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃)
    (hExceptional : 3 ≤
      S.pair.first.rightMoves + S.pair.second.leftMoves)
    (M : ℕ) (hM : M ≤ S.pair.second.rightMoves) :
    let D := erlvK3MaximalGapSetupOfMajorants
      S.pair.first S.pair.second (S.maximalGap (cyclicAdvance S.x 3)) M hM
    ¬IsExceptionalMajorantRow
      D.first.leftMoves D.first.rightMoves D.L D.M := by
  let D := erlvK3MaximalGapSetupOfMajorants
    S.pair.first S.pair.second (S.maximalGap (cyclicAdvance S.x 3)) M hM
  change ¬IsExceptionalMajorantRow
    D.first.leftMoves D.first.rightMoves D.L D.M
  intro hRow
  have hLong : 5 < D.yzSides :=
    (maximal_gap_five_row_enumeration D).2 hRow
  have hShort : D.yzSides ≤ 5 :=
    erlv_exceptional_use_site_localization_short_arc
      S hExceptional M hM
  omega

/-- The two exact color subcases left at the shared tip in `(1,2)`. -/
def ErLVAtVertexCase12OtherD1Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case12 →
      sqDist
        (P (cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)
          S.pair.first.leftMoves))
        (P (cyclicAdvance S.x 1)) = d₁ → False

/-- The remaining `d₂` terminal color is impossible in the `(1,2)` branch. -/
def ErLVAtVertexCase12OtherD2Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case12 →
      sqDist
        (P (cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)
          S.pair.first.leftMoves))
        (P (cyclicAdvance S.x 1)) = d₂ → False

/-- Closing both actual terminal colors would close the `(1,2)` branch. -/
theorem erlv_at_vertex_case12_impossible_of_terminal_colors
    (hD1 : ErLVAtVertexCase12OtherD1Impossible)
    (hD2 : ErLVAtVertexCase12OtherD2Impossible) :
    ErLVAtVertexCase12Impossible := by
  intro n _ P d₁ d₂ d₃ S h12
  have hData := erlv_case12_shared_tip_rank_data S h12
  rcases hData.2.1 with hOtherD1 | hOtherD2
  · exact hD1 P d₁ d₂ d₃ S h12 hOtherD1
  · exact hD2 P d₁ d₂ d₃ S h12 hOtherD2

/-- The mirror terminal-color split left at the shared tip in `(2,1)`. -/
def ErLVAtVertexCase21OtherD1Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case21 →
      sqDist (P (cyclicAdvance S.x 2))
        (P (cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3))
          S.pair.second.rightMoves)) = d₁ → False

/-- The remaining `d₂` terminal color is impossible in the `(2,1)` branch. -/
def ErLVAtVertexCase21OtherD2Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case21 →
      sqDist (P (cyclicAdvance S.x 2))
        (P (cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3))
          S.pair.second.rightMoves)) = d₂ → False

/-- Closing both actual terminal colors would close the `(2,1)` branch. -/
theorem erlv_at_vertex_case21_impossible_of_terminal_colors
    (hD1 : ErLVAtVertexCase21OtherD1Impossible)
    (hD2 : ErLVAtVertexCase21OtherD2Impossible) :
    ErLVAtVertexCase21Impossible := by
  intro n _ P d₁ d₂ d₃ S h21
  have hData := erlv_case21_shared_tip_rank_data S h21
  rcases hData.2.1 with hOtherD1 | hOtherD2
  · exact hD1 P d₁ d₂ d₃ S h21 hOtherD1
  · exact hD2 P d₁ d₂ d₃ S h21 hOtherD2

/-- Four exact top-two cross-color subcases left in `(2,2)`.  The `d₂`
subcases are the only ones even color-compatible with the terminal `d₂`
cage; the `d₁` subcases require a different full-two-rung adapter. -/
def ErLVAtVertexCase22ZTD1Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case22 →
      sqDist (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x))
        (P (cyclicAdvance S.x 3)) = d₁ → False

/-- The `zt = d₂` cross-color subcase is impossible in the `(2,2)` branch. -/
def ErLVAtVertexCase22ZTD2Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case22 →
      sqDist (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x))
        (P (cyclicAdvance S.x 3)) = d₂ → False

/-- The `xu = d₁` cross-color subcase is impossible in the `(2,2)` branch. -/
def ErLVAtVertexCase22XUD1Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case22 →
      sqDist (P S.x)
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) = d₁ → False

/-- The `xu = d₂` cross-color subcase is impossible in the `(2,2)` branch. -/
def ErLVAtVertexCase22XUD2Impossible : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    ∀ S : ErLVAtVertexUseSite P d₁ d₂ d₃, S.Case22 →
      sqDist (P S.x)
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) = d₂ → False

/-- The strengthened ED theorem reduces `(2,2)` exactly to the four named
cross-edge/color obligations. -/
theorem erlv_at_vertex_case22_impossible_of_cross_colors
    (hZTD1 : ErLVAtVertexCase22ZTD1Impossible)
    (hZTD2 : ErLVAtVertexCase22ZTD2Impossible)
    (hXUD1 : ErLVAtVertexCase22XUD1Impossible)
    (hXUD2 : ErLVAtVertexCase22XUD2Impossible) :
    ErLVAtVertexCase22Impossible := by
  intro n _ P d₁ d₂ d₃ S h22
  rcases erlv_case22_cross_top_two_rank_data S h22 with hZT | hXU
  · rcases hZT with hD1 | hD2
    · exact hZTD1 P d₁ d₂ d₃ S h22 hD1
    · exact hZTD2 P d₁ d₂ d₃ S h22 hD2
  · rcases hXU with hD1 | hD2
    · exact hXUD1 P d₁ d₂ d₃ S h22 hD1
    · exact hXUD2 P d₁ d₂ d₃ S h22 hD2

/-- The exact remaining use-site boundary after the rigid branch analysis:
two terminal colors in each shared-tip branch and four cross-edge/color
possibilities in the `(2,2)` branch.  Discharging these eight propositions is
sufficient for the at-the-vertex replacement of the abstract exchange. -/
theorem erlv_at_vertex_exceptional_branches_impossible_of_color_cases
    (h12D1 : ErLVAtVertexCase12OtherD1Impossible)
    (h12D2 : ErLVAtVertexCase12OtherD2Impossible)
    (h21D1 : ErLVAtVertexCase21OtherD1Impossible)
    (h21D2 : ErLVAtVertexCase21OtherD2Impossible)
    (h22ZTD1 : ErLVAtVertexCase22ZTD1Impossible)
    (h22ZTD2 : ErLVAtVertexCase22ZTD2Impossible)
    (h22XUD1 : ErLVAtVertexCase22XUD1Impossible)
    (h22XUD2 : ErLVAtVertexCase22XUD2Impossible) :
    ErLVAtVertexExceptionalBranchesImpossible := by
  rw [erlv_at_vertex_exceptional_branches_impossible_iff_cases]
  exact
    ⟨erlv_at_vertex_case12_impossible_of_terminal_colors h12D1 h12D2,
      erlv_at_vertex_case21_impossible_of_terminal_colors h21D1 h21D2,
      erlv_at_vertex_case22_impossible_of_cross_colors
        h22ZTD1 h22ZTD2 h22XUD1 h22XUD2⟩

/-- The same exact eight-subcase boundary, connected all the way to the
source-facing nesting interface used by the global reduction. -/
theorem erlv_majorant_arc_nesting_complete_of_at_vertex_color_cases
    (h12D1 : ErLVAtVertexCase12OtherD1Impossible)
    (h12D2 : ErLVAtVertexCase12OtherD2Impossible)
    (h21D1 : ErLVAtVertexCase21OtherD1Impossible)
    (h21D2 : ErLVAtVertexCase21OtherD2Impossible)
    (h22ZTD1 : ErLVAtVertexCase22ZTD1Impossible)
    (h22ZTD2 : ErLVAtVertexCase22ZTD2Impossible)
    (h22XUD1 : ErLVAtVertexCase22XUD1Impossible)
    (h22XUD2 : ErLVAtVertexCase22XUD2Impossible) :
    ErLVMajorantArcNestingComplete :=
  erlv_majorant_arc_nesting_complete_of_at_vertex_closure
    (erlv_at_vertex_exceptional_branches_impossible_of_color_cases
      h12D1 h12D2 h21D1 h21D2 h22ZTD1 h22ZTD2 h22XUD1 h22XUD2)

end LeanPool.Erdos132ConvexK3
