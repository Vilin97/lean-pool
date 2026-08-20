/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Assembly
import LeanPool.Erdos132ConvexK3.TerminalColorClosure
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Global convex k = 3 assembly

This file connects the raw convex/top-three hypotheses to the ErLV
maximal-gap diagram.  The unconditional terminal-color closure supplies the
jointly selected majorants and their outer-endpoint localization.  The first
stage below packages that data and instantiates the five-row enumeration.
-/

namespace LeanPool.Erdos132ConvexK3

namespace K3CoverSequence

/-- The first strict cover move acts at the left endpoint. -/
inductive StartsLeft
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} :
    {i j : Fin n} → {leftMoves rightMoves : ℕ} →
      K3CoverSequence P i j leftMoves rightMoves → Prop where
  | intro {i j : Fin n} {leftMoves rightMoves : ℕ}
      (h : IsLeftCover P i j)
      (tail : K3CoverSequence P (cyclicRetreat i 1) j leftMoves rightMoves) :
      StartsLeft (.left h tail)

/-- The first strict cover move acts at the right endpoint. -/
inductive StartsRight
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} :
    {i j : Fin n} → {leftMoves rightMoves : ℕ} →
      K3CoverSequence P i j leftMoves rightMoves → Prop where
  | intro {i j : Fin n} {leftMoves rightMoves : ℕ}
      (h : IsRightCover P i j)
      (tail : K3CoverSequence P i (cyclicAdvance j 1) leftMoves rightMoves) :
      StartsRight (.right h tail)

/-- The actual path consists of one left-end cover. -/
def IsSingleLeft
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 1 0) : Prop :=
  ∃ h : IsLeftCover P i j, path = .left h (.nil _ _)

/-- The actual path consists of one right-end cover. -/
def IsSingleRight
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 0 1) : Prop :=
  ∃ h : IsRightCover P i j, path = .right h (.nil _ _)

/-- The actual path consists of two left-end covers. -/
def IsDoubleLeft
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 2 0) : Prop :=
  ∃ (h₀ : IsLeftCover P i j)
      (h₁ : IsLeftCover P (cyclicRetreat i 1) j),
    path = .left h₀ (.left h₁ (.nil _ _))

/-- First a left-end cover, then a right-end cover. -/
def IsLeftRight
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 1 1) : Prop :=
  ∃ (h₀ : IsLeftCover P i j)
      (h₁ : IsRightCover P (cyclicRetreat i 1) j),
    path = .left h₀ (.right h₁ (.nil _ _))

/-- First a right-end cover, then a left-end cover. -/
def IsRightLeft
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 1 1) : Prop :=
  ∃ (h₀ : IsRightCover P i j)
      (h₁ : IsLeftCover P i (cyclicAdvance j 1)),
    path = .right h₀ (.left h₁ (.nil _ _))

/-- The actual path consists of two right-end covers. -/
def IsDoubleRight
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 0 2) : Prop :=
  ∃ (h₀ : IsRightCover P i j)
      (h₁ : IsRightCover P i (cyclicAdvance j 1)),
    path = .right h₀ (.right h₁ (.nil _ _))

theorem isSingleLeft
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 1 0) : path.IsSingleLeft := by
  cases path with
  | left h tail =>
      cases tail with
      | nil => exact ⟨h, rfl⟩

theorem isSingleRight
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 0 1) : path.IsSingleRight := by
  cases path with
  | right h tail =>
      cases tail with
      | nil => exact ⟨h, rfl⟩

theorem isDoubleLeft
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 2 0) : path.IsDoubleLeft := by
  cases path with
  | left h₀ tail =>
      cases tail with
      | left h₁ tail =>
          cases tail with
          | nil => exact ⟨h₀, h₁, rfl⟩

theorem oneEachOrder
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 1 1) :
    path.IsLeftRight ∨ path.IsRightLeft := by
  cases path with
  | left h₀ tail =>
      cases tail with
      | right h₁ tail =>
          cases tail with
          | nil => exact Or.inl ⟨h₀, h₁, rfl⟩
  | right h₀ tail =>
      cases tail with
      | left h₁ tail =>
          cases tail with
          | nil => exact Or.inr ⟨h₀, h₁, rfl⟩

theorem isDoubleRight
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (path : K3CoverSequence P i j 0 2) : path.IsDoubleRight := by
  cases path with
  | right h₀ tail =>
      cases tail with
      | right h₁ tail =>
          cases tail with
          | nil => exact ⟨h₀, h₁, rfl⟩

theorem startsLeft_or_startsRight_of_positive
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    {leftMoves rightMoves : ℕ}
    (path : K3CoverSequence P i j leftMoves rightMoves)
    (hpositive : 0 < leftMoves + rightMoves) :
    path.StartsLeft ∨ path.StartsRight := by
  cases path with
  | nil => omega
  | left h tail => exact Or.inl (.intro h tail)
  | right h tail => exact Or.inr (.intro h tail)

theorem startsLeft_of_left_positive_right_zero
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    {leftMoves rightMoves : ℕ}
    (path : K3CoverSequence P i j leftMoves rightMoves)
    (hleft : 0 < leftMoves) (hright : rightMoves = 0) :
    path.StartsLeft := by
  cases path with
  | nil => omega
  | left h tail => exact .intro h tail
  | right => omega

theorem startsRight_of_left_zero_right_positive
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    {leftMoves rightMoves : ℕ}
    (path : K3CoverSequence P i j leftMoves rightMoves)
    (hleft : leftMoves = 0) (hright : 0 < rightMoves) :
    path.StartsRight := by
  cases path with
  | nil => omega
  | left => omega
  | right h tail => exact .intro h tail

end K3CoverSequence

/-- A single strict rank increase between top-three edges has exactly one of
the three transitions `d₃→d₂`, `d₃→d₁`, or `d₂→d₁`. -/
theorem strict_top_three_rank_transition
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j p q : Fin n}
    (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (hEnd : TopThreeAdjacent P d₁ d₂ d₃ p q)
    (hRaise : sqDist (P i) (P j) < sqDist (P p) (P q)) :
    (sqDist (P i) (P j) = d₃ ∧ sqDist (P p) (P q) = d₂) ∨
      (sqDist (P i) (P j) = d₃ ∧ sqDist (P p) (P q) = d₁) ∨
      (sqDist (P i) (P j) = d₂ ∧ sqDist (P p) (P q) = d₁) := by
  have hd₃d₂ := hClasses.1
  have hd₂d₁ := hClasses.2.1
  rcases hStart.2 with hs₁ | hs₂ | hs₃ <;>
    rcases hEnd.2 with he₁ | he₂ | he₃
  · linarith
  · linarith
  · linarith
  · exact Or.inr (Or.inr ⟨hs₂, he₁⟩)
  · linarith
  · linarith
  · exact Or.inr (Or.inl ⟨hs₃, he₁⟩)
  · exact Or.inl ⟨hs₃, he₂⟩
  · linarith

/-- The geometric maximal-gap frame obtained in the high-minimum-degree
branch, including the jointly minimal majorants and the now-proved outer
endpoint localization. -/
structure ErLVGlobalFiveRowFrame
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  convex : CyclicStrictConvex P
  classes : HasTopThreeDistanceClasses P d₁ d₂ d₃
  highDegree : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v
  /-- Vertex whose first-neighbor gap is maximal. -/
  x : Fin n
  maximalGap : ∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
    firstNeighborGap P d₁ d₂ d₃ x
  /-- Jointly minimal majorants anchored at the selected vertex. -/
  pair : CoordinatedK3MajorantPair P d₁ d₂ d₃
    (firstClockwiseNeighbor P d₁ d₂ d₃ x) x
    (cyclicAdvance x 3)
    (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3))
  /-- Outer localization offset along the second majorant. -/
  M : ℕ
  M_le_secondRight : M ≤ pair.second.rightMoves
  outerLocalized :
    cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ x)
        pair.first.leftMoves =
      cyclicAdvance
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)) M

namespace ErLVGlobalFiveRowFrame

/-- The global frame contains exactly the data required by the established
degree-seven use-site lemmas. -/
noncomputable def toUseSite
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    ErLVAtVertexUseSite P d₁ d₂ d₃ :=
  erlvAtVertexUseSiteOfHighDegree F.convex F.classes F.highDegree
    F.x F.maximalGap F.pair

/-- Forget the geometric labels while retaining the exact arithmetic data
used by the five-row enumeration. -/
noncomputable def setup
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ErLVK3MaximalGapSetup :=
  erlvK3MaximalGapSetupOfMajorants F.pair.first F.pair.second
    (F.maximalGap (cyclicAdvance F.x 3)) F.M F.M_le_secondRight

/-- First exceptional row of the five-row count table. -/
def Row1
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.pair.first.rightMoves = 0 ∧ F.pair.first.leftMoves = 1 ∧
    F.setup.L = 3 ∧ F.M = 2

/-- Second exceptional row of the five-row count table. -/
def Row2
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.pair.first.rightMoves = 1 ∧ F.pair.first.leftMoves = 1 ∧
    F.setup.L = 3 ∧ F.M = 2

/-- Third exceptional row of the five-row count table. -/
def Row3
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.pair.first.rightMoves = 0 ∧ F.pair.first.leftMoves = 2 ∧
    F.setup.L = 2 ∧ F.M = 2

/-- Fourth exceptional row of the five-row count table. -/
def Row4
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.pair.first.rightMoves = 0 ∧ F.pair.first.leftMoves = 2 ∧
    F.setup.L = 3 ∧ F.M = 1

/-- Fifth exceptional row of the five-row count table. -/
def Row5
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.pair.first.rightMoves = 0 ∧ F.pair.first.leftMoves = 2 ∧
    F.setup.L = 3 ∧ F.M = 2

theorem exceptional_row_iff_rows
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    IsExceptionalMajorantRow F.setup.first.leftMoves
        F.setup.first.rightMoves F.setup.L F.setup.M ↔
      F.Row1 ∨ F.Row2 ∨ F.Row3 ∨ F.Row4 ∨ F.Row5 := by
  simp [IsExceptionalMajorantRow, Row1, Row2, Row3, Row4, Row5, setup,
    erlvK3MaximalGapSetupOfMajorants, K3MajorantWitness.toFirstK3Majorant]
  norm_cast

/-- Squared distance of the first majorant's starting edge. -/
noncomputable def firstStartSqDist
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ℝ :=
  sqDist (P (firstClockwiseNeighbor P d₁ d₂ d₃ F.x)) (P F.x)

/-- Squared distance of the first majorant's terminal edge. -/
noncomputable def firstTerminalSqDist
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ℝ :=
  sqDist
    (P (cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x)
      F.pair.first.leftMoves))
    (P (cyclicAdvance F.x F.pair.first.rightMoves))

/-- Squared distance of the second majorant's starting edge. -/
noncomputable def secondStartSqDist
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ℝ :=
  sqDist (P (cyclicAdvance F.x 3))
    (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3)))

/-- Squared distance of the second majorant's terminal edge. -/
noncomputable def secondTerminalSqDist
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ℝ :=
  sqDist
    (P (cyclicRetreat (cyclicAdvance F.x 3) F.pair.second.leftMoves))
    (P (cyclicAdvance
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3))
      F.pair.second.rightMoves))

/-- The first majorant changes rank from `d₃` to `d₂`. -/
def FirstRank32
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.firstStartSqDist = d₃ ∧ F.firstTerminalSqDist = d₂

/-- The first majorant changes rank from `d₃` to `d₁`. -/
def FirstRank31
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.firstStartSqDist = d₃ ∧ F.firstTerminalSqDist = d₁

/-- The first majorant changes rank from `d₂` to `d₁`. -/
def FirstRank21
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.firstStartSqDist = d₂ ∧ F.firstTerminalSqDist = d₁

/-- The second majorant changes rank from `d₃` to `d₂`. -/
def SecondRank32
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.secondStartSqDist = d₃ ∧ F.secondTerminalSqDist = d₂

/-- The second majorant changes rank from `d₃` to `d₁`. -/
def SecondRank31
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.secondStartSqDist = d₃ ∧ F.secondTerminalSqDist = d₁

/-- The second majorant changes rank from `d₂` to `d₁`. -/
def SecondRank21
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : Prop :=
  F.secondStartSqDist = d₂ ∧ F.secondTerminalSqDist = d₁

theorem first_rank_transition_of_positive
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hpositive : 0 < F.pair.first.leftMoves + F.pair.first.rightMoves) :
    F.FirstRank32 ∨ F.FirstRank31 ∨ F.FirstRank21 := by
  have hstart : TopThreeAdjacent P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x := by
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree F.x
    omega
  have hraise := K3CoverSequence.sqDist_lt_terminal_of_positive
    F.pair.first.path hpositive
  simpa [FirstRank32, FirstRank31, FirstRank21, firstStartSqDist,
    firstTerminalSqDist] using
      strict_top_three_rank_transition F.classes hstart
        F.pair.first.adjacent hraise

theorem second_rank_transition_of_positive
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hpositive : 0 < F.pair.second.leftMoves + F.pair.second.rightMoves) :
    F.SecondRank32 ∨ F.SecondRank31 ∨ F.SecondRank21 := by
  have hstart : TopThreeAdjacent P d₁ d₂ d₃ (cyclicAdvance F.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3)) := by
    apply firstCounterclockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree (cyclicAdvance F.x 3)
    omega
  have hraise := K3CoverSequence.sqDist_lt_terminal_of_positive
    F.pair.second.path hpositive
  simpa [SecondRank32, SecondRank31, SecondRank21, secondStartSqDist,
    secondTerminalSqDist] using
      strict_top_three_rank_transition F.classes hstart
        F.pair.second.adjacent hraise

/-- Geometric semantics of the thirteen cover words for one localized
maximal-gap frame.  The letters record the actual endpoint order (`A/B` for
the first path and `C/D` for the second); the one-step words also retain the
exact strict rank transition. -/
def RealizesCoverWord
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    ExceptionalCoverWord → Prop
  | .row1_B32 => F.Row1 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.path.StartsRight ∧ F.FirstRank32
  | .row1_B31 => F.Row1 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.path.StartsRight ∧ F.FirstRank31
  | .row1_B21 => F.Row1 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.path.StartsRight ∧ F.FirstRank21
  | .row2_AB => F.Row2 ∧ F.pair.first.path.StartsRight ∧
      F.pair.second.path.StartsRight
  | .row2_BA => F.Row2 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.path.StartsRight
  | .row3_BB_DD => F.Row3 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.path.StartsRight
  | .row4_D32 => F.Row4 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.leftMoves = 0 ∧ F.pair.second.rightMoves = 1 ∧
      F.pair.second.path.StartsRight ∧ F.SecondRank32
  | .row4_D31 => F.Row4 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.leftMoves = 0 ∧ F.pair.second.rightMoves = 1 ∧
      F.pair.second.path.StartsRight ∧ F.SecondRank31
  | .row4_D21 => F.Row4 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.leftMoves = 0 ∧ F.pair.second.rightMoves = 1 ∧
      F.pair.second.path.StartsRight ∧ F.SecondRank21
  | .row4_CD => F.Row4 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.leftMoves = 1 ∧ F.pair.second.rightMoves = 1 ∧
      F.pair.second.path.StartsLeft
  | .row4_DC => F.Row4 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.leftMoves = 1 ∧ F.pair.second.rightMoves = 1 ∧
      F.pair.second.path.StartsRight
  | .row4_DD => F.Row4 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.leftMoves = 0 ∧ F.pair.second.rightMoves = 2 ∧
      F.pair.second.path.StartsRight
  | .row5_BB_DD => F.Row5 ∧ F.pair.first.path.StartsLeft ∧
      F.pair.second.path.StartsRight

/-- Every actual exceptional row expands to one of exactly the thirteen
cover words in the draft table. -/
theorem exceptional_row_realizes_cover_word
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hRow : IsExceptionalMajorantRow F.setup.first.leftMoves
      F.setup.first.rightMoves F.setup.L F.setup.M) :
    ∃ w, F.RealizesCoverWord w := by
  rcases F.exceptional_row_iff_rows.mp hRow with h1 | h2 | h3 | h4 | h5
  · dsimp only [Row1] at h1
    have hFirst : F.pair.first.path.StartsLeft :=
      K3CoverSequence.startsLeft_of_left_positive_right_zero
        F.pair.first.path (by rw [h1.2.1]; omega) h1.1
    have hSecondLeft : F.pair.second.leftMoves = 0 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecondRight : F.pair.second.rightMoves = 2 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecondStart : F.pair.second.path.StartsRight :=
      K3CoverSequence.startsRight_of_left_zero_right_positive
        F.pair.second.path hSecondLeft (by rw [hSecondRight]; omega)
    rcases F.first_rank_transition_of_positive (by
      rw [h1.1, h1.2.1]
      omega) with h32 | h31 | h21
    · exact ⟨.row1_B32, h1, hFirst, hSecondStart, h32⟩
    · exact ⟨.row1_B31, h1, hFirst, hSecondStart, h31⟩
    · exact ⟨.row1_B21, h1, hFirst, hSecondStart, h21⟩
  · dsimp only [Row2] at h2
    have hSecondLeft : F.pair.second.leftMoves = 0 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecondRight : F.pair.second.rightMoves = 2 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecondStart : F.pair.second.path.StartsRight :=
      K3CoverSequence.startsRight_of_left_zero_right_positive
        F.pair.second.path hSecondLeft (by rw [hSecondRight]; omega)
    rcases K3CoverSequence.startsLeft_or_startsRight_of_positive
      F.pair.first.path (by rw [h2.1, h2.2.1]; omega) with hLeft | hRight
    · exact ⟨.row2_BA, h2, hLeft, hSecondStart⟩
    · exact ⟨.row2_AB, h2, hRight, hSecondStart⟩
  · dsimp only [Row3] at h3
    have hFirst : F.pair.first.path.StartsLeft :=
      K3CoverSequence.startsLeft_of_left_positive_right_zero
        F.pair.first.path (by rw [h3.2.1]; omega) h3.1
    have hSecondLeft : F.pair.second.leftMoves = 0 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecondRight : F.pair.second.rightMoves = 2 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecond : F.pair.second.path.StartsRight :=
      K3CoverSequence.startsRight_of_left_zero_right_positive
        F.pair.second.path hSecondLeft (by rw [hSecondRight]; omega)
    exact ⟨.row3_BB_DD, h3, hFirst, hSecond⟩
  · dsimp only [Row4] at h4
    have hFirst : F.pair.first.path.StartsLeft :=
      K3CoverSequence.startsLeft_of_left_positive_right_zero
        F.pair.first.path (by rw [h4.2.1]; omega) h4.1
    have hM := F.M_le_secondRight
    have hBudget := F.pair.second.coverBudget
    have hSecondCases :
        (F.pair.second.leftMoves = 0 ∧ F.pair.second.rightMoves = 1) ∨
        (F.pair.second.leftMoves = 1 ∧ F.pair.second.rightMoves = 1) ∨
        (F.pair.second.leftMoves = 0 ∧ F.pair.second.rightMoves = 2) := by
      omega
    rcases hSecondCases with hSingle | hOneEach | hDouble
    · have hSecond : F.pair.second.path.StartsRight :=
        K3CoverSequence.startsRight_of_left_zero_right_positive
          F.pair.second.path hSingle.1 (by rw [hSingle.2]; omega)
      rcases F.second_rank_transition_of_positive (by
        rw [hSingle.1, hSingle.2]
        omega) with h32 | h31 | h21
      · exact ⟨.row4_D32, h4, hFirst, hSingle.1, hSingle.2, hSecond, h32⟩
      · exact ⟨.row4_D31, h4, hFirst, hSingle.1, hSingle.2, hSecond, h31⟩
      · exact ⟨.row4_D21, h4, hFirst, hSingle.1, hSingle.2, hSecond, h21⟩
    · rcases K3CoverSequence.startsLeft_or_startsRight_of_positive
        F.pair.second.path (by rw [hOneEach.1, hOneEach.2]; omega) with
        hLeft | hRight
      · exact ⟨.row4_CD, h4, hFirst, hOneEach.1, hOneEach.2, hLeft⟩
      · exact ⟨.row4_DC, h4, hFirst, hOneEach.1, hOneEach.2, hRight⟩
    · have hSecond : F.pair.second.path.StartsRight :=
        K3CoverSequence.startsRight_of_left_zero_right_positive
          F.pair.second.path hDouble.1 (by rw [hDouble.2]; omega)
      exact ⟨.row4_DD, h4, hFirst, hDouble.1, hDouble.2, hSecond⟩
  · dsimp only [Row5] at h5
    have hFirst : F.pair.first.path.StartsLeft :=
      K3CoverSequence.startsLeft_of_left_positive_right_zero
        F.pair.first.path (by rw [h5.2.1]; omega) h5.1
    have hSecondLeft : F.pair.second.leftMoves = 0 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecondRight : F.pair.second.rightMoves = 2 := by
      have hBudget := F.pair.second.coverBudget
      have hM := F.M_le_secondRight
      omega
    have hSecond : F.pair.second.path.StartsRight :=
      K3CoverSequence.startsRight_of_left_zero_right_positive
        F.pair.second.path hSecondLeft (by rw [hSecondRight]; omega)
    exact ⟨.row5_BB_DD, h5, hFirst, hSecond⟩

/-- The five-row arithmetic applies to every global frame: either the
short-arc inequality already holds or one of the five exceptional rows is
realized by the actual majorant counts. -/
theorem short_arc_or_exceptional_row
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    F.setup.yzSides ≤ 5 ∨
      IsExceptionalMajorantRow F.setup.first.leftMoves
        F.setup.first.rightMoves F.setup.L F.setup.M := by
  by_cases hShort : F.setup.yzSides ≤ 5
  · exact Or.inl hShort
  · exact Or.inr ((maximal_gap_five_row_enumeration F.setup).1 (by omega))

/-- The localized terminal endpoint turns the abstract signed quantity
`D.yzSides` into the actual counterclockwise offset span from the first
counterclockwise neighbor of `x` to its first clockwise neighbor. -/
theorem localized_offset_span_eq_yzSides
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    ((n - (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val : ℕ) : ℤ) -
        (firstNeighborGap P d₁ d₂ d₃ F.x : ℤ) =
      F.setup.yzSides := by
  let gx := firstNeighborGap P d₁ d₂ d₃ F.x
  let gt := firstNeighborGap P d₁ d₂ d₃ (cyclicAdvance F.x 3)
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val
  let b := F.pair.first.leftMoves
  let zoff := n - hx
  let uoff := 3 + gt
  let soff := zoff - b
  let umoff := uoff + F.M
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (F.highDegree F.x)
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ F.x := by
    have := F.highDegree F.x
    omega
  have htdeg : 0 < vertexDegree P d₁ d₂ d₃ (cyclicAdvance F.x 3) := by
    have := F.highDegree (cyclicAdvance F.x 3)
    omega
  have hhxpos : 0 < hx := by
    simpa [hx] using firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hbudget : gx + hx + 6 ≤ n := by
    simpa [gx, hx] using first_neighbor_gap_cw_budget (v := F.x)
      (F.highDegree F.x)
  have hgtgx : gt ≤ gx := by
    simpa [gt, gx] using F.maximalGap (cyclicAdvance F.x 3)
  have hb : b ≤ 2 := by
    have h := F.pair.first.coverBudget
    dsimp [b]
    omega
  have hM2 : F.M ≤ 2 := by
    calc
      F.M ≤ F.pair.second.rightMoves := F.M_le_secondRight
      _ ≤ F.pair.second.leftMoves + F.pair.second.rightMoves :=
        Nat.le_add_left _ _
      _ ≤ 2 := F.pair.second.coverBudget
  have hhxbn : hx + b < n := by omega
  have hsoffn : soff < n := by
    dsimp [soff, zoff]
    omega
  have humoffn : umoff < n := by
    dsimp [umoff, uoff]
    omega
  have hzIndex :
      firstClockwiseNeighbor P d₁ d₂ d₃ F.x = cyclicRetreat F.x hx := by
    rfl
  have hsIndex :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) b =
        cyclicAdvance F.x soff := by
    rw [hzIndex, cyclicRetreat_add,
      cyclicRetreat_eq_advance_complement F.x (by omega : 0 < hx + b) hhxbn]
    have hoff : n - (hx + b) = soff := by
      dsimp [soff, zoff]
      omega
    rw [hoff]
  have huIndex :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
        cyclicAdvance F.x uoff := by
    unfold firstCounterclockwiseNeighbor
    rw [cyclicAdvance_add]
  have huMIndex :
      cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3)) F.M =
        cyclicAdvance F.x umoff := by
    rw [huIndex, cyclicAdvance_add]
  have hOffsetLabel : cyclicAdvance F.x soff = cyclicAdvance F.x umoff := by
    rw [← hsIndex, ← huMIndex]
    exact F.outerLocalized
  have hFin : Fin.ofNat n soff = Fin.ofNat n umoff := by
    unfold cyclicAdvance at hOffsetLabel
    exact add_left_cancel hOffsetLabel
  have hoff : soff = umoff := by
    have hval := congrArg Fin.val hFin
    simpa [Fin.ofNat, Nat.mod_eq_of_lt hsoffn,
      Nat.mod_eq_of_lt humoffn] using hval
  have hbz : b ≤ zoff := by
    dsimp [zoff]
    omega
  have hoffAdd : zoff = uoff + F.M + b := by
    dsimp [soff, umoff] at hoff
    omega
  change (zoff : ℤ) - (gx : ℤ) =
    3 - ((gx - gt : ℕ) : ℤ) + (F.M : ℤ) + (b : ℤ)
  rw [hoffAdd, Nat.cast_sub hgtgx]
  push_cast
  dsimp [uoff]
  ring

/-- The direct branch of the ErLV assembly.  If the localized span between
the first counterclockwise and first clockwise neighbors is at most five
sides, the complete neighbor set of `x` has at most six vertices. -/
theorem degree_le_six_of_short_arc
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hShort : F.setup.yzSides ≤ 5) :
    vertexDegree P d₁ d₂ d₃ F.x ≤ 6 := by
  classical
  let gx := firstNeighborGap P d₁ d₂ d₃ F.x
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val
  let zoff := n - hx
  let g := firstNeighborOffset P d₁ d₂ d₃ F.x
  let N := ccwNeighborOffsets P d₁ d₂ d₃ F.x
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ F.x := by
    have := F.highDegree F.x
    omega
  have hhxpos : 0 < hx := by
    simpa [hx] using firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hbudget : gx + hx + 6 ≤ n := by
    simpa [gx, hx] using first_neighbor_gap_cw_budget (v := F.x)
      (F.highDegree F.x)
  have hzoffn : zoff < n := by
    dsimp [zoff]
    omega
  let upper : Fin n := ⟨zoff, hzoffn⟩
  have hccw := ccwNeighborOffsets_nonempty_of_degree_pos hxdeg
  have hNSub : N ⊆ Finset.Icc g upper := by
    intro k hk
    have hkUpperRaw := ccw_neighbor_offset_le_clockwise_boundary hxdeg hk
    have hkUpper : k.val ≤ zoff := by
      dsimp [hx, zoff]
      omega
    exact Finset.mem_Icc.mpr
      ⟨firstNeighborOffset_le_of_mem hccw hk, hkUpper⟩
  have hcard := Finset.card_le_card hNSub
  rw [Fin.card_Icc] at hcard
  have hgval : g.val = gx := rfl
  have hupperval : upper.val = zoff := rfl
  rw [hgval, hupperval] at hcard
  have hzg : gx ≤ zoff := by
    dsimp [zoff]
    omega
  have hspanEq : (zoff : ℤ) - (gx : ℤ) = F.setup.yzSides := by
    simpa [zoff, hx, gx] using F.localized_offset_span_eq_yzSides
  have hspanInt : ((zoff - gx : ℕ) : ℤ) ≤ 5 := by
    rw [Nat.cast_sub hzg, hspanEq]
    exact hShort
  have hspan : zoff - gx ≤ 5 := by
    exact_mod_cast hspanInt
  have hdegreeEq : N.card = vertexDegree P d₁ d₂ d₃ F.x := by
    simpa [N] using ccwNeighborOffsets_card_eq_vertexDegree P d₁ d₂ d₃ F.x
  rw [← hdegreeEq]
  omega

end ErLVGlobalFiveRowFrame

/-- Raw convex/top-three data in the high-degree contradiction branch
produces the complete localized maximal-gap frame. -/
theorem exists_erlv_global_five_row_frame
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v) :
    Nonempty (ErLVGlobalFiveRowFrame P d₁ d₂ d₃) := by
  obtain ⟨x, hMax⟩ := exists_maximal_firstNeighborGap P d₁ d₂ d₃
  obtain ⟨pair, M, hM, hOuter⟩ :=
    erlv_majorant_arc_nesting_complete_of_tail
      P d₁ d₂ d₃ hConvex hClasses hHigh x hMax
  exact ⟨{
    convex := hConvex
    classes := hClasses
    highDegree := hHigh
    x := x
    maximalGap := hMax
    pair := pair
    M := M
    M_le_secondRight := hM
    outerLocalized := hOuter }⟩

/-- Combined raw-data form of the maximal-gap choice, the two actual
majorants, their localization, and the five-row enumeration. -/
theorem exists_erlv_global_short_arc_or_exceptional_row
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v) :
    ∃ F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃,
      F.setup.yzSides ≤ 5 ∨
        IsExceptionalMajorantRow F.setup.first.leftMoves
          F.setup.first.rightMoves F.setup.L F.setup.M := by
  obtain ⟨F⟩ := exists_erlv_global_five_row_frame P d₁ d₂ d₃
    hConvex hClasses hHigh
  exact ⟨F, F.short_arc_or_exceptional_row⟩

/-- Once the direct short-arc branch is discharged, failure of the desired
degree bound produces an actual localized frame in one of the five rows. -/
theorem exists_erlv_global_exceptional_row_of_no_degree_six
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hNoLow : ¬∃ v, vertexDegree P d₁ d₂ d₃ v ≤ 6) :
    ∃ F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃,
      IsExceptionalMajorantRow F.setup.first.leftMoves
        F.setup.first.rightMoves F.setup.L F.setup.M := by
  have hHigh := all_degrees_at_least_seven_of_no_degree_six hNoLow
  obtain ⟨F⟩ := exists_erlv_global_five_row_frame P d₁ d₂ d₃
    hConvex hClasses hHigh
  refine ⟨F, ?_⟩
  rcases F.short_arc_or_exceptional_row with hShort | hRow
  · exact (hNoLow ⟨F.x, F.degree_le_six_of_short_arc hShort⟩).elim
  · exact hRow

/-- Canonical raw geometric meaning of a cover word: it is realized by an
actual localized maximal-gap frame with the row, endpoint order, and rank
data recorded by `RealizesCoverWord`. -/
def GeometricallyRealizesCoverWord
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (w : ExceptionalCoverWord) : Prop :=
  ∃ F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃, F.RealizesCoverWord w

/-- Raw convex/top-three data now supplies the complete direct-or-thirteen-
word reduction.  No route closure is assumed in this theorem. -/
theorem has_thirteen_word_reduction_of_convex_top_three
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃) :
    HasThirteenWordReduction (vertexDegree P d₁ d₂ d₃)
      (GeometricallyRealizesCoverWord P d₁ d₂ d₃) := by
  by_cases hLow : ∃ v, vertexDegree P d₁ d₂ d₃ v ≤ 6
  · exact Or.inl hLow
  · right
    obtain ⟨F, hRow⟩ :=
      exists_erlv_global_exceptional_row_of_no_degree_six
        P d₁ d₂ d₃ hConvex hClasses hLow
    obtain ⟨w, hw⟩ := F.exceptional_row_realizes_cover_word hRow
    exact ⟨w, F, hw⟩

/-- Exact remaining global component after the maximal-gap, five-row, and
thirteen-word reductions: prove each canonical geometric word closes by its
routed local kernel. -/
def GlobalThirteenWordClosureComplete : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    Nonempty (DraftWordClosureInterface (vertexDegree P d₁ d₂ d₃)
      (GeometricallyRealizesCoverWord P d₁ d₂ d₃))

/-- Once the route-specific geometric closure interface is constructed, the
new raw reduction is the final `HasConvexK3DraftReduction` adapter. -/
theorem convex_top_three_draft_reduction_complete_of_global_word_closure
    (hClosure : GlobalThirteenWordClosureComplete) :
    ConvexTopThreeDraftReductionComplete := by
  intro n _ P d₁ d₂ d₃ hConvex hClasses
  exact ⟨GeometricallyRealizesCoverWord P d₁ d₂ d₃,
    has_thirteen_word_reduction_of_convex_top_three
      P d₁ d₂ d₃ hConvex hClasses,
    hClosure P d₁ d₂ d₃⟩

/-- The same exact closure boundary implies the intended unconditional
degree-six statement through the existing thirteen-word assembly. -/
theorem convex_top_three_degree_six_of_global_word_closure
    (hClosure : GlobalThirteenWordClosureComplete) :
    ConvexTopThreeDegreeSixStatement :=
  convex_top_three_degree_six_of_reduction_complete
    (convex_top_three_draft_reduction_complete_of_global_word_closure hClosure)

end LeanPool.Erdos132ConvexK3
