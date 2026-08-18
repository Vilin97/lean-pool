/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.TerminalCage
import LeanPool.Erdos132ConvexK3.Majorants
import Lean.Elab.Tactic.Omega

/-!
# Thirteen-word assembly

This file kernelizes the exact Section 7 routing table, packages the concrete
local data consumed by its four closure theorems, and constructs every route
handler unconditionally.  The final section separately records the stronger
global reduction still needed to obtain the source-facing convex theorem.
-/

namespace LeanPool.Erdos132ConvexK3

/-- The five exceptional rows of draft table (3.5). -/
inductive ExceptionalRow where
  | row1
  | row2
  | row3
  | row4
  | row5
  deriving DecidableEq

instance : Fintype ExceptionalRow where
  elems := {.row1, .row2, .row3, .row4, .row5}
  complete := by
    intro row
    cases row <;> simp

/-- The thirteen and only thirteen row/cover words in draft Section 7. -/
inductive ExceptionalCoverWord where
  | row1_B32
  | row1_B31
  | row1_B21
  | row2_AB
  | row2_BA
  | row3_BB_DD
  | row4_D32
  | row4_D31
  | row4_D21
  | row4_CD
  | row4_DC
  | row4_DD
  | row5_BB_DD
  deriving DecidableEq

instance : Fintype ExceptionalCoverWord where
  elems := {
    .row1_B32, .row1_B31, .row1_B21, .row2_AB, .row2_BA, .row3_BB_DD,
    .row4_D32, .row4_D31, .row4_D21, .row4_CD, .row4_DC, .row4_DD, .row5_BB_DD
  }
  complete := by
    intro word
    cases word <;> simp

/-- The four local kernels named in the Section 7 destination column. -/
inductive WordClosureRoute where
  | fullTwoRung
  | antiSaturation
  | terminalCage
  | fourEdgeCage
  deriving DecidableEq

instance : Fintype WordClosureRoute where
  elems := {.fullTwoRung, .antiSaturation, .terminalCage, .fourEdgeCage}
  complete := by
    intro route
    cases route <;> simp

/-- Row projection for the thirteen-word audit. -/
def ExceptionalCoverWord.row : ExceptionalCoverWord → ExceptionalRow
  | .row1_B32 | .row1_B31 | .row1_B21 => .row1
  | .row2_AB | .row2_BA => .row2
  | .row3_BB_DD => .row3
  | .row4_D32 | .row4_D31 | .row4_D21 | .row4_CD | .row4_DC | .row4_DD => .row4
  | .row5_BB_DD => .row5

/-- Exact destination column of the draft Section 7 table. -/
def ExceptionalCoverWord.route : ExceptionalCoverWord → WordClosureRoute
  | .row1_B32 | .row4_D32 => .terminalCage
  | .row1_B31 | .row2_BA | .row4_D31 | .row4_DC => .antiSaturation
  | .row4_DD => .fourEdgeCage
  | .row1_B21 | .row2_AB | .row3_BB_DD | .row4_D21 | .row4_CD |
      .row5_BB_DD => .fullTwoRung

/-- Transparent finite check that the audit datatype has exactly 13 words. -/
theorem thirteen_word_count : Fintype.card ExceptionalCoverWord = 13 := by
  decide

/-- Kernel rendering of every row and destination in the Section 7 table. -/
theorem thirteen_word_route_table :
    ExceptionalCoverWord.row1_B32.row = .row1 ∧
    ExceptionalCoverWord.row1_B32.route = .terminalCage ∧
    ExceptionalCoverWord.row1_B31.row = .row1 ∧
    ExceptionalCoverWord.row1_B31.route = .antiSaturation ∧
    ExceptionalCoverWord.row1_B21.row = .row1 ∧
    ExceptionalCoverWord.row1_B21.route = .fullTwoRung ∧
    ExceptionalCoverWord.row2_AB.row = .row2 ∧
    ExceptionalCoverWord.row2_AB.route = .fullTwoRung ∧
    ExceptionalCoverWord.row2_BA.row = .row2 ∧
    ExceptionalCoverWord.row2_BA.route = .antiSaturation ∧
    ExceptionalCoverWord.row3_BB_DD.row = .row3 ∧
    ExceptionalCoverWord.row3_BB_DD.route = .fullTwoRung ∧
    ExceptionalCoverWord.row4_D32.row = .row4 ∧
    ExceptionalCoverWord.row4_D32.route = .terminalCage ∧
    ExceptionalCoverWord.row4_D31.row = .row4 ∧
    ExceptionalCoverWord.row4_D31.route = .antiSaturation ∧
    ExceptionalCoverWord.row4_D21.row = .row4 ∧
    ExceptionalCoverWord.row4_D21.route = .fullTwoRung ∧
    ExceptionalCoverWord.row4_CD.row = .row4 ∧
    ExceptionalCoverWord.row4_CD.route = .fullTwoRung ∧
    ExceptionalCoverWord.row4_DC.row = .row4 ∧
    ExceptionalCoverWord.row4_DC.route = .antiSaturation ∧
    ExceptionalCoverWord.row4_DD.row = .row4 ∧
    ExceptionalCoverWord.row4_DD.route = .fourEdgeCage ∧
    ExceptionalCoverWord.row5_BB_DD.row = .row5 ∧
    ExceptionalCoverWord.row5_BB_DD.route = .fullTwoRung := by
  decide

/-- Logical closure of the shared-tip `F_s=A/B/≤C` split after the
reflection and metric/sign sublemmas have discharged their branches. -/
theorem full_two_rung_shared_tip_degree_le_six
    {degree : ℕ} {F_s A B C : ℝ}
    (hSplit : F_s = A ∨ F_s = B ∨ F_s ≤ C)
    (hAImpossible : F_s = A → False)
    (hB : F_s = B → degree ≤ 6)
    (hLow : F_s ≤ C → degree ≤ 1) :
    degree ≤ 6 := by
  rcases hSplit with hA | hB' | hLow'
  · exact (hAImpossible hA).elim
  · exact hB hB'
  · exact (hLow hLow').trans (by omega)

/-- Concrete local data consumed by a full two-rung word closure. -/
structure FullTwoRungWordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  /-- Vertex whose degree the full two-rung route bounds. -/
  vertex : Fin n
  /-- Shared upper tip used by the two inserted rungs. -/
  sharedTip : Fin n
  topSplit :
    sqDist (P vertex) (P sharedTip) = d₁ ∨
      sqDist (P vertex) (P sharedTip) = d₂ ∨
        sqDist (P vertex) (P sharedTip) ≤ d₃
  diameterImpossible : sqDist (P vertex) (P sharedTip) = d₁ → False
  secondClassBound : sqDist (P vertex) (P sharedTip) = d₂ →
    vertexDegree P d₁ d₂ d₃ vertex ≤ 6
  lowerClassBound : sqDist (P vertex) (P sharedTip) ≤ d₃ →
    vertexDegree P d₁ d₂ d₃ vertex ≤ 1

/-- Concrete local data consumed by a one-penultimate anti-saturation word. -/
structure AntiSaturationWordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  /-- Vertex whose degree the anti-saturation route bounds. -/
  vertex : Fin n
  /-- Surviving shared tip after one penultimate rung is lost. -/
  sharedTip : Fin n
  topSplit :
    sqDist (P vertex) (P sharedTip) = d₁ ∨
      sqDist (P vertex) (P sharedTip) = d₂ ∨
        sqDist (P vertex) (P sharedTip) ≤ d₃
  diameterImpossible : sqDist (P vertex) (P sharedTip) = d₁ → False
  secondClassBound : sqDist (P vertex) (P sharedTip) = d₂ →
    vertexDegree P d₁ d₂ d₃ vertex ≤ 5
  lowerClassBound : sqDist (P vertex) (P sharedTip) ≤ d₃ →
    vertexDegree P d₁ d₂ d₃ vertex ≤ 1

/-- Concrete local arc counts and metric collapses for a terminal cage word. -/
structure TerminalCageWordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  /-- Vertex at the center of the terminal cage count. -/
  vertex : Fin n
  /-- Number of available neighbors on the left boundary arc. -/
  leftArc : ℕ
  /-- Number of available neighbors on the right boundary arc. -/
  rightArc : ℕ
  /-- Optional neighbor in the outer circle slot. -/
  outerSlot : ℕ
  degreePartition : vertexDegree P d₁ d₂ d₃ vertex ≤
    leftArc + rightArc + outerSlot + 1
  leftArcBound : leftArc ≤ 3
  rightArcBound : rightArc ≤ 2
  outerSlotBound : outerSlot ≤ 1
  longMetricCollapse : 2 * d₂ ≤ d₁ + d₃ → rightArc ≤ 1
  shortMetricCollapse : d₁ + d₃ < 2 * d₂ →
    outerSlot = 0 ∨ leftArc ≤ 2

/-- Long-regime package data for the two endpoints of a four-edge cage. -/
structure FourEdgeLongWordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  /-- First endpoint of the four-edge cage. -/
  firstVertex : Fin n
  /-- Second endpoint of the four-edge cage. -/
  secondVertex : Fin n
  /-- Left distance band at the first endpoint. -/
  firstLeft : CageDistanceBand
  /-- Right distance band at the first endpoint. -/
  firstRight : CageDistanceBand
  /-- Left distance band at the second endpoint. -/
  secondLeft : CageDistanceBand
  /-- Right distance band at the second endpoint. -/
  secondRight : CageDistanceBand
  firstPackage : vertexDegree P d₁ d₂ d₃ firstVertex ≤
    fourEdgeLongPackage firstLeft + fourEdgeLongPackage firstRight
  secondPackage : vertexDegree P d₁ d₂ d₃ secondVertex ≤
    fourEdgeLongPackage secondLeft + fourEdgeLongPackage secondRight
  uniqueDiameterPair : ¬(firstLeft = .d1 ∧ firstRight = .d1 ∧
    secondLeft = .d1 ∧ secondRight = .d1)

/-- Short-regime package data and occupied-circle exclusions for a
four-edge cage. -/
structure FourEdgeShortWordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  /-- First endpoint of the four-edge cage. -/
  firstVertex : Fin n
  /-- Second endpoint of the four-edge cage. -/
  secondVertex : Fin n
  /-- Left distance band at the first endpoint. -/
  firstLeft : CageDistanceBand
  /-- Right distance band at the first endpoint. -/
  firstRight : CageDistanceBand
  /-- Left distance band at the second endpoint. -/
  secondLeft : CageDistanceBand
  /-- Right distance band at the second endpoint. -/
  secondRight : CageDistanceBand
  firstPackage : vertexDegree P d₁ d₂ d₃ firstVertex ≤
    fourEdgeGeneralPackage firstLeft + fourEdgeGeneralPackage firstRight
  secondPackage : vertexDegree P d₁ d₂ d₃ secondVertex ≤
    fourEdgeGeneralPackage secondLeft + fourEdgeGeneralPackage secondRight
  firstD1D2Impossible : ¬(firstLeft = .d1 ∧ firstRight = .d2)
  firstD2D1Impossible : ¬(firstLeft = .d2 ∧ firstRight = .d1)
  secondD1D2Impossible : ¬(secondLeft = .d1 ∧ secondRight = .d2)
  secondD2D1Impossible : ¬(secondLeft = .d2 ∧ secondRight = .d1)
  uniqueDiameterPair : ¬(firstLeft = .d1 ∧ firstRight = .d1 ∧
    secondLeft = .d1 ∧ secondRight = .d1)

/-- Either metric package that closes a four-edge cage word. -/
inductive FourEdgeCageWordRealization
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) where
  | long (data : FourEdgeLongWordRealization P d₁ d₂ d₃)
  | short (data : FourEdgeShortWordRealization P d₁ d₂ d₃)

/-- Geometric realization evidence for a word is exactly the local data
consumed by the closure theorem selected in the Section 7 destination table. -/
def RealizesGeom
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (word : ExceptionalCoverWord) : Prop :=
  match word.route with
  | .fullTwoRung => Nonempty (FullTwoRungWordRealization P d₁ d₂ d₃)
  | .antiSaturation => Nonempty (AntiSaturationWordRealization P d₁ d₂ d₃)
  | .terminalCage => Nonempty (TerminalCageWordRealization P d₁ d₂ d₃)
  | .fourEdgeCage => Nonempty (FourEdgeCageWordRealization P d₁ d₂ d₃)

/-- Route-indexed local closure interface.  `Realizes w` supplies the local
geometric data for the corresponding exceptional word. -/
structure DraftWordClosureInterface
    {n : ℕ} (degree : Fin n → ℕ) (Realizes : ExceptionalCoverWord → Prop) where
  fullTwoRung : ∀ w, w.route = .fullTwoRung → Realizes w →
    ∃ v, degree v ≤ 6
  antiSaturation : ∀ w, w.route = .antiSaturation → Realizes w →
    ∃ v, degree v ≤ 5
  terminalCage : ∀ w, w.route = .terminalCage → Realizes w →
    ∃ v, degree v ≤ 6
  fourEdgeCage : ∀ w, w.route = .fourEdgeCage → Realizes w →
    ∃ v, degree v ≤ 6

private theorem exists_degree_le_six_of_min
    {n : ℕ} {degree : Fin n → ℕ} {firstVertex secondVertex : Fin n}
    (hMinimum : min (degree firstVertex) (degree secondVertex) ≤ 6) :
    ∃ v, degree v ≤ 6 := by
  by_cases hFirst : degree firstVertex ≤ degree secondVertex
  · exact ⟨firstVertex, by simpa [min_eq_left hFirst] using hMinimum⟩
  · have hSecond : degree secondVertex ≤ degree firstVertex := le_of_not_ge hFirst
    exact ⟨secondVertex, by simpa [min_eq_right hSecond] using hMinimum⟩

/-- All thirteen concrete word realizations close unconditionally by the
proved full-two-rung, anti-saturation, terminal-cage, and four-edge lemmas. -/
theorem concrete_word_closures
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) :
    DraftWordClosureInterface (vertexDegree P d₁ d₂ d₃)
      (RealizesGeom P d₁ d₂ d₃) := by
  constructor
  · intro word hRoute hRealizes
    simp only [RealizesGeom, hRoute] at hRealizes
    obtain ⟨data⟩ := hRealizes
    exact ⟨data.vertex, full_two_rung_shared_tip_degree_le_six
      data.topSplit data.diameterImpossible data.secondClassBound
        data.lowerClassBound⟩
  · intro word hRoute hRealizes
    simp only [RealizesGeom, hRoute] at hRealizes
    obtain ⟨data⟩ := hRealizes
    exact ⟨data.vertex, one_penultimate_shared_tip_degree_le_five
      data.topSplit data.diameterImpossible data.secondClassBound
        data.lowerClassBound⟩
  · intro word hRoute hRealizes
    simp only [RealizesGeom, hRoute] at hRealizes
    obtain ⟨data⟩ := hRealizes
    exact ⟨data.vertex, terminal_d2_cage_metric_split_degree_le_six
      data.degreePartition data.leftArcBound data.rightArcBound
        data.outerSlotBound data.longMetricCollapse data.shortMetricCollapse⟩
  · intro word hRoute hRealizes
    simp only [RealizesGeom, hRoute] at hRealizes
    obtain ⟨data⟩ := hRealizes
    cases data with
    | long data =>
        apply exists_degree_le_six_of_min
        exact four_edge_cage_long_min_degree_le_six
          data.firstPackage data.secondPackage data.uniqueDiameterPair
    | short data =>
        apply exists_degree_le_six_of_min
        exact four_edge_cage_short_min_degree_le_six
          data.firstPackage data.secondPackage data.firstD1D2Impossible
            data.firstD2D1Impossible data.secondD1D2Impossible
              data.secondD2D1Impossible data.uniqueDiameterPair

/-- Direct short-arc closure or one of the thirteen exceptional words. -/
def HasThirteenWordReduction
    {n : ℕ} (degree : Fin n → ℕ) (Realizes : ExceptionalCoverWord → Prop) : Prop :=
  (∃ v, degree v ≤ 6) ∨ ∃ w, Realizes w

/-- Exact thirteen-word logical assembly.  Every constructor is routed by
`ExceptionalCoverWord.route`, with anti-saturation's stronger bound weakened
from five to six only at the final interface. -/
theorem thirteen_word_assembly
    {n : ℕ} {degree : Fin n → ℕ} {Realizes : ExceptionalCoverWord → Prop}
    (hReduction : HasThirteenWordReduction degree Realizes)
    (hClosures : DraftWordClosureInterface degree Realizes) :
    ∃ v, degree v ≤ 6 := by
  rcases hReduction with hDirect | ⟨w, hw⟩
  · exact hDirect
  · cases hroute : w.route with
    | fullTwoRung => exact hClosures.fullTwoRung w hroute hw
    | antiSaturation =>
        obtain ⟨v, hv⟩ := hClosures.antiSaturation w hroute hw
        exact ⟨v, hv.trans (by omega)⟩
    | terminalCage => exact hClosures.terminalCage w hroute hw
    | fourEdgeCage => exact hClosures.fourEdgeCage w hroute hw

/-- The proof-producing reduction package still required for an arbitrary
convex configuration. -/
def HasConvexK3DraftReduction
    {n : ℕ} [_nonzero : NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) : Prop :=
  ∃ Realizes : ExceptionalCoverWord → Prop,
    HasThirteenWordReduction (vertexDegree P d₁ d₂ d₃) Realizes ∧
      Nonempty (DraftWordClosureInterface (vertexDegree P d₁ d₂ d₃) Realizes)

/-- Conditional final existential theorem: once the global reduction package
is constructed, the thirteen kernel routes produce a vertex of degree at
most six. -/
theorem convex_top_three_min_degree_le_six_of_draft_reduction
    {n : ℕ} [_nonzero : NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hReduction : HasConvexK3DraftReduction P d₁ d₂ d₃) :
    ∃ v, vertexDegree P d₁ d₂ d₃ v ≤ 6 := by
  obtain ⟨Realizes, hCases, ⟨hClosures⟩⟩ := hReduction
  exact thirteen_word_assembly hCases hClosures

/-- The intended unqualified convex theorem as a proposition. -/
def ConvexTopThreeDegreeSixStatement : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    CyclicStrictConvex P → HasTopThreeDistanceClasses P d₁ d₂ d₃ →
      ∃ v, vertexDegree P d₁ d₂ d₃ v ≤ 6

/-- Exact missing bridge from the two public hypotheses to the reduction.
Because `HasThirteenWordReduction` admits the target as its direct branch,
this interface is logically as strong as the desired conclusion.  It is
retained only as an explicit map from the proved closure machinery to the
open global reduction; challenge PR #341 records the clean full statement. -/
def ConvexTopThreeDraftReductionComplete : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    CyclicStrictConvex P → HasTopThreeDistanceClasses P d₁ d₂ d₃ →
      HasConvexK3DraftReduction P d₁ d₂ d₃

/-- If the named global bridge is supplied, the actual convex degree-six
statement follows with no further geometric or combinatorial assumptions. -/
theorem convex_top_three_degree_six_of_reduction_complete
    (hComplete : ConvexTopThreeDraftReductionComplete) :
    ConvexTopThreeDegreeSixStatement := by
  intro n _ P d₁ d₂ d₃ hConvex hClasses
  exact convex_top_three_min_degree_le_six_of_draft_reduction
    (hComplete P d₁ d₂ d₃ hConvex hClasses)

/-- Conditional entry point.  Its interface is logically as strong as the
conclusion; it is retained as an explicit map from the closure machinery to
the open reduction, whose full statement is challenge PR #341. -/
theorem convex_k3_degree_six_of_reduction
    (hComplete : ConvexTopThreeDraftReductionComplete) :
    ConvexTopThreeDegreeSixStatement :=
  convex_top_three_degree_six_of_reduction_complete hComplete

end LeanPool.Erdos132ConvexK3
