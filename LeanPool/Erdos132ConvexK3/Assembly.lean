/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.WordClosures
import Lean.Elab.Tactic.Omega

/-!
# Thirteen-word assembly

This file kernelizes the exact Section 7 routing table, assigns each word its
own raw geometric realization predicate, and constructs every route handler
from the corresponding geometric closure theorem.  The final section
separately records the stronger global reduction still needed to obtain the
source-facing convex theorem.
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

/-- Geometric realization evidence is word-specific raw polygon data. -/
def RealizesGeom
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (word : ExceptionalCoverWord) : Prop := match word with
  | .row1_B32 => Nonempty (Row1B32WordRealization P d₁ d₂ d₃)
  | .row1_B31 => Nonempty (Row1B31WordRealization P d₁ d₂ d₃)
  | .row1_B21 => Nonempty (Row1B21WordRealization P d₁ d₂ d₃)
  | .row2_AB => Nonempty (Row2ABWordRealization P d₁ d₂ d₃)
  | .row2_BA => Nonempty (Row2BAWordRealization P d₁ d₂ d₃)
  | .row3_BB_DD => Nonempty (Row3BBDDWordRealization P d₁ d₂ d₃)
  | .row4_D32 => Nonempty (Row4D32WordRealization P d₁ d₂ d₃)
  | .row4_D31 => Nonempty (Row4D31WordRealization P d₁ d₂ d₃)
  | .row4_D21 => Nonempty (Row4D21WordRealization P d₁ d₂ d₃)
  | .row4_CD => Nonempty (Row4CDWordRealization P d₁ d₂ d₃)
  | .row4_DC => Nonempty (Row4DCWordRealization P d₁ d₂ d₃)
  | .row4_DD => Nonempty (Row4DDWordRealization P d₁ d₂ d₃)
  | .row5_BB_DD => Nonempty (Row5BBDDWordRealization P d₁ d₂ d₃)

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

/-- All thirteen concrete word realizations close unconditionally by the
proved full-two-rung, anti-saturation, terminal-cage, and four-edge lemmas. -/
theorem concrete_word_closures
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) :
    DraftWordClosureInterface (vertexDegree P d₁ d₂ d₃)
      (RealizesGeom P d₁ d₂ d₃) := by
  constructor
  · intro word hRoute hRealizes
    cases word with
    | row1_B32 => simp [ExceptionalCoverWord.route] at hRoute
    | row1_B31 => simp [ExceptionalCoverWord.route] at hRoute
    | row1_B21 =>
        obtain ⟨data⟩ : Nonempty (Row1B21WordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row1_B21_realization_degree_le_six data⟩
    | row2_AB =>
        obtain ⟨data⟩ : Nonempty (Row2ABWordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row2_AB_realization_degree_le_six data⟩
    | row2_BA => simp [ExceptionalCoverWord.route] at hRoute
    | row3_BB_DD =>
        obtain ⟨data⟩ : Nonempty (Row3BBDDWordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row3_BB_DD_realization_degree_le_six data⟩
    | row4_D32 => simp [ExceptionalCoverWord.route] at hRoute
    | row4_D31 => simp [ExceptionalCoverWord.route] at hRoute
    | row4_D21 =>
        obtain ⟨data⟩ : Nonempty (Row4D21WordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row4_D21_realization_degree_le_six data⟩
    | row4_CD =>
        obtain ⟨data⟩ : Nonempty (Row4CDWordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row4_CD_realization_degree_le_six data⟩
    | row4_DC => simp [ExceptionalCoverWord.route] at hRoute
    | row4_DD => simp [ExceptionalCoverWord.route] at hRoute
    | row5_BB_DD =>
        obtain ⟨data⟩ : Nonempty (Row5BBDDWordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row5_BB_DD_realization_degree_le_six data⟩
  · intro word hRoute hRealizes
    cases word with
    | row1_B31 =>
        obtain ⟨data⟩ : Nonempty (Row1B31WordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row1_B31_realization_degree_le_five data⟩
    | row2_BA =>
        obtain ⟨data⟩ : Nonempty (Row2BAWordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row2_BA_realization_degree_le_five data⟩
    | row4_D31 =>
        obtain ⟨data⟩ : Nonempty (Row4D31WordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row4_D31_realization_degree_le_five data⟩
    | row4_DC =>
        obtain ⟨data⟩ : Nonempty (Row4DCWordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.geometry.vertex, row4_DC_realization_degree_le_five data⟩
    | row1_B32 | row1_B21 | row2_AB | row3_BB_DD | row4_D32 | row4_D21 |
        row4_CD | row4_DD | row5_BB_DD =>
        simp [ExceptionalCoverWord.route] at hRoute
  · intro word hRoute hRealizes
    cases word with
    | row1_B32 =>
        obtain ⟨data⟩ : Nonempty (Row1B32WordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.vertex, row1_B32_realization_degree_le_six data⟩
    | row4_D32 =>
        obtain ⟨data⟩ : Nonempty (Row4D32WordRealization P d₁ d₂ d₃) := hRealizes
        exact ⟨data.vertex, row4_D32_realization_degree_le_six data⟩
    | row1_B31 | row1_B21 | row2_AB | row2_BA | row3_BB_DD | row4_D31 |
        row4_D21 | row4_CD | row4_DC | row4_DD | row5_BB_DD =>
        simp [ExceptionalCoverWord.route] at hRoute
  · intro word hRoute hRealizes
    cases word with
    | row4_DD =>
        obtain ⟨data⟩ : Nonempty (Row4DDWordRealization P d₁ d₂ d₃) := hRealizes
        exact row4_DD_realization_degree_le_six data
    | row1_B32 | row1_B31 | row1_B21 | row2_AB | row2_BA | row3_BB_DD |
        row4_D32 | row4_D31 | row4_D21 | row4_CD | row4_DC | row5_BB_DD =>
        simp [ExceptionalCoverWord.route] at hRoute

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
