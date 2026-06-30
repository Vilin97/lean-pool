/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import LeanPool.FrontierMathOpenHypergraphs.Substitution

/-!
# The uniform 26/25 factor and the finite bootstrap
-/

namespace HypergraphLowerBound

/-! ## The sequence A_n -/

/-- A support gadget together with its stated capacity vector. -/
structure FrameSpec where
  /-- The capacity assigned to each part. -/
  parts : List ℕ
  /-- Raw support patterns, represented as lists of part indices. -/
  rawSupports : List (List ℕ)
  /-- The raw support patterns are valid subsets of the part indices of size at least two. -/
  rawSupports_ok :
    ∀ s ∈ rawSupports, s.Nodup ∧ (∀ i ∈ s, i < parts.length) ∧ 2 ≤ s.length

/-- The arity of a frame specification. -/
def FrameSpec.t (spec : FrameSpec) : ℕ :=
  spec.parts.length

/-- The capacity vector of a frame specification. -/
def FrameSpec.cap (spec : FrameSpec) : Fin spec.t → ℕ :=
  fun i => spec.parts.get i

private def supportPatternOfList {t : ℕ} (s : List ℕ)
    (hIn : ∀ i ∈ s, i < t) (hNodup : s.Nodup) (hCard : 2 ≤ s.length) :
    SupportPattern t := by
  let finList : List (Fin t) := s.pmap (fun i hi => (⟨i, hi⟩ : Fin t)) hIn
  have hFinNodup : finList.Nodup := by
    apply hNodup.pmap
    intro a ha b hb hEq
    simpa using congrArg Fin.val hEq
  refine ⟨finList.toFinset, ?_⟩
  rw [List.toFinset_card_of_nodup hFinNodup]
  simpa [finList] using hCard

/-- The support list of a frame specification, interpreted on `Fin spec.t`. -/
def FrameSpec.supportList (spec : FrameSpec) : List (SupportPattern spec.t) :=
  (spec.rawSupports.pmap (fun s hs =>
      supportPatternOfList s
        (fun i hi => (spec.rawSupports_ok s hs).2.1 i hi)
        (spec.rawSupports_ok s hs).1
        (spec.rawSupports_ok s hs).2.2)
    (by
      intro s hs
      exact hs) : List (SupportPattern spec.t))

/-- The support multiset of a frame specification, interpreted on `Fin spec.t`. -/
def FrameSpec.supports (spec : FrameSpec) : Multiset (SupportPattern spec.t) :=
  spec.supportList

/-- The total number of support occurrences in a frame specification. -/
def FrameSpec.bonus (spec : FrameSpec) : ℕ :=
  spec.rawSupports.length

/-- Decide whether a support pattern contributes to the frame inequality for `T` and `I`. -/
def frameWitnesses {t : ℕ} (T I : Finset (Fin t)) (S : SupportPattern t) : Bool :=
  decide (S.1 ⊆ T ∧ ((S.1 ∩ I).card = 1))

/-- The computable count of support occurrences contributing to the frame inequality. -/
def FrameSpec.countWitnesses (spec : FrameSpec)
    (T I : Finset (Fin spec.t)) : ℕ :=
  spec.supportList.countP (frameWitnesses T I)

/-- A frame specification is valid when its support multiset satisfies the corresponding
    frame inequalities. -/
def FrameSpec.IsValid (spec : FrameSpec) : Prop :=
  ∀ T I : Finset (Fin spec.t), I ⊆ T →
    spec.countWitnesses T I ≤ (T \ I).sum spec.cap

instance (spec : FrameSpec) : Decidable spec.IsValid := by
  unfold FrameSpec.IsValid FrameSpec.countWitnesses
  infer_instance

private def sup2 (a b : ℕ) : List ℕ := [a, b]
private def sup3 (a b c : ℕ) : List ℕ := [a, b, c]
private def sup4 (a b c d : ℕ) : List ℕ := [a, b, c, d]
private def sup5 (a b c d e : ℕ) : List ℕ := [a, b, c, d, e]
private def sup6 (a b c d e f : ℕ) : List ℕ := [a, b, c, d, e, f]
private def sup7 (a b c d e f g : ℕ) : List ℕ := [a, b, c, d, e, f, g]
private def sup8 (a b c d e f g h : ℕ) : List ℕ := [a, b, c, d, e, f, g, h]
private def sup9 (a b c d e f g h i : ℕ) : List ℕ := [a, b, c, d, e, f, g, h, i]

local notation "s2" => sup2
local notation "s3" => sup3
local notation "s4" => sup4
local notation "s5" => sup5
local notation "s6" => sup6
local notation "s7" => sup7
local notation "s8" => sup8
local notation "s9" => sup9

private def mkFrame (parts : List ℕ) (rawSupports : List (List ℕ))
    (h : ∀ s ∈ rawSupports, s.Nodup ∧ (∀ i ∈ s, i < parts.length) ∧ 2 ≤ s.length) :
    FrameSpec where
  parts := parts
  rawSupports := rawSupports
  rawSupports_ok := h

local notation "frame" => mkFrame
local syntax:max "frame!" term:max term:max : term
macro_rules
  | `(frame! $parts:term $supports:term) => `(mkFrame $parts $supports (by decide))

private inductive ChoiceKind where
  | base
  | bin
  | frame
  | quadres
  | quad4
  | boost15
  | boost16
  | boost17
  | boost19
  | boost31
  | boost32
  | boost33
deriving DecidableEq, Repr, Inhabited

private structure ChoiceSpec where
  kind : ChoiceKind
  parts : List ℕ
  bonus : ℕ
deriving Inhabited

private def core4Supports : List (List ℕ) :=
  [ s2 0 1
  , s2 0 2
  , s2 0 3
  , s2 1 2
  , s2 1 3
  , s2 2 3
  , s3 0 1 2
  , s3 0 1 3
  , s3 0 2 3
  , s3 1 2 3
  , s4 0 1 2 3
  , s4 0 1 2 3
  , s4 0 1 2 3
  ]

/-- The four-part core gadget used in the residue construction. -/
def core4Spec : FrameSpec :=
  frame [3, 3, 3, 3] core4Supports (by decide)

/-- The exact small frames listed in Appendix A. -/
def exactSmallFrames : List FrameSpec :=
[
  frame! [2, 2, 2] [
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 2
  ],
  frame! [4, 4, 6] [
    s2 0 1,
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2
  ],
  frame! [6, 6, 6] [
    s2 0 1,
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 2,
    s2 1 2,
    s2 1 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2
  ],
  frame! [2, 2, 2, 3] [
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [2, 2, 2, 4] [
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [4, 4, 6, 9] [
    s2 0 1,
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [6, 6, 6, 6] [
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 3,
    s2 0 3,
    s2 1 2,
    s2 1 2,
    s2 1 3,
    s2 1 3,
    s2 2 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [6, 6, 6, 7] [
    s2 0 1,
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 3,
    s2 1 2,
    s2 1 2,
    s2 1 3,
    s2 2 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [6, 6, 6, 8] [
    s2 0 1,
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 2,
    s2 1 2,
    s2 1 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [6, 6, 6, 9] [
    s2 0 1,
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 2,
    s2 1 2,
    s2 1 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [6, 6, 6, 10] [
    s2 0 1,
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 2,
    s2 1 2,
    s2 1 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [2, 2, 2, 3, 4] [
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 3,
    s3 0 1 4,
    s3 0 2 3,
    s3 0 2 4,
    s3 0 3 4,
    s3 1 2 3,
    s3 1 2 3,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [3, 4, 4, 4, 6] [
    s2 0 1,
    s2 0 2,
    s2 0 3,
    s2 1 2,
    s2 2 3,
    s2 2 3,
    s2 3 4,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 4,
    s3 0 2 4,
    s3 2 3 4,
    s3 2 3 4,
    s3 2 3 4,
    s4 0 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [4, 4, 4, 4, 4] [
    s2 0 1,
    s2 0 2,
    s2 0 3,
    s2 0 4,
    s2 1 2,
    s2 1 3,
    s2 1 4,
    s2 2 3,
    s2 2 4,
    s2 3 4,
    s3 1 2 3,
    s3 1 2 4,
    s3 1 3 4,
    s3 2 3 4,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [4, 4, 4, 4, 6] [
    s2 0 1,
    s2 0 2,
    s2 0 3,
    s2 0 3,
    s2 1 2,
    s2 1 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 4,
    s3 0 2 4,
    s3 0 3 4,
    s3 1 2 3,
    s3 1 2 4,
    s3 1 3 4,
    s3 2 3 4,
    s4 0 1 2 3,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [5, 6, 6, 6, 6] [
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 3,
    s2 0 4,
    s2 1 2,
    s2 1 2,
    s2 1 3,
    s2 2 3,
    s2 2 3,
    s2 2 4,
    s2 3 4,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 4,
    s3 0 2 4,
    s3 0 3 4,
    s3 1 3 4,
    s3 1 3 4,
    s3 2 3 4,
    s3 2 3 4,
    s3 2 3 4,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [6, 6, 6, 6, 6] [
    s2 0 1,
    s2 0 2,
    s2 0 3,
    s2 0 4,
    s2 0 4,
    s2 0 4,
    s2 1 2,
    s2 1 3,
    s2 1 4,
    s2 2 3,
    s2 2 4,
    s2 3 4,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s3 1 2 4,
    s3 1 2 4,
    s3 1 3 4,
    s3 1 3 4,
    s3 2 3 4,
    s3 2 3 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [6, 6, 6, 6, 10] [
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 3,
    s2 0 3,
    s2 1 2,
    s2 1 2,
    s2 1 3,
    s2 1 3,
    s2 2 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 1 4,
    s3 0 2 3,
    s3 0 2 4,
    s3 0 3 4,
    s3 1 2 3,
    s3 1 2 4,
    s3 1 2 4,
    s3 1 3 4,
    s3 2 3 4,
    s3 2 3 4,
    s4 0 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [6, 6, 6, 6, 11] [
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 3,
    s2 0 3,
    s2 1 2,
    s2 1 2,
    s2 1 3,
    s2 1 3,
    s2 2 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ],
  frame! [6, 6, 6, 6, 12] [
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 3,
    s2 0 3,
    s2 1 2,
    s2 1 2,
    s2 1 3,
    s2 1 3,
    s2 2 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4
  ],
  frame! [6, 6, 6, 6, 13] [
    s2 0 1,
    s2 0 1,
    s2 0 2,
    s2 0 2,
    s2 0 3,
    s2 0 3,
    s2 1 2,
    s2 1 2,
    s2 1 3,
    s2 1 3,
    s2 2 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 0 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s4 1 2 3 4,
    s5 0 1 2 3 4,
    s5 0 1 2 3 4
  ]
]

/-- The explicit boosters listed in Appendix B. -/
def boosters : List FrameSpec :=
[
  frame! [2, 2, 2, 2, 2, 2, 3] [
    s2 0 2,
    s2 0 4,
    s2 1 3,
    s2 1 5,
    s2 2 4,
    s2 3 5,
    s4 0 1 2 6,
    s4 0 1 3 4,
    s4 0 1 5 6,
    s4 0 2 3 5,
    s4 0 4 5 6,
    s4 1 2 3 6,
    s4 1 2 4 5,
    s4 2 3 4 6,
    s4 3 4 5 6,
    s5 0 1 3 4 6,
    s5 0 2 3 5 6,
    s5 1 2 4 5 6,
    s6 0 1 2 3 4 5,
    s6 0 1 2 3 4 5,
    s7 0 1 2 3 4 5 6,
    s7 0 1 2 3 4 5 6
  ],
  frame! [2, 2, 2, 2, 2, 2, 2, 2] [
    s2 0 4,
    s2 1 5,
    s2 2 6,
    s2 3 7,
    s3 0 1 6,
    s3 0 2 3,
    s3 0 5 7,
    s3 1 2 7,
    s3 1 3 4,
    s3 2 4 5,
    s3 3 5 6,
    s3 4 6 7,
    s5 0 1 2 3 5,
    s5 0 1 2 4 7,
    s5 0 1 3 6 7,
    s5 0 2 5 6 7,
    s5 0 3 4 5 6,
    s5 1 2 3 4 6,
    s5 1 4 5 6 7,
    s5 2 3 4 5 7,
    s6 0 1 2 4 5 6,
    s6 0 1 3 4 5 7,
    s6 0 2 3 4 6 7,
    s6 1 2 3 5 6 7,
    s8 0 1 2 3 4 5 6 7,
    s8 0 1 2 3 4 5 6 7
  ],
  frame! [2, 2, 2, 3, 4, 4] [
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 3,
    s3 0 1 4,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 5,
    s3 1 3 4,
    s3 1 4 5,
    s3 2 3 4,
    s3 3 4 5,
    s4 0 1 2 5,
    s4 0 1 3 5,
    s4 0 2 3 5,
    s4 0 2 4 5,
    s4 0 2 4 5,
    s6 0 1 2 3 4 5,
    s6 0 1 2 3 4 5,
    s6 0 1 2 3 4 5,
    s6 0 1 2 3 4 5,
    s6 0 1 2 3 4 5
  ],
  frame! [2, 2, 2, 3, 4, 6] [
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s2 3 4,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3,
    s4 0 1 2 4,
    s4 0 1 2 4,
    s4 0 1 3 4,
    s4 0 2 3 4,
    s4 0 3 4 5,
    s4 0 3 4 5,
    s4 0 3 4 5,
    s4 1 2 3 4,
    s5 0 1 2 3 5,
    s5 0 1 2 3 5,
    s5 0 1 2 3 5,
    s5 0 1 2 4 5,
    s5 0 1 2 4 5,
    s5 0 1 2 4 5,
    s5 1 2 3 4 5,
    s5 1 2 3 4 5,
    s5 1 2 3 4 5
  ],
  frame! [3, 4, 4, 4, 4, 4, 4, 4] [
    s2 1 2,
    s2 1 7,
    s2 2 3,
    s2 3 4,
    s2 4 5,
    s2 5 6,
    s2 6 7,
    s3 0 1 3,
    s3 0 1 4,
    s3 0 1 5,
    s3 0 1 6,
    s3 0 2 4,
    s3 0 2 5,
    s3 0 2 6,
    s3 0 2 7,
    s3 0 3 5,
    s3 0 3 6,
    s3 0 3 7,
    s3 0 4 6,
    s3 0 4 7,
    s3 0 5 7,
    s3 1 2 4,
    s3 1 3 7,
    s3 1 5 6,
    s3 2 3 5,
    s3 2 6 7,
    s3 3 4 6,
    s3 4 5 7,
    s5 1 2 3 5 6,
    s5 1 2 4 5 6,
    s5 1 2 4 5 7,
    s5 1 3 4 5 7,
    s5 1 3 4 6 7,
    s5 2 3 4 6 7,
    s5 2 3 5 6 7,
    s7 0 1 2 3 4 5 6,
    s7 0 1 2 3 4 5 6,
    s7 0 1 2 3 4 5 7,
    s7 0 1 2 3 4 5 7,
    s7 0 1 2 3 4 6 7,
    s7 0 1 2 3 4 6 7,
    s7 0 1 2 3 5 6 7,
    s7 0 1 2 3 5 6 7,
    s7 0 1 2 4 5 6 7,
    s7 0 1 2 4 5 6 7,
    s7 0 1 3 4 5 6 7,
    s7 0 1 3 4 5 6 7,
    s7 0 2 3 4 5 6 7,
    s7 0 2 3 4 5 6 7,
    s7 1 2 3 4 5 6 7
  ],
  frame! [4, 4, 4, 4, 4, 4, 4, 4] [
    s2 0 2,
    s2 0 4,
    s2 0 4,
    s2 0 6,
    s2 1 3,
    s2 1 5,
    s2 1 5,
    s2 1 7,
    s2 2 4,
    s2 2 6,
    s2 2 6,
    s2 3 5,
    s2 3 7,
    s2 3 7,
    s2 4 6,
    s2 5 7,
    s4 0 1 2 3,
    s4 0 1 2 7,
    s4 0 1 3 6,
    s4 0 1 4 5,
    s4 0 1 6 7,
    s4 0 2 3 5,
    s4 0 2 4 6,
    s4 0 2 4 6,
    s4 0 2 5 7,
    s4 0 3 4 7,
    s4 0 3 5 6,
    s4 0 5 6 7,
    s4 1 2 3 4,
    s4 1 2 4 7,
    s4 1 2 5 6,
    s4 1 3 4 6,
    s4 1 3 5 7,
    s4 1 3 5 7,
    s4 1 4 6 7,
    s4 2 3 4 5,
    s4 2 3 6 7,
    s4 2 4 5 7,
    s4 3 4 5 6,
    s4 4 5 6 7,
    s7 0 1 2 3 4 5 6,
    s7 0 1 2 3 4 5 7,
    s7 0 1 2 3 4 6 7,
    s7 0 1 2 3 5 6 7,
    s7 0 1 2 4 5 6 7,
    s7 0 1 3 4 5 6 7,
    s7 0 2 3 4 5 6 7,
    s7 1 2 3 4 5 6 7,
    s8 0 1 2 3 4 5 6 7,
    s8 0 1 2 3 4 5 6 7,
    s8 0 1 2 3 4 5 6 7,
    s8 0 1 2 3 4 5 6 7,
    s8 0 1 2 3 4 5 6 7
  ],
  frame! [1, 4, 4, 4, 4, 4, 4, 4, 4] [
    s2 1 5,
    s2 2 6,
    s2 3 7,
    s2 4 8,
    s3 0 1 3,
    s3 0 1 7,
    s3 0 2 4,
    s3 0 2 8,
    s3 0 3 5,
    s3 0 4 6,
    s3 0 5 7,
    s3 0 6 8,
    s4 0 1 3 6,
    s4 0 1 4 6,
    s4 0 1 4 7,
    s4 0 2 4 7,
    s4 0 2 5 7,
    s4 0 2 5 8,
    s4 0 3 5 8,
    s4 0 3 6 8,
    s4 1 2 3 4,
    s4 1 2 3 8,
    s4 1 2 4 5,
    s4 1 2 6 7,
    s4 1 2 7 8,
    s4 1 3 4 8,
    s4 1 3 5 7,
    s4 1 5 6 8,
    s4 1 6 7 8,
    s4 2 3 4 5,
    s4 2 3 5 6,
    s4 2 3 7 8,
    s4 2 4 6 8,
    s4 3 4 5 6,
    s4 3 4 6 7,
    s4 4 5 6 7,
    s4 4 5 7 8,
    s4 5 6 7 8,
    s5 0 1 2 5 6,
    s5 0 1 4 5 8,
    s5 0 2 3 6 7,
    s5 0 3 4 7 8,
    s8 0 1 2 3 4 5 6 7,
    s8 0 1 2 3 4 5 6 8,
    s8 0 1 2 3 4 5 7 8,
    s8 0 1 2 3 4 6 7 8,
    s8 0 1 2 3 5 6 7 8,
    s8 0 1 2 4 5 6 7 8,
    s8 0 1 3 4 5 6 7 8,
    s8 0 2 3 4 5 6 7 8,
    s8 1 2 3 4 5 6 7 8,
    s8 1 2 3 4 5 6 7 8,
    s8 1 2 3 4 5 6 7 8,
    s8 1 2 3 4 5 6 7 8,
    s9 0 1 2 3 4 5 6 7 8
  ]
]

/-- The residue gadgets `R_r` used by the balanced four-way construction. -/
def residueGadgets : List FrameSpec :=
[
  frame! [0, 0, 0, 0] [
  ],
  frame! [0, 0, 0, 1] [
  ],
  frame! [0, 0, 1, 1] [
    s2 2 3
  ],
  frame! [0, 1, 1, 1] [
    s3 1 2 3,
    s3 1 2 3
  ],
  frame! [1, 1, 1, 1] [
    s3 0 1 2,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3
  ],
  frame! [1, 1, 1, 2] [
    s3 0 1 2,
    s4 0 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [1, 1, 2, 2] [
    s2 0 1,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [1, 2, 2, 2] [
    s2 1 2,
    s2 1 3,
    s2 2 3,
    s3 0 1 2,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [2, 2, 2, 2] [
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 0 2 3,
    s3 1 2 3,
    s3 1 2 3
  ],
  frame! [2, 2, 2, 3] [
    s2 0 1,
    s2 0 2,
    s2 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [2, 2, 3, 3] [
    s2 0 1,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ],
  frame! [2, 3, 3, 3] [
    s2 1 2,
    s2 1 3,
    s2 2 3,
    s3 0 1 2,
    s3 0 1 2,
    s3 0 1 3,
    s3 0 2 3,
    s3 1 2 3,
    s4 0 1 2 3,
    s4 0 1 2 3
  ]
]

private def under60Choices : List ChoiceSpec :=
  [ { kind := .base, parts := [], bonus := 0 }
  , { kind := .bin, parts := [1, 1], bonus := 1 }
  , { kind := .bin, parts := [1, 2], bonus := 1 }
  , { kind := .bin, parts := [2, 2], bonus := 2 }
  , { kind := .bin, parts := [2, 3], bonus := 2 }
  , { kind := .frame, parts := [2, 2, 2], bonus := 5 }
  , { kind := .bin, parts := [3, 4], bonus := 3 }
  , { kind := .bin, parts := [4, 4], bonus := 4 }
  , { kind := .frame, parts := [2, 2, 2, 3], bonus := 9 }
  , { kind := .frame, parts := [2, 2, 2, 4], bonus := 10 }
  , { kind := .bin, parts := [5, 6], bonus := 5 }
  , { kind := .bin, parts := [6, 6], bonus := 6 }
  , { kind := .frame, parts := [2, 2, 2, 3, 4], bonus := 15 }
  , { kind := .frame, parts := [4, 4, 6], bonus := 11 }
  , { kind := .boost15, parts := [2, 2, 2, 2, 2, 2, 3], bonus := 22 }
  , { kind := .boost16, parts := [2, 2, 2, 2, 2, 2, 2, 2], bonus := 26 }
  , { kind := .boost17, parts := [2, 2, 2, 3, 4, 4], bonus := 22 }
  , { kind := .frame, parts := [6, 6, 6], bonus := 15 }
  , { kind := .boost19, parts := [2, 2, 2, 3, 4, 6], bonus := 24 }
  , { kind := .frame, parts := [4, 4, 4, 4, 4], bonus := 25 }
  , { kind := .frame, parts := [3, 4, 4, 4, 6], bonus := 25 }
  , { kind := .frame, parts := [4, 4, 4, 4, 6], bonus := 27 }
  , { kind := .frame, parts := [4, 4, 6, 9], bonus := 22 }
  , { kind := .frame, parts := [6, 6, 6, 6], bonus := 26 }
  , { kind := .frame, parts := [6, 6, 6, 7], bonus := 26 }
  , { kind := .frame, parts := [6, 6, 6, 8], bonus := 27 }
  , { kind := .frame, parts := [6, 6, 6, 9], bonus := 28 }
  , { kind := .frame, parts := [6, 6, 6, 10], bonus := 29 }
  , { kind := .frame, parts := [5, 6, 6, 6, 6], bonus := 35 }
  , { kind := .frame, parts := [6, 6, 6, 6, 6], bonus := 38 }
  , { kind := .boost31, parts := [3, 4, 4, 4, 4, 4, 4, 4], bonus := 50 }
  , { kind := .boost32, parts := [4, 4, 4, 4, 4, 4, 4, 4], bonus := 53 }
  , { kind := .boost33, parts := [1, 4, 4, 4, 4, 4, 4, 4, 4], bonus := 55 }
  , { kind := .frame, parts := [6, 6, 6, 6, 10], bonus := 42 }
  , { kind := .frame, parts := [6, 6, 6, 6, 11], bonus := 42 }
  , { kind := .frame, parts := [6, 6, 6, 6, 12], bonus := 44 }
  , { kind := .frame, parts := [6, 6, 6, 6, 13], bonus := 44 }
  , { kind := .quadres, parts := [9, 9, 10, 10], bonus := 40 }
  , { kind := .quadres, parts := [9, 10, 10, 10], bonus := 41 }
  , { kind := .quadres, parts := [10, 10, 10, 10], bonus := 43 }
  , { kind := .bin, parts := [20, 21], bonus := 20 }
  , { kind := .bin, parts := [21, 21], bonus := 21 }
  , { kind := .bin, parts := [21, 22], bonus := 21 }
  , { kind := .bin, parts := [22, 22], bonus := 22 }
  , { kind := .bin, parts := [22, 23], bonus := 22 }
  , { kind := .quadres, parts := [11, 11, 12, 12], bonus := 49 }
  , { kind := .bin, parts := [23, 24], bonus := 23 }
  , { kind := .bin, parts := [24, 24], bonus := 24 }
  , { kind := .quadres, parts := [12, 12, 12, 13], bonus := 52 }
  , { kind := .quadres, parts := [12, 12, 13, 13], bonus := 53 }
  , { kind := .quadres, parts := [12, 13, 13, 13], bonus := 54 }
  , { kind := .bin, parts := [26, 26], bonus := 26 }
  , { kind := .bin, parts := [26, 27], bonus := 26 }
  , { kind := .quadres, parts := [13, 13, 14, 14], bonus := 58 }
  , { kind := .bin, parts := [27, 28], bonus := 27 }
  , { kind := .bin, parts := [28, 28], bonus := 28 }
  , { kind := .quadres, parts := [14, 14, 14, 15], bonus := 61 }
  , { kind := .quadres, parts := [14, 14, 15, 15], bonus := 62 }
  , { kind := .bin, parts := [29, 30], bonus := 29 }
  ]

/-- The bonus terms e_r(m) for the balanced four-way construction. -/
def eBonus (r : ℕ) (m : ℕ) : ℕ :=
  match r % 4 with
  | 0 => (13 * m) / 3
  | 1 => (13 * m + 1) / 3
  | 2 => (13 * m + 5) / 3
  | _ => (13 * m + 6) / 3

/-- The bootstrap table values for A_n, 0 ≤ n < 60. -/
def bootstrapValues : List ℕ :=
  [0, 1, 3, 4, 6, 7, 10, 11, 14, 17,     -- 0-9
   19, 21, 24, 28, 30, 45, 50, 52, 57, 60, -- 10-19
   65, 68, 73, 75, 82, 84, 89, 93, 98, 101, -- 20-29
   108, 111, 117, 120, 125, 127, 134, 137, 140, 145, -- 30-39
   151, 153, 157, 162, 168, 170, 175, 180, 188, 191, -- 40-49
   195, 199, 204, 208, 214, 218, 224, 229, 234, 238] -- 50-59

/-- The sequence A(n) of vertex counts for the explicit hypergraph family. -/
def A (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n < 60 then
    bootstrapValues[n]!
  else
    let m := n / 4
    let r := n % 4
    match r with
    | 0 => A m + A m + A m + A m + eBonus 0 m
    | 1 => A m + A m + A m + A (m + 1) + eBonus 1 m
    | 2 => A m + A m + A (m + 1) + A (m + 1) + eBonus 2 m
    | _ => A m + A (m + 1) + A (m + 1) + A (m + 1) + eBonus 3 m
termination_by n
decreasing_by all_goals omega

local macro "eval_A_small" : tactic =>
  `(tactic| (
    first
    | rw [Fin.sum_univ_two]
    | rw [Fin.sum_univ_three]
    | rw [Fin.sum_univ_four]
    | skip
    try unfold A
    first | rfl | decide | omega))

local macro "eval_Ak_small" : tactic =>
  `(tactic| (unfold A; norm_num [bootstrapValues, k]))

private theorem Fin.sum_univ_five {α : Type*} [AddCommMonoid α] (f : Fin 5 → α) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem Fin.sum_univ_six {α : Type*} [AddCommMonoid α] (f : Fin 6 → α) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem Fin.sum_univ_seven {α : Type*} [AddCommMonoid α] (f : Fin 7 → α) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem Fin.sum_univ_nine {α : Type*} [AddCommMonoid α] (f : Fin 9 → α) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem sum_vec_22234 :
    ((Finset.univ : Finset (Fin 5)).sum (![2, 2, 2, 3, 4] : Fin 5 → ℕ)) = 13 := by
  decide

private theorem sum_vec_3335814 :
    ((Finset.univ : Finset (Fin 6)).sum (![3, 3, 3, 5, 8, 14] : Fin 6 → ℕ)) = 36 := by
  decide

private theorem sum_vec_588814 :
    ((Finset.univ : Finset (Fin 5)).sum (![5, 8, 8, 8, 14] : Fin 5 → ℕ)) = 43 := by
  decide

private theorem sum_vec_888814 :
    ((Finset.univ : Finset (Fin 5)).sum (![8, 8, 8, 8, 14] : Fin 5 → ℕ)) = 46 := by
  decide

private theorem sum_vec_14141420 :
    ((Finset.univ : Finset (Fin 4)).sum
      (![14, 14, 14, 20] : Fin 4 → ℕ)) = 62 := by
  decide

private theorem sum_vec_14141423 :
    ((Finset.univ : Finset (Fin 4)).sum
      (![14, 14, 14, 23] : Fin 4 → ℕ)) = 65 := by
  decide

private theorem sum_vec_14141427 :
    ((Finset.univ : Finset (Fin 4)).sum
      (![14, 14, 14, 27] : Fin 4 → ℕ)) = 69 := by
  decide

private theorem sum_vec_1014141414 :
    ((Finset.univ : Finset (Fin 5)).sum (![10, 14, 14, 14, 14] : Fin 5 → ℕ)) = 66 := by
  decide

private theorem sum_vec_58888888 :
    ((Finset.univ : Finset (Fin 8)).sum (![5, 8, 8, 8, 8, 8, 8, 8] : Fin 8 → ℕ)) = 61 := by
  decide

private theorem sum_vec_188888888 :
    ((Finset.univ : Finset (Fin 9)).sum (![1, 8, 8, 8, 8, 8, 8, 8, 8] : Fin 9 → ℕ)) = 65 := by
  decide

private theorem sum_vec_1414141427 :
    ((Finset.univ : Finset (Fin 5)).sum (![14, 14, 14, 14, 27] : Fin 5 → ℕ)) = 83 := by
  decide

private theorem sum_vec_1414141434 :
    ((Finset.univ : Finset (Fin 5)).sum (![14, 14, 14, 14, 34] : Fin 5 → ℕ)) = 90 := by
  decide

private theorem sum_vec_1414141437 :
    ((Finset.univ : Finset (Fin 5)).sum (![14, 14, 14, 14, 37] : Fin 5 → ℕ)) = 93 := by
  decide

private lemma card_filter_univ_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    ((Finset.univ : Finset (Fin n)).filter fun i => p (f i)).card =
      (List.ofFn f).countP p := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        ((Finset.univ : Finset (Fin (n + 1))).filter fun i => p (f i)).card
            = (if p (f 0) = true then 1 else 0) +
                ((Finset.univ : Finset (Fin n)).filter fun i => p (f i.succ)).card := by
                  simpa using
                    (Fin.card_filter_univ_succ'
                      (p := fun i : Fin (n + 1) => p (f i) = true))
        _ = (if p (f 0) = true then 1 else 0) +
              (List.ofFn fun i : Fin n => f i.succ).countP p := by
          rw [ih (fun i : Fin n => f i.succ)]
        _ = (List.ofFn f).countP p := by
          simp [List.ofFn_succ, List.countP_cons, Nat.add_comm]

private lemma card_filter_univ_get_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    ((Finset.univ : Finset (Fin l.length)).filter fun i => p (l.get i)).card = l.countP p := by
  simpa [List.ofFn_get] using card_filter_univ_ofFn l.get p

lemma card_filter_univ_get_eq_countP_prop {α : Type*} (l : List α)
    (p : α → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin l.length)).filter fun i => p (l.get i)).card =
      l.countP (fun a => decide (p a)) := by
  simpa using card_filter_univ_get_eq_countP l (fun a => decide (p a))

lemma card_filter_univ_multiset_toList_eq_countP_prop {α : Type*}
    (m : Multiset α) (p : α → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin m.card)).filter fun i =>
      p (m.toList.get ⟨i.1, by rw [Multiset.length_toList]; exact i.2⟩)).card =
        m.toList.countP (fun a => decide (p a)) := by
  have hcard :
      ((Finset.univ : Finset (Fin m.card)).filter fun i =>
        p (m.toList.get ⟨i.1, by rw [Multiset.length_toList]; exact i.2⟩)).card =
      ((Finset.univ : Finset (Fin m.toList.length)).filter fun i =>
        p (m.toList.get i)).card := by
    apply Finset.card_bij
      (fun i _ => (⟨i.1, by rw [Multiset.length_toList]; exact i.2⟩ :
        Fin m.toList.length))
    · intro i hi
      simpa using hi
    · intro i _ j _ hij
      apply Fin.ext
      exact congrArg (fun x : Fin m.toList.length => x.1) hij
    · intro j hj
      refine ⟨(⟨j.1, by rw [← Multiset.length_toList]; exact j.2⟩ : Fin m.card), ?_, ?_⟩
      · simpa using hj
      · rfl
  calc
    ((Finset.univ : Finset (Fin m.card)).filter fun i =>
      p (m.toList.get ⟨i.1, by rw [Multiset.length_toList]; exact i.2⟩)).card
        = ((Finset.univ : Finset (Fin m.toList.length)).filter fun i =>
            p (m.toList.get i)).card := hcard
    _ = m.toList.countP (fun a => decide (p a)) :=
      card_filter_univ_get_eq_countP_prop m.toList p

private lemma card_filter_univ_get_eq_countP_cast {α : Type*} (l : List α)
    {n : ℕ} (h : n = l.length) (p : α → Bool) :
    ((Finset.univ : Finset (Fin n)).filter fun i =>
      p (l.get ⟨i.1, by simpa [h] using i.2⟩)).card = l.countP p := by
  subst h
  simpa using card_filter_univ_get_eq_countP l p

lemma omegaCount_coe_eq_countP {t : ℕ} (l : List (SupportPattern t))
    (T I : Finset (Fin t)) :
    omegaCount (l : Multiset (SupportPattern t)) T I =
      l.countP (frameWitnesses T I) := by
  let m : Multiset (SupportPattern t) := l
  have hperm : List.Perm m.toList l := by
    simpa [m] using
      (Multiset.coe_eq_coe.mp (Multiset.coe_toList (l : Multiset (SupportPattern t))))
  calc
    omegaCount (l : Multiset (SupportPattern t)) T I =
        m.toList.countP
          (fun S : SupportPattern t => decide (S.1 ⊆ T ∧ ((S.1 ∩ I).card = 1))) := by
      unfold omegaCount supportSetAt
      unfold supportPatternAt
      change ((Finset.univ : Finset (Fin m.card)).filter fun i =>
        (m.toList.get ⟨i.1, by rw [Multiset.length_toList]; exact i.2⟩).1 ⊆ T ∧
          (((m.toList.get
            ⟨i.1, by rw [Multiset.length_toList]; exact i.2⟩).1 ∩ I).card = 1)).card =
        m.toList.countP
          (fun S : SupportPattern t => decide (S.1 ⊆ T ∧ ((S.1 ∩ I).card = 1)))
      exact card_filter_univ_multiset_toList_eq_countP_prop m
        (fun S : SupportPattern t => S.1 ⊆ T ∧ ((S.1 ∩ I).card = 1))
    _ = m.toList.countP (frameWitnesses T I) := by
      unfold frameWitnesses
      simp
    _ = l.countP (frameWitnesses T I) := hperm.countP_eq _

private lemma omegaCount_supportList_eq_countWitnesses (spec : FrameSpec)
    (T I : Finset (Fin spec.t)) :
    omegaCount spec.supports T I = spec.countWitnesses T I := by
  simpa [FrameSpec.supports, FrameSpec.countWitnesses] using
    (omegaCount_coe_eq_countP spec.supportList T I)

/-- The computable frame checker is equivalent to the abstract frame predicate. -/
theorem FrameSpec.isValid_iff_isFrame (spec : FrameSpec) :
    spec.IsValid ↔ IsFrame spec.supports spec.cap := by
  constructor
  · intro h T I hIT
    rw [omegaCount_supportList_eq_countWitnesses spec T I]
    exact h T I hIT
  · intro h T I hIT
    rw [← omegaCount_supportList_eq_countWitnesses spec T I]
    exact h T I hIT

private def rawInterCount (Imask : Nat) (s : List ℕ) : ℕ :=
  s.countP fun i => Imask.testBit i

private def rawWitnessAux (Tmask Imask : Nat) : Nat → List ℕ → Bool
  | acc, [] => decide (acc = 1)
  | acc, i :: s =>
      Tmask.testBit i &&
        rawWitnessAux Tmask Imask (acc + if Imask.testBit i then 1 else 0) s

private def rawWitness (Tmask Imask : Nat) (s : List ℕ) : Bool :=
  rawWitnessAux Tmask Imask 0 s

private def rawAttachedWitness (spec : FrameSpec) (Tmask Imask : Nat)
    (x : { s // s ∈ spec.rawSupports }) : Bool :=
  rawWitness Tmask Imask x.1

private theorem rawAttachedCount_eq_count (spec : FrameSpec) (Tmask Imask : Nat) :
    spec.rawSupports.attach.countP (rawAttachedWitness spec Tmask Imask) =
      spec.rawSupports.countP (rawWitness Tmask Imask) := by
  change spec.rawSupports.attach.countP
      (fun x : { s // s ∈ spec.rawSupports } => rawWitness Tmask Imask x.1) =
    spec.rawSupports.countP (rawWitness Tmask Imask)
  exact List.countP_attach (l := spec.rawSupports) (p := rawWitness Tmask Imask)

private def rawCapSum (spec : FrameSpec) (Tmask Imask : Nat) : ℕ :=
  (Finset.univ : Finset (Fin spec.t)).sum fun i =>
    if Tmask.testBit i.1 && !(Imask.testBit i.1) then spec.cap i else 0

/-- Recursively check all masks contributing to the raw frame inequalities. -/
def checkMasksDown (spec : FrameSpec) : Nat → Nat → Nat → Bool
  | 0, Tmask, Imask =>
      decide
        (spec.rawSupports.countP (rawWitness Tmask Imask) ≤
          rawCapSum spec Tmask Imask)
  | n + 1, Tmask, Imask =>
      let bit := (1 : Nat) <<< n
      checkMasksDown spec n Tmask Imask &&
      checkMasksDown spec n (Tmask ||| bit) Imask &&
      checkMasksDown spec n (Tmask ||| bit) (Imask ||| bit)

/-- A Boolean validator for the raw frame inequalities of a frame specification. -/
def FrameSpec.rawCheckValid (spec : FrameSpec) : Bool :=
  checkMasksDown spec spec.t 0 0

private theorem mem_supportPatternOfList_iff {t : ℕ} {s : List ℕ}
    {hIn : ∀ i ∈ s, i < t} {hNodup : s.Nodup} {hCard : 2 ≤ s.length} {i : Fin t} :
    i ∈ (supportPatternOfList s hIn hNodup hCard).1 ↔ i.1 ∈ s := by
  unfold supportPatternOfList
  constructor
  · intro hi
    rw [List.mem_toFinset, List.mem_pmap] at hi
    rcases hi with ⟨a, ha, hEq⟩
    have : a = i.1 := by
      simpa using congrArg Fin.val hEq
    simpa [this] using ha
  · intro hi
    rw [List.mem_toFinset, List.mem_pmap]
    refine ⟨i.1, hi, ?_⟩
    apply Fin.ext
    rfl

private theorem rawCapSum_eq_sum (spec : FrameSpec)
    (Tmask Imask : Nat) (T I : Finset (Fin spec.t))
    (hT : ∀ i : Fin spec.t, Tmask.testBit i.1 = decide (i ∈ T))
    (hI : ∀ i : Fin spec.t, Imask.testBit i.1 = decide (i ∈ I)) :
    rawCapSum spec Tmask Imask = (T \ I).sum spec.cap := by
  unfold rawCapSum
  have hfilter :
      ((Finset.univ : Finset (Fin spec.t)).filter fun i =>
          Tmask.testBit i.1 && !(Imask.testBit i.1)) = T \ I := by
    ext i
    simp [hT i, hI i]
  rw [← Finset.sum_filter]
  rw [hfilter]

private theorem rawInterCount_eq_interCard (spec : FrameSpec)
    (Imask : Nat) (I : Finset (Fin spec.t))
    (hI : ∀ i : Fin spec.t, Imask.testBit i.1 = decide (i ∈ I))
    (x : { s // s ∈ spec.rawSupports }) :
    rawInterCount Imask x.1 =
      (((supportPatternOfList x.1
          (fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi)
          (spec.rawSupports_ok x.1 x.2).1
          (spec.rawSupports_ok x.1 x.2).2.2).1 ∩ I).card) := by
  let hIn : ∀ i ∈ x.1, i < spec.t := fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi
  let hNodup : x.1.Nodup := (spec.rawSupports_ok x.1 x.2).1
  let hCard : 2 ≤ x.1.length := (spec.rawSupports_ok x.1 x.2).2.2
  let finList : List (Fin spec.t) :=
    x.1.pmap (fun i hi => (⟨i, hi⟩ : Fin spec.t)) hIn
  have hfinNodup : finList.Nodup := by
    apply hNodup.pmap
    intro a ha b hb hEq
    simpa using congrArg Fin.val hEq
  have hcount :
      rawInterCount Imask x.1 = finList.countP (fun j => decide (j ∈ I)) := by
    unfold rawInterCount finList
    rw [← List.countP_attach (l := x.1) (p := fun i => Imask.testBit i)]
    rw [List.countP_pmap]
    apply List.countP_congr
    intro y hy
    rcases y with ⟨a, ha⟩
    exact Bool.eq_iff_iff.mp (hI ⟨a, hIn a ha⟩)
  calc
    rawInterCount Imask x.1 = finList.countP (fun j => decide (j ∈ I)) := hcount
    _ = (finList.filter fun j => decide (j ∈ I)).length := by
      rw [List.countP_eq_length_filter]
    _ = ((finList.toFinset.filter fun j => decide (j ∈ I)).card) := by
      let filtered := finList.filter fun j => decide (j ∈ I)
      have hfilteredNodup : filtered.Nodup := hfinNodup.filter _
      have hfilteredCard : filtered.toFinset.card = filtered.length :=
        List.toFinset_card_of_nodup (l := filtered) hfilteredNodup
      simpa [filtered] using hfilteredCard.symm
    _ = (((supportPatternOfList x.1 hIn hNodup hCard).1 ∩ I).card) := by
      congr 1
      ext j
      simp [supportPatternOfList, finList]

private theorem rawAll_eq_decide_subset (spec : FrameSpec)
    (Tmask : Nat) (T : Finset (Fin spec.t))
    (hT : ∀ i : Fin spec.t, Tmask.testBit i.1 = decide (i ∈ T))
    (x : { s // s ∈ spec.rawSupports }) :
    x.1.all (fun i => Tmask.testBit i) =
      decide ((supportPatternOfList x.1
        (fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi)
        (spec.rawSupports_ok x.1 x.2).1
        (spec.rawSupports_ok x.1 x.2).2.2).1 ⊆ T) := by
  let hIn : ∀ i ∈ x.1, i < spec.t := fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi
  let hNodup : x.1.Nodup := (spec.rawSupports_ok x.1 x.2).1
  let hCard : 2 ≤ x.1.length := (spec.rawSupports_ok x.1 x.2).2.2
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro hAll i hi
    have hiList : i.1 ∈ x.1 :=
      (mem_supportPatternOfList_iff (hIn := hIn) (hNodup := hNodup) (hCard := hCard)).mp hi
    have hbit : Tmask.testBit i.1 = true := List.all_eq_true.mp hAll i.1 hiList
    let i' : Fin spec.t := ⟨i.1, by rw [FrameSpec.t]; exact i.2⟩
    have hbit' : Tmask.testBit i'.1 = true := by
      simpa [i'] using hbit
    have hmem : i' ∈ T := of_decide_eq_true <| by
      rw [← hT i']
      exact hbit'
    change i' ∈ T
    exact hmem
  · intro hSub
    refine List.all_eq_true.mpr ?_
    intro a ha
    let i : Fin spec.t := ⟨a, hIn a ha⟩
    have hi : i ∈ (supportPatternOfList x.1 hIn hNodup hCard).1 :=
      (mem_supportPatternOfList_iff (hIn := hIn) (hNodup := hNodup) (hCard := hCard)).mpr ha
    have hmem : i ∈ T := hSub hi
    have hmem' : decide (i ∈ T) = true := decide_eq_true hmem
    rw [hT i]
    exact hmem'

private theorem rawWitnessAux_eq (Tmask Imask : Nat) :
    ∀ acc s,
      rawWitnessAux Tmask Imask acc s =
        (s.all (fun i => Tmask.testBit i) &&
          decide (acc + rawInterCount Imask s = 1))
  | acc, [] => by
      rfl
  | acc, i :: s => by
      by_cases hI : Imask.testBit i
      · simp [rawWitnessAux, rawInterCount, rawWitnessAux_eq Tmask Imask (acc + 1) s, hI,
          Bool.and_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [rawWitnessAux, rawInterCount, rawWitnessAux_eq Tmask Imask acc s, hI,
          Bool.and_assoc]
        rfl

private theorem rawWitness_eq_all_and (Tmask Imask : Nat) (s : List ℕ) :
    rawWitness Tmask Imask s =
      (s.all (fun i => Tmask.testBit i) && decide (rawInterCount Imask s = 1)) := by
  simpa [rawWitness] using rawWitnessAux_eq Tmask Imask 0 s

private theorem frameWitness_eq_rawAttachedWitness (spec : FrameSpec)
    (Tmask Imask : Nat) (T I : Finset (Fin spec.t))
    (hT : ∀ i : Fin spec.t, Tmask.testBit i.1 = decide (i ∈ T))
    (hI : ∀ i : Fin spec.t, Imask.testBit i.1 = decide (i ∈ I))
    (x : { s // s ∈ spec.rawSupports }) :
    frameWitnesses T I
      (supportPatternOfList x.1
        (fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi)
        (spec.rawSupports_ok x.1 x.2).1
        (spec.rawSupports_ok x.1 x.2).2.2) =
      rawAttachedWitness spec Tmask Imask x := by
  let hIn : ∀ i ∈ x.1, i < spec.t := fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi
  let hNodup : x.1.Nodup := (spec.rawSupports_ok x.1 x.2).1
  let hCard : 2 ≤ x.1.length := (spec.rawSupports_ok x.1 x.2).2.2
  have hsub :
      x.1.all (fun i => Tmask.testBit i) =
        decide ((supportPatternOfList x.1 hIn hNodup hCard).1 ⊆ T) :=
    rawAll_eq_decide_subset spec Tmask T hT x
  have hpattern :
      supportPatternOfList x.1
          (fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi)
          (spec.rawSupports_ok x.1 x.2).1
          (spec.rawSupports_ok x.1 x.2).2.2 =
        supportPatternOfList x.1 hIn hNodup hCard := by
    apply Subtype.ext
    ext i
    constructor
    · intro hi
      exact (mem_supportPatternOfList_iff (hIn := hIn) (hNodup := hNodup)
        (hCard := hCard)).mpr
        ((mem_supportPatternOfList_iff
          (hIn := fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi)
          (hNodup := (spec.rawSupports_ok x.1 x.2).1)
          (hCard := (spec.rawSupports_ok x.1 x.2).2.2)).mp hi)
    · intro hi
      exact (mem_supportPatternOfList_iff
        (hIn := fun i hi => (spec.rawSupports_ok x.1 x.2).2.1 i hi)
        (hNodup := (spec.rawSupports_ok x.1 x.2).1)
        (hCard := (spec.rawSupports_ok x.1 x.2).2.2)).mpr
        ((mem_supportPatternOfList_iff (hIn := hIn) (hNodup := hNodup)
          (hCard := hCard)).mp hi)
  have hcard :
      decide (rawInterCount Imask x.1 = 1) =
        decide ((((supportPatternOfList x.1 hIn hNodup hCard).1 ∩ I).card) = 1) := by
    rw [rawInterCount_eq_interCard spec Imask I hI x]
    rw [hpattern]
    rfl
  unfold frameWitnesses rawAttachedWitness
  simp [rawWitness_eq_all_and, hsub, hcard]

private theorem countWitnesses_eq_rawAttachedCount (spec : FrameSpec)
    (Tmask Imask : Nat) (T I : Finset (Fin spec.t))
    (hT : ∀ i : Fin spec.t, Tmask.testBit i.1 = decide (i ∈ T))
    (hI : ∀ i : Fin spec.t, Imask.testBit i.1 = decide (i ∈ I)) :
    spec.countWitnesses T I =
      spec.rawSupports.attach.countP (rawAttachedWitness spec Tmask Imask) := by
  unfold FrameSpec.countWitnesses FrameSpec.supportList
  rw [List.countP_pmap]
  apply List.countP_congr
  intro x hx
  rcases x with ⟨a, m⟩
  constructor <;> intro h
  · have hEq :=
      frameWitness_eq_rawAttachedWitness spec Tmask Imask T I hT hI ⟨a, m⟩
    simpa [hEq] using h
  · have hEq :=
      frameWitness_eq_rawAttachedWitness spec Tmask Imask T I hT hI ⟨a, m⟩
    simpa [← hEq] using h

private theorem bit_testBit_lt {n i : Nat} (hi : i < n) :
    (((1 : Nat) <<< n).testBit i) = false := by
  simp [Nat.testBit_shiftLeft, Nat.not_le.mpr hi]

private theorem bit_testBit_self (n : Nat) :
    (((1 : Nat) <<< n).testBit n) = true := by
  simp [Nat.testBit_shiftLeft]

private theorem bit_testBit_gt {n i : Nat} (hi : n < i) :
    (((1 : Nat) <<< n).testBit i) = false := by
  have hne : i - n ≠ 0 := by omega
  have hbit : Nat.testBit 1 (i - n) = false := by
    by_cases htrue : Nat.testBit 1 (i - n) = true
    · exfalso
      exact hne ((Nat.testBit_one_eq_true_iff_self_eq_zero).mp htrue)
    · cases htest : Nat.testBit 1 (i - n) <;> simp_all
  rw [Nat.testBit_shiftLeft]
  simp [Nat.le_of_lt hi, hbit]

private theorem checkMasksDown_sound (spec : FrameSpec) :
    ∀ n Tmask Imask, n ≤ spec.t →
      (∀ i < n, Tmask.testBit i = false ∧ Imask.testBit i = false) →
      checkMasksDown spec n Tmask Imask = true →
      ∀ T I : Finset (Fin spec.t), I ⊆ T →
        (∀ i : Fin spec.t, n ≤ i.1 → Tmask.testBit i.1 = decide (i ∈ T)) →
        (∀ i : Fin spec.t, n ≤ i.1 → Imask.testBit i.1 = decide (i ∈ I)) →
        spec.countWitnesses T I ≤ (T \ I).sum spec.cap := by
  intro n
  induction n with
  | zero =>
      intro Tmask Imask hn hzero hcheck T I hIT hTrep hIrep
      have hleaf :
          spec.rawSupports.countP (rawWitness Tmask Imask) ≤
            rawCapSum spec Tmask Imask := by
        simpa [checkMasksDown] using hcheck
      have hleaf' :
          spec.rawSupports.attach.countP (rawAttachedWitness spec Tmask Imask) ≤
            rawCapSum spec Tmask Imask := by
        rw [rawAttachedCount_eq_count]
        exact hleaf
      have hTall : ∀ i : Fin spec.t, Tmask.testBit i.1 = decide (i ∈ T) := by
        intro i
        exact hTrep i (by omega)
      have hIall : ∀ i : Fin spec.t, Imask.testBit i.1 = decide (i ∈ I) := by
        intro i
        exact hIrep i (by omega)
      calc
        spec.countWitnesses T I =
            spec.rawSupports.attach.countP (rawAttachedWitness spec Tmask Imask) := by
              symm
              exact (countWitnesses_eq_rawAttachedCount spec Tmask Imask T I hTall hIall).symm
        _ ≤ rawCapSum spec Tmask Imask := hleaf'
        _ = (T \ I).sum spec.cap := rawCapSum_eq_sum spec Tmask Imask T I hTall hIall
  | succ n ih =>
      intro Tmask Imask hn hzero hcheck T I hIT hTrep hIrep
      let bit := (1 : Nat) <<< n
      have hcases :
          (checkMasksDown spec n Tmask Imask = true ∧
            checkMasksDown spec n (Tmask ||| bit) Imask = true) ∧
          checkMasksDown spec n (Tmask ||| bit) (Imask ||| bit) = true := by
        simpa [checkMasksDown, bit] using hcheck
      rcases hcases with ⟨⟨h0, h1⟩, h2⟩
      have hn' : n ≤ spec.t := Nat.le_of_succ_le hn
      let i0 : Fin spec.t := ⟨n, by omega⟩
      by_cases hTn : i0 ∈ T
      · by_cases hIn : i0 ∈ I
        · apply ih (Tmask ||| bit) (Imask ||| bit) hn'
          · intro i hi
            constructor
            · rw [Nat.testBit_lor,
                (hzero i (Nat.lt_trans hi (Nat.lt_succ_self n))).1, bit_testBit_lt hi]
              simp
            · rw [Nat.testBit_lor,
                (hzero i (Nat.lt_trans hi (Nat.lt_succ_self n))).2, bit_testBit_lt hi]
              simp
          · exact h2
          · exact hIT
          · intro j hj
            by_cases hEq : j.1 = n
            · have hj0 : j = i0 := by
                apply Fin.ext
                simpa using hEq
              subst hj0
              rw [Nat.testBit_lor, (hzero n (Nat.lt_succ_self n)).1, bit_testBit_self]
              simp [hTn]
            · have hgt : n < j.1 := by omega
              rw [Nat.testBit_lor, hTrep j (by omega), bit_testBit_gt hgt]
              simp
          · intro j hj
            by_cases hEq : j.1 = n
            · have hj0 : j = i0 := by
                apply Fin.ext
                simpa using hEq
              subst hj0
              rw [Nat.testBit_lor, (hzero n (Nat.lt_succ_self n)).2, bit_testBit_self]
              simp [hIn]
            · have hgt : n < j.1 := by omega
              rw [Nat.testBit_lor, hIrep j (by omega), bit_testBit_gt hgt]
              simp
        · apply ih (Tmask ||| bit) Imask hn'
          · intro i hi
            constructor
            · rw [Nat.testBit_lor,
                (hzero i (Nat.lt_trans hi (Nat.lt_succ_self n))).1, bit_testBit_lt hi]
              simp
            · exact (hzero i (Nat.lt_trans hi (Nat.lt_succ_self n))).2
          · exact h1
          · exact hIT
          · intro j hj
            by_cases hEq : j.1 = n
            · have hj0 : j = i0 := by
                apply Fin.ext
                simpa using hEq
              subst hj0
              rw [Nat.testBit_lor, (hzero n (Nat.lt_succ_self n)).1, bit_testBit_self]
              simp [hTn]
            · have hgt : n < j.1 := by omega
              rw [Nat.testBit_lor, hTrep j (by omega), bit_testBit_gt hgt]
              simp
          · intro j hj
            by_cases hEq : j.1 = n
            · have hj0 : j = i0 := by
                apply Fin.ext
                simpa using hEq
              subst hj0
              have hImask : Imask.testBit n = false := (hzero n (Nat.lt_succ_self n)).2
              rw [hImask]
              simp [hIn]
            · have hgt : n < j.1 := by omega
              exact hIrep j (by omega)
      · have hInot : i0 ∉ I := by
          intro hi
          exact hTn (hIT hi)
        apply ih Tmask Imask hn'
        · intro i hi
          exact hzero i (Nat.lt_trans hi (Nat.lt_succ_self n))
        · exact h0
        · exact hIT
        · intro j hj
          by_cases hEq : j.1 = n
          · have hj0 : j = i0 := by
              apply Fin.ext
              simpa using hEq
            subst hj0
            have hTmask : Tmask.testBit n = false := (hzero n (Nat.lt_succ_self n)).1
            rw [hTmask]
            simp [hTn]
          · exact hTrep j (by omega)
        · intro j hj
          by_cases hEq : j.1 = n
          · have hj0 : j = i0 := by
              apply Fin.ext
              simpa using hEq
            subst hj0
            have hImask : Imask.testBit n = false := (hzero n (Nat.lt_succ_self n)).2
            rw [hImask]
            simp [hInot]
          · exact hIrep j (by omega)

theorem FrameSpec.rawCheckValid_sound (spec : FrameSpec)
    (h : spec.rawCheckValid = true) : spec.IsValid := by
  intro T I hIT
  have hzero : ∀ i < spec.t, (0 : Nat).testBit i = false ∧ (0 : Nat).testBit i = false := by
    intro i hi
    simp
  have hTrep : ∀ i : Fin spec.t, spec.t ≤ i.1 → (0 : Nat).testBit i.1 = decide (i ∈ T) := by
    intro i hi
    exact (False.elim (Nat.not_le_of_lt i.2 hi))
  have hIrep : ∀ i : Fin spec.t, spec.t ≤ i.1 → (0 : Nat).testBit i.1 = decide (i ∈ I) := by
    intro i hi
    exact (False.elim (Nat.not_le_of_lt i.2 hi))
  exact checkMasksDown_sound spec spec.t 0 0 le_rfl hzero
    (by simpa [FrameSpec.rawCheckValid] using h) T I hIT hTrep hIrep

theorem checkMasksDown_step_true (spec : FrameSpec) (n Tmask Imask : Nat)
    (h0 : checkMasksDown spec n Tmask Imask = true)
    (h1 : checkMasksDown spec n (Tmask ||| ((1 : Nat) <<< n)) Imask = true)
    (h2 : checkMasksDown spec n (Tmask ||| ((1 : Nat) <<< n))
      (Imask ||| ((1 : Nat) <<< n)) = true) :
    checkMasksDown spec (n + 1) Tmask Imask = true := by
  simp [checkMasksDown, h0, h1, h2]

/-- A computable checker for the frame inequalities attached to a finite specification. -/
def FrameSpec.checkValid (spec : FrameSpec) : Bool :=
  decide spec.IsValid

private lemma all_checkValid_eq_true_iff (bank : List FrameSpec) :
    bank.all FrameSpec.checkValid = true ↔ ∀ spec ∈ bank, spec.IsValid := by
  induction bank with
  | nil =>
      simp
  | cons spec bank ih =>
      simp [FrameSpec.checkValid, ih]


end HypergraphLowerBound
