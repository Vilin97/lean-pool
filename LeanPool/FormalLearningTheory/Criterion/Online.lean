/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Learner.Core

/-!
# Online Learning Criteria

Mistake-bounded learning, online learnability, and regret bounds.
Characterized by Littlestone dimension.
-/

universe u v

/-- Helper: run an online learner on a sequence, counting mistakes. -/
noncomputable def OnlineLearner.mistakes {X : Type u} {Y : Type v} [DecidableEq Y]
    (L : OnlineLearner X Y) (c : Concept X Y) (seq : List X) : ℕ :=
  let rec go (state : L.State) (remaining : List X) (count : ℕ) : ℕ :=
    match remaining with
    | [] => count
    | x :: xs =>
      let pred := L.predict state x
      let newState := L.update state x (c x)
      go newState xs (if pred ≠ c x then count + 1 else count)
  go L.init seq 0

/-- Mistake-bounded learning: the learner makes at most M mistakes on ANY sequence.
    No distribution assumption. Characterized by Littlestone dimension. -/
def MistakeBounded (X : Type u) (Y : Type v) [DecidableEq Y]
    (C : ConceptClass X Y) (M : ℕ) : Prop :=
  ∃ (L : OnlineLearner X Y),
    ∀ (c : Concept X Y), c ∈ C →
      ∀ (seq : List X), L.mistakes c seq ≤ M

/-- Online learnable: there exists a finite mistake bound. -/
def OnlineLearnable (X : Type u) (Y : Type v) [DecidableEq Y] (C : ConceptClass X Y) : Prop :=
  ∃ (M : ℕ), MistakeBounded X Y C M

/-- Helper: cumulative loss of an online learner on a sequence. -/
noncomputable def OnlineLearner.cumulativeLoss {X : Type u} {Y : Type v}
    (L : OnlineLearner X Y) (loss : LossFunction Y) (seq : List (X × Y)) : ℝ :=
  let rec go (state : L.State) (remaining : List (X × Y)) (acc : ℝ) : ℝ :=
    match remaining with
    | [] => acc
    | (x, y) :: rest =>
      let pred := L.predict state x
      let newState := L.update state x y
      go newState rest (acc + loss pred y)
  go L.init seq 0

/-- Helper: cumulative loss of a fixed hypothesis on a sequence. -/
noncomputable def fixedHypothesisLoss {X : Type u} {Y : Type v}
    (h : Concept X Y) (loss : LossFunction Y) (seq : List (X × Y)) : ℝ :=
  seq.foldl (fun acc p => acc + loss (h p.1) p.2) 0

/-- Regret-bounded learning: the learner's cumulative loss is close to the
    best hypothesis in hindsight. No distributional assumptions. -/
def RegretBounded (X : Type u) (Y : Type v)
    (H : HypothesisSpace X Y) (loss : LossFunction Y) (bound : ℕ → ℝ) : Prop :=
  ∃ (L : OnlineLearner X Y),
    ∀ (seq : List (X × Y)),
      ∀ (h : Concept X Y), h ∈ H →
        L.cumulativeLoss loss seq - fixedHypothesisLoss h loss seq ≤ bound seq.length

attribute [nolint docBlame]
  OnlineLearner.mistakes.go
  OnlineLearner.cumulativeLoss.go
