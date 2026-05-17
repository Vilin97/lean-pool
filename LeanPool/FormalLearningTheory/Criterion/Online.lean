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

/-- Count mistakes from an arbitrary online-learner state. -/
noncomputable def OnlineLearner.mistakesFrom {X : Type u} {Y : Type v} [DecidableEq Y]
    (L : OnlineLearner X Y) (state : L.State) (c : Concept X Y) : List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict state x ≠ c x then 1 else 0) +
      L.mistakesFrom (L.update state x (c x)) c xs

/-- Helper: run an online learner on a sequence, counting mistakes. -/
noncomputable def OnlineLearner.mistakes {X : Type u} {Y : Type v} [DecidableEq Y]
    (L : OnlineLearner X Y) (c : Concept X Y) (seq : List X) : ℕ :=
  L.mistakesFrom L.init c seq

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
  (seq.foldl
    (fun stateAndLoss sample =>
      let prediction := L.predict stateAndLoss.1 sample.1
      (L.update stateAndLoss.1 sample.1 sample.2,
        stateAndLoss.2 + loss prediction sample.2))
    (L.init, 0)).2

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
