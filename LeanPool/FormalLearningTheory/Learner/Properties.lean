/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Learner.Core

/-!
# Learner Properties

Properties that learners may satisfy: iterative, set-driven, consistent,
conservative, passive. These are `Prop` predicates, not separate types.
Also includes probabilistic and team learner variants.
-/

universe u v

/-!
## Learner Properties
-/

/-- An iterative learner depends only on its previous hypothesis and the new data point. -/
def IsIterative {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∃ step : Concept X Y → (X × Y) → Concept X Y,
    ∀ (data : List (X × Y)) (xy : X × Y),
      L.conjecture (data ++ [xy]) = step (L.conjecture data) xy

/-- A set-driven learner's output depends only on the SET of data, not the order. -/
def IsSetDriven {X : Type u} {Y : Type v} [DecidableEq X] [DecidableEq Y]
    (L : GoldLearner X Y) : Prop :=
  ∀ (data₁ data₂ : List (X × Y)),
    data₁.toFinset = data₂.toFinset → L.conjecture data₁ = L.conjecture data₂

/-- A consistent learner always outputs a hypothesis consistent with all data seen. -/
def IsConsistent {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∀ (data : List (X × Y)),
    ∀ p ∈ data, (L.conjecture data) p.1 = p.2

/-- A conservative learner only changes its hypothesis when forced by inconsistency. -/
def IsConservative {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∀ (data : List (X × Y)) (xy : X × Y),
    (L.conjecture data) xy.1 = xy.2 →
      L.conjecture (data ++ [xy]) = L.conjecture data

/-- A probabilistic learner uses randomness. -/
structure ProbabilisticLearner (X : Type u) (Y : Type v) where
  /-- The hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Randomized learning: seed → sample → hypothesis -/
  learn : {m : ℕ} → ℕ → (Fin m → X × Y) → Concept X Y

/-- A team learner: multiple learners, at least one of which identifies the target. -/
structure TeamLearner (X : Type u) (Y : Type v) (n : ℕ) where
  /-- The team members -/
  team : Fin n → GoldLearner X Y

/-! ## MeasurableBatchLearner API -/

/-- Fixed-sample measurability: for fixed training data S,
    L.learn S is a measurable function X → Bool.
    This is the most commonly used consequence of MeasurableBatchLearner. -/
theorem MeasurableBatchLearner.learn_measurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [h : MeasurableBatchLearner X L]
    {m : ℕ} (S : Fin m → X × Bool) :
    Measurable (L.learn S) :=
  (h.eval_measurable m).comp (Measurable.prodMk measurable_const measurable_id)
