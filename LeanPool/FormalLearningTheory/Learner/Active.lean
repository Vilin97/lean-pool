/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Learner.Core

/-!
# Active Learning, Teachers, and Meta-Learning

Active learners query oracles. Teachers present data strategically.
Meta-learners learn to learn. Also includes synthesizers and verifiers
for the CEGIS paradigm.
-/

universe u v

/-!
## Active Learner (Query Learning)
-/

/-- An active learner can query oracles (membership, equivalence). -/
structure ActiveLearner (X : Type u) (Y : Type v) where
  /-- The hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Learning with membership oracle: produce a hypothesis -/
  learnMQ : MembershipOracle X Y → Concept X Y
  /-- Output is in hypothesis space -/
  output_in_H_MQ : ∀ (mq : MembershipOracle X Y), learnMQ mq ∈ hypotheses

/-- A passive learner receives data without querying. -/
def IsPassive {X : Type u} {Y : Type v} (L : BatchLearner X Y) : Prop := L = L

/-- A learner augmented with advice. -/
structure LearnerWithAdvice (X : Type u) (Y : Type v) (A : Type*) where
  /-- Base learner -/
  base : BatchLearner X Y
  /-- Advice-augmented learning: advice → sample → hypothesis -/
  learnWithAdvice : A → {m : ℕ} → (Fin m → X × Y) → Concept X Y

/-!
## Teachers
-/

/-- A teacher presents examples to a learner according to some strategy. -/
structure Teacher (X : Type u) (Y : Type v) where
  /-- The concept the teacher is teaching -/
  target : Concept X Y
  /-- Teaching strategy: choose next example given what's been shown -/
  teach : List (X × Y) → X × Y

/-- Generate the teaching sequence: the teacher's strategy iterated. -/
def Teacher.teachingSequence {X : Type u} {Y : Type v}
    (T : Teacher X Y) : ℕ → List (X × Y)
  | 0 => []
  | n + 1 => let prev := T.teachingSequence n; prev ++ [T.teach prev]

/-- An optimal teacher minimizes the number of examples needed to
    uniquely identify the target within concept class C. Formally:
    the teaching sequence distinguishes T.target from all other c ∈ C
    in at most k steps, and no teacher for the same target does it in fewer. -/
def IsOptimalTeacher {X : Type u} {Y : Type v} (T : Teacher X Y)
    (C : ConceptClass X Y) : Prop :=
  T.target ∈ C ∧
  ∃ (k : ℕ),
    -- T's teaching sequence of length k uniquely identifies the target in C
    (∀ c ∈ C, c ≠ T.target →
      ∃ p ∈ T.teachingSequence k, c p.1 ≠ T.target p.1) ∧
    -- k is minimal: no teacher for the same target identifies it in fewer steps
    (∀ (T' : Teacher X Y), T'.target = T.target →
      (∀ c ∈ C, c ≠ T'.target →
        ∃ p ∈ T'.teachingSequence k, c p.1 ≠ T'.target p.1) →
      ∀ (k' : ℕ), k' < k →
        ∃ c ∈ C, c ≠ T'.target ∧
          ∀ p ∈ T'.teachingSequence k', c p.1 = T'.target p.1)

/-- An adversarial teacher chooses examples that maximize learner error.
    For every learner state (represented by what the learner has seen so far),
    the teacher picks the example that is hardest for ANY learner to use. -/
def IsAdversarial {X : Type u} {Y : Type v} (T : Teacher X Y)
    (C : ConceptClass X Y) : Prop :=
  T.target ∈ C ∧
  -- The teaching strategy maximizes the number of concepts in C
  -- consistent with data shown so far (maximally ambiguous examples)
  ∀ (data : List (X × Y)),
    ∀ (x' : X) (y' : Y),
      (Set.ncard { c ∈ C | ∀ p ∈ data ++ [T.teach data], c p.1 = p.2 }
        ≥ Set.ncard { c ∈ C | ∀ p ∈ data ++ [(x', y')], c p.1 = p.2 })

/-- A random teacher draws examples uniformly: the teaching strategy
    does not depend on what data has been shown so far. -/
def IsRandomTeacher {X : Type u} {Y : Type v} (T : Teacher X Y) : Prop :=
  -- Teaching strategy is history-independent: the choice at step n+1
  -- does not depend on the examples shown at steps 1..n
  ∀ (data₁ data₂ : List (X × Y)), T.teach data₁ = T.teach data₂

/-- Minimally adequate teacher: provides membership queries and equivalence queries.
    Interface for Angluin's L* algorithm. -/
structure MinimallyAdequateTeacher (X : Type u) (Y : Type v) where
  /-- Membership oracle -/
  mq : MembershipOracle X Y
  /-- Equivalence oracle -/
  eq : EquivalenceOracle X Y
  /-- Both answer about the same target -/
  consistent : mq.target = eq.target

/-!
## Meta-Learner
-/

/-- A meta-learner: a learner that takes a concept class and produces
    a learner specialized for that class (learning-to-learn). -/
structure MetaLearner (X : Type u) (Y : Type v) where
  /-- Given a concept class, produce a learner for that class -/
  metaLearn : ConceptClass X Y → BatchLearner X Y

/-- LLM critic: a teacher that uses a language model as its strategy. -/
structure LLMCritic (X : Type u) (Y : Type v) extends Teacher X Y where
  /-- Critique quality score -/
  critiqueQuality : ℝ

/-- A synthesizer: produces candidate concepts from specifications. -/
def Synthesizer (X : Type u) (Y : Type v) := List (X × Y) → Concept X Y

/-- A verifier: checks whether a candidate concept satisfies a specification. -/
def Verifier (X : Type u) (Y : Type v) (spec : Concept X Y) :=
  fun (candidate : Concept X Y) => Option { x : X // candidate x ≠ spec x }
