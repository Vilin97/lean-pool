/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Data
import LeanPool.FormalLearningTheory.Computation

/-!
# Core Learner Types

The three paradigm-specific learner types with incompatible signatures.
There is no common parent type; the type system cannot express "learner"
without choosing a paradigm, because the three signatures are fundamentally
different:

- **PAC learner**: `{m : ℕ} → (Fin m → X × Y) → Concept X Y` (batch)
- **Online learner**: `State → X → Y` (sequential with internal state)
- **Gold learner**: `List (X × Y) → Concept X Y` (sequential, extensible)

This is intentional: a common parent would erase the structural properties
that make each paradigm's theorems non-trivial.
-/

universe u v

/-- A batch learner (PAC paradigm): takes a finite sample, returns a hypothesis. -/
structure BatchLearner (X : Type u) (Y : Type v) where
  /-- The learner's hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- The learning algorithm: given a sample, produce a hypothesis -/
  learn : {m : ℕ} → (Fin m → X × Y) → Concept X Y
  /-- Output is in the hypothesis space -/
  output_in_H : ∀ {m : ℕ} (S : Fin m → X × Y), learn S ∈ hypotheses

/-- An online learner: receives instances one at a time, makes predictions sequentially. -/
structure OnlineLearner (X : Type u) (Y : Type v) where
  /-- Internal state type -/
  State : Type
  /-- Initial state -/
  init : State
  /-- Predict: given current state and new instance, output a prediction -/
  predict : State → X → Y
  /-- Update: given current state, instance, and revealed true label, update state -/
  update : State → X → Y → State

/-- A Gold-style learner (identification in the limit): receives a stream of data
    and at each step conjectures a hypothesis. -/
structure GoldLearner (X : Type u) (Y : Type v) where
  /-- The learner's conjecture given data seen so far -/
  conjecture : List (X × Y) → Concept X Y

/-! ## Measurability Typeclasses

Regularity conditions for measure-theoretic PAC arguments. These replace
ad hoc predicates (`LearnEvalMeasurable`, `AdviceEvalMeasurable`) and
explicit hypothesis threading (`hmeas_C`, `hc_meas`, `hWB`).

The conditions identified here are the minimal requirements for:
- PAC success events to be MeasurableSet
- Section measure arguments (measurable_measure_prod_mk_left)
- PAC-Bayes bounds to be well-defined
- Information-theoretic generalization bounds (mutual information) to be statable

Reference: Krapp & Wirth, "Measurability in the Fundamental Theorem of
Statistical Learning", arXiv:2410.10243, 2024. -/

/-- A batch learner whose evaluation map is jointly measurable.

    The condition: for each sample size m, the map
      (S, x) ↦ L.learn S x
    from (Fin m → X × Bool) × X to Bool is Measurable.

    This is the minimal regularity that makes the PAC success event
      {S | D{x | L.learn(S)(x) ≠ c(x)} ≤ ε}
    a MeasurableSet (via measurable_measure_prod_mk_left).

    Equivalent to `LearnEvalMeasurable` (Separation.lean) and
    `AdviceEvalMeasurable` (Extended.lean) for the non-advice case. -/
class MeasurableBatchLearner (X : Type u) [MeasurableSpace X]
    (L : BatchLearner X Bool) : Prop where
  /-- Joint measurability of the evaluation map -/
  eval_measurable : ∀ (m : ℕ),
    Measurable (fun p : (Fin m → X × Bool) × X => L.learn p.1 p.2)
