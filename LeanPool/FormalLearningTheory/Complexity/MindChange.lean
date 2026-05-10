/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Data
import LeanPool.FormalLearningTheory.Learner.Core
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Mind Change Complexity (Gold Paradigm)

Counts how often a Gold learner changes its conjecture before converging.
-/

universe u v

/-- The data prefix: the first t examples from a data stream, as a list. -/
def DataStream.prefix {X : Type u} {Y : Type v} (T : DataStream X Y) (t : ℕ) : List (X × Y) :=
  (List.range t).map T.observe

/-- Mind change count: the number of times a Gold learner changes its conjecture.
    Counts time steps t where L's conjecture on the first t examples differs from
    its conjecture on the first t+1 examples.
    Note: parameter c (target concept) is not used in the definition  -  it is carried
    for the type-level specification (theorems bounding mind changes reference c). -/
noncomputable def MindChangeCount (X : Type u) (L : GoldLearner X Bool)
    (_c : Concept X Bool) (T : DataStream X Bool) : ℕ :=
  Set.ncard { t : ℕ | L.conjecture (T.prefix t) ≠ L.conjecture (T.prefix (t + 1)) }

open Classical in
/-- Mind change ordinal: ordinal-valued complexity measure encoding both convergence
    and correctness. Returns a finite ordinal (< ω) when the learner converges correctly
    to concept c with finitely many mind changes. Returns ω otherwise (non-convergent,
    or convergent to wrong concept). This encoding makes `MindChangeOrdinal < ω` equivalent
    to correct convergence with finite mind changes  -  the key property for the mind change
    characterization theorem.

    Design rationale: encoding correctness at the definition level makes the backward
    direction of mind_change_characterization provable  -  `MindChangeOrdinal < ω` directly
    entails both convergence and correctness without needing to extract them separately. -/
noncomputable def MindChangeOrdinal (X : Type u) (L : GoldLearner X Bool)
    (c : Concept X Bool) (T : DataStream X Bool) : Ordinal :=
  let changes := { t : ℕ | L.conjecture (T.prefix t) ≠ L.conjecture (T.prefix (t + 1)) }
  if h : changes.Finite then
    if ∃ t₀, ∀ t ≥ t₀, L.conjecture (T.prefix t) = c
    then (h.toFinset.card : Ordinal)
    else Ordinal.omega0
  else Ordinal.omega0

attribute [nolint unusedArguments] MindChangeCount
