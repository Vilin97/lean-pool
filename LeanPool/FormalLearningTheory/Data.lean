/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Data Presentations

The interfaces through which learners receive data. The three main paradigms
(PAC, Online, Gold) present data in fundamentally different ways:
- PAC: i.i.d. sample from a distribution (IIDSample)
- Gold: infinite stream enumerating the concept (DataStream, TextPresentation)
- Online: adversary-chosen sequence (no distributional assumptions)

These are typed separately because no common interface captures all three
without losing the structural properties that theorems depend on.

Also includes query-learning interfaces (MembershipOracle, EquivalenceOracle),
noisy data, and advice.
-/

universe u v

/-!
## Time and Streams
-/

/-- Time index for sequential learning. Just ℕ. -/
abbrev TimeStep := ℕ

/-- A data stream: an infinite sequence of labeled examples.
    Primary data interface for Gold-style learning.
    The stream is an enumeration  -  it must eventually cover the relevant domain. -/
-- 6 incoming: learner, ex_learning, version_space, text, informant, noisy_input
structure DataStream (X : Type u) (Y : Type v) where
  /-- The stream of examples at each time step -/
  observe : TimeStep → X × Y

/-- Text presentation: a stream of POSITIVE examples only.
    For a concept c : X → Bool, a text for c enumerates all x with c(x) = true.
    Used in Gold's theorem: identification from text. -/
structure TextPresentation (X : Type u) (c : X → Bool) extends DataStream X Bool where
  /-- Every element in the stream is a positive example -/
  positive : ∀ t, (observe t).2 = true
  /-- Every element in the stream satisfies c -/
  correct : ∀ t, c (observe t).1 = true
  /-- Every positive element eventually appears -/
  exhaustive : ∀ x, c x = true → ∃ t, (observe t).1 = x

/-- Informant presentation: a stream of (example, membership) pairs covering all of X.
    The learner sees both positive and negative examples. Strictly more informative
    than text presentation. -/
structure InformantPresentation (X : Type u) (c : X → Bool) extends DataStream X Bool where
  /-- Labels are correct: the stream tells the truth about membership -/
  correct : ∀ t, (observe t).2 = c (observe t).1
  /-- Every element of X eventually appears -/
  exhaustive : ∀ x : X, ∃ t, (observe t).1 = x

/-- Noisy input: a data stream where labels may be corrupted.
    Instance_of DataStream with noise model. -/
structure NoisyDataStream (X : Type u) (Y : Type v) extends DataStream X Y where
  /-- The true labels (unobserved by learner) -/
  trueLabel : TimeStep → Y
  /-- Noise rate: probability of corruption at each step -/
  noiseRate : ℝ
  /-- Noise rate is bounded -/
  noiseRate_pos : 0 ≤ noiseRate
  noiseRate_lt : noiseRate < 1 / 2

/-!
## IID Samples (PAC paradigm)

This is where the PAC/Gold break manifests at the data level.
IID samples are meaningless in the Gold setting (no distribution).
IID samples are irrelevant in the online setting (adversarial).
-/

/-- An i.i.d. sample from a distribution over X.
    This is the data interface for PAC and statistical learning.
    Requires measure theory  -  MeasurableSpace on X. -/
structure IIDSample (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- The underlying distribution over labeled examples -/
  distribution : MeasureTheory.Measure (X × Y)
  /-- The distribution is a probability measure -/
  isProbability : MeasureTheory.IsProbabilityMeasure distribution
  /-- Sample size -/
  sampleSize : ℕ
  /-- The sample itself: a function from index to labeled example -/
  sample : Fin sampleSize → X × Y

/- Alternative: marginal + conditional decomposition (for agnostic PAC bounds):
-- structure IIDSampleMarginal (X : Type u) (Y : Type v)
--     [MeasurableSpace X] [MeasurableSpace Y] where
--   marginalX : MeasureTheory.ProbabilityMeasure X
--   conditionalY : X → MeasureTheory.ProbabilityMeasure Y
--   sampleSize : ℕ
--   sample : Fin sampleSize → X × Y -/

/- Alternative: prior-weighted sample (for Bayesian posterior consistency):
-- structure IIDSampleBayes (X : Type u) (Y : Type v)
--     [MeasurableSpace X] [MeasurableSpace Y] where
--   distribution : MeasureTheory.ProbabilityMeasure (X × Y)
--   prior : Concept X Y → ℝ≥0
--   sampleSize : ℕ
--   sample : Fin sampleSize → X × Y -/

/-- All Bool-valued functions on X are measurable.
    Domain-level property: the σ-algebra is fine enough that
    concept measurability is never an issue. -/
class MeasurableBoolSpace (X : Type u) [MeasurableSpace X] : Prop where
  all_bool_measurable : ∀ f : X → Bool, Measurable f

/-- MeasurableBoolSpace implies MeasurableHypotheses for every C. -/
instance (priority := 50) MeasurableHypotheses.ofMeasurableBoolSpace
    {X : Type u} [MeasurableSpace X] [h : MeasurableBoolSpace X]
    (C : ConceptClass X Bool) : MeasurableHypotheses X C where
  mem_measurable := fun c _ => h.all_bool_measurable c

/-- The marginal distribution over X (ignoring labels).
    Extracted from an IIDSample. Needed for generalization error definitions. -/
noncomputable def IIDSample.marginalX {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : IIDSample X Y) : MeasureTheory.Measure X :=
  S.distribution.map Prod.fst

/-!
## Query Learning Interfaces

Active learning paradigm: the learner ASKS questions rather than
passively receiving data. These are function types  -  the oracle is
a callable interface.
-/

/-- Membership oracle: given x, returns c(x).
    Used in exact learning (Angluin's framework) and active learning. -/
-- 3 incoming: active_learner, query_complexity, minimally_adequate_teacher
structure MembershipOracle (X : Type u) (Y : Type v) where
  /-- The oracle's response function -/
  query : X → Y
  /-- The target concept the oracle answers about -/
  target : Concept X Y
  /-- Oracle is truthful -/
  truthful : ∀ x, query x = target x

/-- Equivalence oracle: given a hypothesis h, either confirms h = c
    or returns a counterexample x where h(x) ≠ c(x). -/
-- 3 incoming: exact_learning, query_complexity, minimally_adequate_teacher
structure EquivalenceOracle (X : Type u) (Y : Type v) where
  /-- The target concept -/
  target : Concept X Y
  /-- Query: given hypothesis, either confirm or give counterexample -/
  query : Concept X Y → Option X
  /-- If query returns none, hypothesis equals target -/
  correct_none : ∀ h, query h = none → h = target
  /-- If query returns some x, it's a genuine counterexample -/
  correct_some : ∀ h x, query h = some x → h x ≠ target x

/-- A counterexample is a domain element where the hypothesis disagrees with the target. -/
def Counterexample (X : Type u) (Y : Type v) (h c : Concept X Y) := { x : X // h x ≠ c x }

/-- Advice: additional information given to a learner beyond the data.
    Used in advice_reduction theorems and learner_with_advice. -/
def Advice (A : Type*) := A
