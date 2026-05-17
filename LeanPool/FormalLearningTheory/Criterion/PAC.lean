/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Data
import LeanPool.FormalLearningTheory.Learner.Core
import LeanPool.FormalLearningTheory.Learner.Active
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# PAC Learning Criteria

PAC (Probably Approximately Correct), Agnostic PAC, and Exact (Angluin) learning.

## PAC quantifier structure (standard, realizable)

  ∃ L mf, ∀ ε δ > 0, ∀ D (probability on X), ∀ c ∈ C,
    let m := mf ε δ
    D^m { xs : Fin m → X | err_D(L(labeled xs)) ≤ ε } ≥ 1 - δ

where D^m = Measure.pi (fun _ : Fin m => D) is the i.i.d. product measure
and the labeled sample is constructed as fun i => (xs i, c (xs i)).

## Key design decision

The sample distribution is the CONCRETE product measure D^m, NOT an existentially
quantified Dm. The existential ∃Dm formulation is strictly weaker than standard PAC:
it allows Dm to depend on the target concept c, so finite-domain examples can be
learned by choosing a concept-dependent point-mass sample distribution.

Instead, Dm = Measure.pi (fun _ : Fin m => D), which:
- Does NOT depend on c (D is quantified before c)
- Correctly captures independent sampling
- Uses Mathlib's Measure.pi, which provides IsProbabilityMeasure instance
  when each factor is a probability measure

## Measurability note

The set { xs | D { x | L.learn (labeled xs) x ≠ c x } ≤ ε } is measured by
Measure.pi via outer measure. Full measurability of this set requires the error
function xs ↦ D{x | L(S(xs)) x ≠ c x} to be measurable  -  a deep technical
condition that specific proofs (Hoeffding, Sauer-Shelah) will establish.
-/

universe u v

/-- PAC (Probably Approximately Correct) learning.
    The central definition of computational learning theory.

    Sample space: Fin m → X with i.i.d. product measure D^m.
    Labels: derived deterministically from target concept c (realizable case).
    Error: D-probability of disagreement between learner output and c. -/
def PACLearnable (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
        ∀ (c : Concept X Bool), c ∈ C →
          let m := mf ε δ
          -- D^m: the i.i.d. product measure on Fin m → X
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            -- The success event: error of L on labeled sample ≤ ε
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ)

/-- Agnostic PAC learning: no realizability assumption.
    The learner competes against the best hypothesis in H.

    Sample space: Fin m → X × Bool with i.i.d. product measure D^m.
    Here D is a distribution over X × Bool (the joint distribution over
    instances and labels, possibly noisy). No deterministic labeling assumption.

    The learner's error is compared to the BEST hypothesis in H:
    err(L(S)) ≤ min_{h ∈ H} err(h) + ε. -/
def AgnosticPACLearnable (X : Type u) [MeasurableSpace X]
    (H : HypothesisSpace X Bool) : Prop :=
  ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure (X × Bool)), MeasureTheory.IsProbabilityMeasure D →
        let m := mf ε δ
        -- D^m: the i.i.d. product measure on Fin m → X × Bool
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          -- Success event: learner is competitive with best h ∈ H
          { S : Fin m → X × Bool |
            ∀ (h : Concept X Bool), h ∈ H →
              D { p | L.learn S p.1 ≠ p.2 } ≤
                D { p | h p.1 ≠ p.2 } + ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)

/-- Exact learning (Angluin model): learn using membership + equivalence queries.
    This is a deterministic, query-based paradigm  -  no distributional assumptions.
    This is a genuinely different paradigm from PAC  -  deterministic, query-based,
    with no distributional assumptions. -/
def ExactLearnable (X : Type u)
    (C : ConceptClass X Bool) : Prop :=
  ∃ (L : ActiveLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (mq : MembershipOracle X Bool),
        mq.target = c →
          L.learnMQ mq = c
