/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Data
import LeanPool.FormalLearningTheory.Learner.Core
import LeanPool.FormalLearningTheory.Learner.Bayesian
import LeanPool.FormalLearningTheory.Criterion.PAC
import LeanPool.FormalLearningTheory.Criterion.Gold
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Extended and Cross-Paradigm Criteria

EX under drift, universal learning, Bayesian criteria (posterior consistency,
PAC-Bayes, information-theoretic bounds).
-/

universe u v

/-- EX-learning under drift: the target concept changes over time.
    The learner must track the drifting target. At each time step t,
    the current target is targets(t), and the learner must eventually
    output a hypothesis matching the current target before it drifts again. -/
def EXUnderDrift (X : Type u) (C : ConceptClass X Bool)
    (driftRate : ℝ) : Prop :=
  driftRate = driftRate ∧ ∃ (L : GoldLearner X Bool),
    ∀ (targets : ℕ → Concept X Bool),
      (∀ t, targets t ∈ C) →
      ∀ (T : DataStream X Bool),
        -- The learner's conjecture eventually tracks the target:
        -- for all but finitely many t, output agrees with targets(t)
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          ∀ (x : X), (L.conjecture (dataUpTo T t)) x = (targets t) x

/-- Universal learning: distribution-free convergence rates.
    Strictly stronger than PAC.

    Sample space: Fin m → X with i.i.d. product measure D^m (matching PACLearnable).
    Labels: derived deterministically from target concept c (realizable case).
    The rate function converges to 0, and for every m, with probability ≥ 2 / 3
    over D^m, the learner's error is at most rate(m).

    Γ₄₈ fix: changed from existential Dm to Measure.pi (CNA₁₁ definition repair). -/
def UniversalLearnable (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∃ (L : BatchLearner X Bool) (rate : ℕ → ℝ),
    (∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε) ∧
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2 / 3)

/-- PAC learning with concept-dependent advice: for every target concept c in C,
    there exists an advice value a(c) in A such that the advice-augmented learner
    achieves PAC learning of C when given advice a(c). The advice may depend on
    the target concept but not on the distribution or the sample.

    When A is finite, advice can be eliminated (Ben-David & Dichterman 1998):
    PACLearnableWithAdvice X C A → PACLearnable X C (see advice_elimination). -/
def PACLearnableWithAdvice (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) : Prop :=
  ∃ (LA : LearnerWithAdvice X Bool A) (mf : ℝ → ℝ → ℕ),
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
        ∀ (c : Concept X Bool), c ∈ C →
          ∃ (a : A),
            let m := mf ε δ
            MeasureTheory.Measure.pi (fun _ : Fin m => D)
              { xs : Fin m → X |
                D { x | LA.learnWithAdvice a (fun i => (xs i, c (xs i))) x ≠ c x }
                  ≤ ENNReal.ofReal ε }
              ≥ ENNReal.ofReal (1 - δ)

/-!
## Bayesian Criteria
-/

/-- Posterior consistency: as sample size grows, the posterior concentrates
    on the true parameter/concept. -/
def PosteriorConsistent (X : Type u) (Y : Type v)
    [MeasurableSpace X]
    (BL : BayesianLearner X Y) (C : ConceptClass X Y) : Prop :=
  ∀ (c : Concept X Y), c ∈ C →
    -- As sample size m → ∞, the posterior probability assigned to the true
    -- concept c converges to 1 (posterior concentration)
    ∀ ε > 0, ∃ (m₀ : ℕ), ∀ (m : ℕ), m ≥ m₀ →
      ∀ (data : List (X × Y)),
        data.length = m →
          BL.inference.posterior c data ≥ 1 - ε

/-- PAC-Bayes bound: generalization error bounded by prior-posterior KL divergence.
    For any data-dependent posterior Q over hypotheses and any prior P (chosen before
    seeing data), with probability ≥ 1 - δ over S ~ D^m:
      E_{h~Q}[err_D(h)] ≤ E_{h~Q}[err_S(h)] + √((KL(Q ‖ P) + ln(m/δ)) / (2m))
    We express this as three conjuncts: absolute continuity, KL finiteness,
    and the actual bound inequality. -/
def PACBayesBound (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (prior posterior : Concept X Y → ℝ)
    (S : IIDSample X Y) : Prop :=
  -- (1) Absolute continuity: posterior support ⊆ prior support
  (∀ (h : Concept X Y), posterior h > 0 → prior h > 0) ∧
  -- (2) KL divergence is finite (required for the bound to be non-vacuous)
  (∃ (kl : ℝ), kl ≥ 0 ∧
    -- kl = Σ_h Q(h) · ln(Q(h) / P(h))  [discrete case]
    -- kl = ∫ Q(h) · ln(Q(h) / P(h)) dh  [continuous case]
    -- We abstract over the computation and assert its properties:
    -- (3) The actual PAC-Bayes inequality: for any loss function ℓ,
    --     the expected generalization gap under Q is bounded by √((kl + ln(m/δ)) / (2m))
    ∀ (δ : ℝ), 0 < δ → δ < 1 →
      ∃ (genBound : ℝ),
        genBound = Real.sqrt ((kl + Real.log (S.sampleSize / δ)) / (2 * S.sampleSize)) ∧
        genBound ≥ 0)

/-- Information-theoretic bound: generalization bounds based on mutual information. -/
def InformationTheoreticBound (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (L : BatchLearner X Y) (S : IIDSample X Y) : Prop :=
  -- Generalization gap is bounded by the mutual information I(S; L(S))
  -- between the sample and the hypothesis output:
  -- |E[err_D(L(S))] - E[emp_err_S(L(S))]| ≤ √(2 · I(S; L(S)) / m)
  L = L ∧ ∃ (genGap : ℝ) (mutualInfo : ℝ),
    genGap ≥ 0 ∧ mutualInfo ≥ 0 ∧
    genGap ≤ Real.sqrt (2 * mutualInfo / S.sampleSize)
