/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Learner.Core

/-!
# Bayesian Inference and Learners

BayesianInference bundles prior, likelihood, and posterior computation.
BayesianLearner extends BatchLearner with Bayesian inference machinery.
GibbsPosterior adds temperature for PAC-Bayes optimization.
-/

universe u v

/-- Bayesian inference: bundles prior, likelihood model, and posterior computation. -/
structure BayesianInference (X : Type u) (Y : Type v) [MeasurableSpace X] where
  /-- Prior distribution over hypotheses -/
  prior : Concept X Y → ℝ
  /-- Likelihood: probability of data given hypothesis -/
  likelihood : Concept X Y → X × Y → ℝ
  /-- Posterior: prior(h) × ∏ likelihood(h, dᵢ). Unnormalized; the normalization
      constant Z = Σ_h' prior(h') × ∏ likelihood(h', dᵢ) is omitted because
      computing it requires summing over all hypotheses (which may be uncountable).
      Downstream definitions that need a proper probability must normalize explicitly.
      This is the standard "unnormalized posterior" used in computational Bayesian inference. -/
  posterior (h : Concept X Y) (data : List (X × Y)) : ℝ :=
    prior h * (data.map (likelihood h)).prod

/-- A Bayesian learner carries a prior and updates via Bayes' rule. -/
structure BayesianLearner (X : Type u) (Y : Type v) [MeasurableSpace X] where
  /-- The hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Bayesian inference engine -/
  inference : BayesianInference X Y
  /-- MAP learner: output the maximum a posteriori hypothesis -/
  learnMAP : {m : ℕ} → (Fin m → X × Y) → Concept X Y
  /-- Output is in hypothesis space -/
  output_in_H : ∀ {m : ℕ} (S : Fin m → X × Y), learnMAP S ∈ hypotheses

/-- Gibbs posterior: a Bayesian learner that uses a tempered posterior
    (PAC-Bayes bound optimization). -/
structure GibbsPosterior (X : Type u) (Y : Type v) [MeasurableSpace X] where
  /-- Base Bayesian learner -/
  base : BayesianLearner X Y
  /-- Temperature parameter (inverse) -/
  lambda : ℝ
  /-- Temperature is positive -/
  lambda_pos : 0 < lambda
