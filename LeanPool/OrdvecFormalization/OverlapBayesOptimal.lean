/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.CanonicalTilt
import LeanPool.OrdvecFormalization.FiniteBayesRisk

/-!
# Bayes-optimal overlap thresholds

This file packages the quotient, overlap, and canonical tilt layers into theorem
statements about finite Bayes risk.  The proofs are intentionally thin: the
mathematical work lives in `FiniteExperiment`, `OrdinalSufficiency`,
`OverlapSufficiency`, and `CanonicalTilt`.
-/

open scoped NNReal

namespace OrdvecFormalization

/--
Under the canonical finite model where one law is an exponential tilt of a
positive full-space base law by overlap evidence, an actual-overlap threshold
pulled back through the quotient is optimal for finite Bayes risk among all
deterministic full-space rules.
-/
theorem exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior (overlapQuotientThresholdSet p Q O cut) ≤
        finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior R := by
  simpa [finiteBayesRisk] using
    exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt
      p base Q O hθ prior.compl prior.prob hprior

/-- Strict-parameter version of the finite Bayes-risk theorem. -/
theorem exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior (overlapQuotientThresholdSet p Q O cut) ≤
        finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior R :=
  exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt
    p base Q O hθ.le prior hprior

/--
Changing priors or asymmetric costs changes only the threshold, not the
decision-rule form, provided the false-reject side has positive weight.
-/
theorem exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs (overlapQuotientThresholdSet p Q O cut) ≤
        finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs R := by
  simpa [finiteCostedBayesRisk] using
    exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt p base Q O hθ
      (costs.falseAccept * prior.compl) (costs.falseReject * prior.prob) hw1

/-- Strict-parameter version of the cost-sensitive theorem. -/
theorem exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt_of_lt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs (overlapQuotientThresholdSet p Q O cut) ≤
        finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs R :=
  exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt
    p base Q O hθ.le prior costs hw1

end OrdvecFormalization
