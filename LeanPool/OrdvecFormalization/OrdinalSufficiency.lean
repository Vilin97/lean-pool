/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteExperiment

/-!
# Ordered quotient sufficiency for threshold decisions

This file composes the quotient optimality layer with ordered evidence. If the
full likelihood ratio factors through a quotient and then through a monotone
ordered statistic, the Bayes-optimal full-space rule is a threshold pulled back
from that ordered evidence.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- Pull an ordered evidence threshold back through an ordinal quotient. -/
def orderedQuotientThresholdSet {Ω Ωq : Type} {n : ℕ}
    (Q : Ω → Ωq) (T : Ωq → Support n) (cut : Fin (n + 2)) : Set Ω :=
  {ω | T (Q ω) ∈ thresholdSet n cut}

/--
The full likelihood ratio factors through monotone ordered evidence on a
quotient observation space.
-/
def FiniteLikelihoodRatioFactorsThroughOrderedEvidence {Ω Ωq : Type} [Fintype Ω]
    {n : ℕ} (Q : Ω → Ωq) (T : Ωq → Support n) (p0 p1 : FiniteLaw Ω) : Prop :=
  ∃ φ : Support n → ℝ≥0,
    Monotone φ ∧ ∀ ω : Ω, finiteLikelihoodRatio p0 p1 ω = φ (T (Q ω))

/--
If the full likelihood ratio is a monotone function of ordered quotient
evidence, then a pulled-back threshold is Bayes-optimal among all full-space
deterministic admit sets.
-/
theorem exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_monotone
    {Ω Ωq : Type} [Fintype Ω] {n : ℕ}
    (Q : Ω → Ωq) (T : Ωq → Support n)
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) (hw1 : 0 < w1)
    (φ : Support n → ℝ≥0)
    (hφ : ∀ ω : Ω, finiteLikelihoodRatio p0 p1 ω = φ (T (Q ω)))
    (hmono : Monotone φ) :
    ∃ cut : Fin (n + 2), ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (orderedQuotientThresholdSet Q T cut) ≤
        finiteWeightedRisk p0 p1 w0 w1 R := by
  let cutoff : ℝ≥0 := w0 / w1
  let P : Support n → Prop := fun x => cutoff ≤ φ x
  have hPmono : Monotone P := by
    intro x y hxy hx
    exact le_trans hx (hmono hxy)
  rcases exists_threshold_of_monotone_pred n P hPmono with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  have hset :
      orderedQuotientThresholdSet Q T cut =
        finiteWeightedBayesAdmitSet p0 p1 w0 w1 := by
    ext ω
    constructor
    · intro hω
      change finiteWeightedBayesAdmit p0 p1 w0 w1 ω
      rw [finiteWeightedBayesAdmit_iff_cutoff_le_likelihoodRatio p0 p1 hw1 ω,
        hφ ω]
      exact (hcut (T (Q ω))).mpr (by
        simpa [orderedQuotientThresholdSet] using hω)
    · intro hω
      change finiteWeightedBayesAdmit p0 p1 w0 w1 ω at hω
      have hcutoff : cutoff ≤ φ (T (Q ω)) := by
        have hcutoff' : w0 / w1 ≤ finiteLikelihoodRatio p0 p1 ω :=
          (finiteWeightedBayesAdmit_iff_cutoff_le_likelihoodRatio p0 p1 hw1 ω).mp hω
        simpa [cutoff, hφ ω] using hcutoff'
      exact (by
        simpa [orderedQuotientThresholdSet] using (hcut (T (Q ω))).mp hcutoff)
  calc
    finiteWeightedRisk p0 p1 w0 w1 (orderedQuotientThresholdSet Q T cut)
        = finiteWeightedRisk p0 p1 w0 w1 (finiteWeightedBayesAdmitSet p0 p1 w0 w1) := by
      rw [hset]
    _ ≤ finiteWeightedRisk p0 p1 w0 w1 R :=
      finiteWeightedBayesAdmitSet_optimal p0 p1 w0 w1 R

/--
Bundled version: monotone likelihood-ratio factorization through ordered
quotient evidence yields a Bayes-optimal threshold.
-/
theorem exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor
    {Ω Ωq : Type} [Fintype Ω] {n : ℕ}
    (Q : Ω → Ωq) (T : Ωq → Support n)
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) (hw1 : 0 < w1)
    (hfactor : FiniteLikelihoodRatioFactorsThroughOrderedEvidence Q T p0 p1) :
    ∃ cut : Fin (n + 2), ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (orderedQuotientThresholdSet Q T cut) ≤
        finiteWeightedRisk p0 p1 w0 w1 R := by
  rcases hfactor with ⟨φ, hmono, hφ⟩
  exact exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_monotone
    Q T p0 p1 w0 w1 hw1 φ hφ hmono

end OrdvecFormalization
