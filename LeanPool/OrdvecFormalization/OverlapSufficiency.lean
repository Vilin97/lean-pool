/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.OrdinalSufficiency
import LeanPool.OrdvecFormalization.FNCH

/-!
# Quotient sufficiency for overlap evidence

This file specializes the ordered quotient sufficiency theorem to actual overlap
coordinates.  The observation space is still arbitrary: a quotient map extracts
an observation quotient, and an overlap statistic on that quotient lands in the
feasible overlap support.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- Pull an actual-overlap threshold back through a quotient. -/
def overlapQuotientThresholdSet {Ω Ωq : Type} (p : FNCHParams)
    (Q : Ω → Ωq) (O : Ωq → p.support) (cut : Fin (p.hi - p.lo + 2)) : Set Ω :=
  {ω | O (Q ω) ∈ actualOverlapThresholdSet p cut}

/-- Actual-overlap quotient thresholds are ordered quotient thresholds. -/
theorem overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet {Ω Ωq : Type}
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (cut : Fin (p.hi - p.lo + 2)) :
    overlapQuotientThresholdSet p Q O cut =
      orderedQuotientThresholdSet Q O cut := by
  ext ω
  simp [overlapQuotientThresholdSet, orderedQuotientThresholdSet,
    actualOverlapThresholdSet_eq_thresholdSet p cut]

/--
Overlap factorization condition: the full likelihood ratio is a monotone
function of the actual-overlap evidence extracted from an ordinal quotient.
-/
def FiniteLikelihoodRatioFactorsThroughOverlapEvidence {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (p0 p1 : FiniteLaw Ω) : Prop :=
  FiniteLikelihoodRatioFactorsThroughOrderedEvidence Q O p0 p1

/--
If the full likelihood ratio factors monotonically through quotient-level
overlap evidence, then a pulled-back actual-overlap threshold is Bayes-optimal
among all deterministic full-space admit sets.
-/
theorem exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_overlapEvidenceFactor
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) (hw1 : 0 < w1)
    (hfactor : FiniteLikelihoodRatioFactorsThroughOverlapEvidence p Q O p0 p1) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (overlapQuotientThresholdSet p Q O cut) ≤
        finiteWeightedRisk p0 p1 w0 w1 R := by
  rcases exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor
      Q O p0 p1 w0 w1 hw1 hfactor with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  simpa [overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet p Q O cut] using hcut R

/--
Under monotone likelihood-ratio factorization through quotient-level overlap
evidence, an actual-overlap threshold is Bayes-optimal against all
deterministic full-space rules.
-/
theorem exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_likelihoodRatioFactor
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) (hw1 : 0 < w1)
    (hfactor : FiniteLikelihoodRatioFactorsThroughOverlapEvidence p Q O p0 p1) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (overlapQuotientThresholdSet p Q O cut) ≤
        finiteWeightedRisk p0 p1 w0 w1 R :=
  exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_overlapEvidenceFactor
    p Q O p0 p1 w0 w1 hw1 hfactor

end OrdvecFormalization
