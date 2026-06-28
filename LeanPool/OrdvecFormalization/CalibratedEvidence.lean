/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Data.ENNReal.Basic
import LeanPool.OrdvecFormalization.FiniteBayesRisk
import LeanPool.OrdvecFormalization.OrdinalSufficiency

/-!
# Calibrated ordered evidence

This file packages a Bayes-optimal ordered threshold with a supplied calibration
equality at the same cutoff. The calibration record is deliberately external:
it does not assert that the calibrated event is the full-space decision event,
nor that the calibration model is adequate for any empirical null.
-/

open scoped NNReal ENNReal

namespace OrdvecFormalization

/-- A family of ordered tail events with a supplied mass/value equality. -/
structure OrderedTailCalibration (n : ℕ) (Λ : Type) where
  /-- Tail event indexed by the same finite ordered cut used by threshold rules. -/
  event : Fin (n + 2) → Set Λ
  /-- Mass functional for calibrated events. -/
  mass : Set Λ → ℝ≥0∞
  /-- Closed-form or externally supplied value at each cut. -/
  value : Fin (n + 2) → ℝ≥0∞
  /-- Supplied calibration equality for every cut. -/
  calibrated : ∀ cut, mass (event cut) = value cut

/--
If the likelihood ratio factors monotonically through ordered evidence, some
ordered cutoff is Bayes-optimal and carries the supplied calibration equality
at the same cutoff.
-/
theorem exists_calibratedOrderedThreshold_finiteBayesRisk_le_of_orderedEvidenceFactor
    {Ω Ωq Λ : Type} [Fintype Ω] {n : ℕ}
    (Q : Ω → Ωq) (T : Ωq → Support n)
    (p0 p1 : FiniteLaw Ω) (prior : Prior) (hprior : 0 < prior.prob)
    (calibration : OrderedTailCalibration n Λ)
    (hfactor : FiniteLikelihoodRatioFactorsThroughOrderedEvidence Q T p0 p1) :
    ∃ cut : Fin (n + 2),
      (∀ R : Set Ω,
        finiteBayesRisk p0 p1 prior (orderedQuotientThresholdSet Q T cut) ≤
          finiteBayesRisk p0 p1 prior R) ∧
      calibration.mass (calibration.event cut) = calibration.value cut := by
  rcases exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor
      Q T p0 p1 prior.compl prior.prob hprior hfactor with ⟨cut, hopt⟩
  exact ⟨cut, fun R => by simpa [finiteBayesRisk] using hopt R, calibration.calibrated cut⟩

/--
Cost-sensitive version: asymmetric costs change the selected cutoff, but the
returned cutoff still carries the supplied calibration equality.
-/
theorem exists_calibratedOrderedThreshold_finiteCostedBayesRisk_le_of_orderedEvidenceFactor
    {Ω Ωq Λ : Type} [Fintype Ω] {n : ℕ}
    (Q : Ω → Ωq) (T : Ωq → Support n)
    (p0 p1 : FiniteLaw Ω) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob)
    (calibration : OrderedTailCalibration n Λ)
    (hfactor : FiniteLikelihoodRatioFactorsThroughOrderedEvidence Q T p0 p1) :
    ∃ cut : Fin (n + 2),
      (∀ R : Set Ω,
        finiteCostedBayesRisk p0 p1 prior costs (orderedQuotientThresholdSet Q T cut) ≤
          finiteCostedBayesRisk p0 p1 prior costs R) ∧
      calibration.mass (calibration.event cut) = calibration.value cut := by
  rcases exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor
      Q T p0 p1 (costs.falseAccept * prior.compl) (costs.falseReject * prior.prob)
      hw1 hfactor with ⟨cut, hopt⟩
  exact ⟨cut, fun R => by simpa [finiteCostedBayesRisk] using hopt R,
    calibration.calibrated cut⟩

end OrdvecFormalization
