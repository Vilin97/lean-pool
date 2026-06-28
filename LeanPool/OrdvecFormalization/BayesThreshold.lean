/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteExperiment
import LeanPool.OrdvecFormalization.MLR

/-!
# Bayes threshold theorem

The finite Bayes risk is a pointwise sum. Under MLR, the pointwise Bayes admit
predicate is monotone, hence a threshold, and that threshold minimizes the risk.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- Finite weighted Bayes risk for an arbitrary deterministic admit set. -/
noncomputable def weightedBayesRisk {n : ℕ} (p0 p1 : PosPMF n) (w0 w1 : ℝ≥0)
    (R : Set (Support n)) : ℝ≥0 :=
  by
    classical
    exact Finset.univ.sum fun x : Support n =>
      if x ∈ R then w0 * p0.mass x else w1 * p1.mass x

/--
The ordered-support risk API is the arbitrary finite-law risk API specialized
to the finite law induced by a positive PMF.
-/
theorem weightedBayesRisk_eq_finiteWeightedRisk {n : ℕ} (p0 p1 : PosPMF n)
    (w0 w1 : ℝ≥0) (R : Set (Support n)) :
    weightedBayesRisk p0 p1 w0 w1 R =
      finiteWeightedRisk (finiteLawOfPosPMF p0) (finiteLawOfPosPMF p1) w0 w1 R := by
  dsimp [weightedBayesRisk, finiteWeightedRisk, finiteLawOfPosPMF]

/-- Finite Bayes risk for an arbitrary deterministic admit set. -/
noncomputable def bayesRisk {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (R : Set (Support n)) : ℝ≥0 :=
  weightedBayesRisk p0 p1 prior.compl prior.prob R

/-- Cost-sensitive Bayes admission predicate. -/
def costedBayesAdmit {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (costs : DecisionCosts) (x : Support n) : Prop :=
  weightedBayesAdmit p0 p1 (costs.falseAccept * prior.compl)
    (costs.falseReject * prior.prob) x

/-- Finite cost-sensitive Bayes risk for an arbitrary deterministic admit set. -/
noncomputable def costedBayesRisk {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (costs : DecisionCosts) (R : Set (Support n)) : ℝ≥0 :=
  weightedBayesRisk p0 p1 (costs.falseAccept * prior.compl)
    (costs.falseReject * prior.prob) R

/-- Under MLR, any weighted Bayes admit set is represented by a threshold. -/
theorem weightedBayesAdmit_isThreshold {n : ℕ} (p0 p1 : PosPMF n)
    (w0 w1 : ℝ≥0) (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ x : Support n,
      weightedBayesAdmit p0 p1 w0 w1 x ↔ x ∈ thresholdSet n cut :=
  exists_threshold_of_monotone_pred n (weightedBayesAdmit p0 p1 w0 w1)
    (mlr_monotone_weightedBayesAdmit p0 p1 w0 w1 hmlr)

/-- Under MLR, the Bayes admit set is represented by a threshold. -/
theorem bayesAdmit_isThreshold {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ x : Support n,
      bayesAdmit p0 p1 prior x ↔ x ∈ thresholdSet n cut :=
  weightedBayesAdmit_isThreshold p0 p1 prior.compl prior.prob hmlr

/-- Under MLR, any cost-sensitive Bayes admit set is represented by a threshold. -/
theorem costedBayesAdmit_isThreshold {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (costs : DecisionCosts) (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ x : Support n,
      costedBayesAdmit p0 p1 prior costs x ↔ x ∈ thresholdSet n cut :=
  weightedBayesAdmit_isThreshold p0 p1 (costs.falseAccept * prior.compl)
    (costs.falseReject * prior.prob) hmlr

/-- The weighted Bayes admit rule minimizes finite weighted Bayes risk. -/
theorem weighted_threshold_bayesRisk_optimal {n : ℕ} (p0 p1 : PosPMF n)
    (w0 w1 : ℝ≥0) (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ R : Set (Support n),
      weightedBayesRisk p0 p1 w0 w1 (thresholdSet n cut) ≤
        weightedBayesRisk p0 p1 w0 w1 R := by
  rcases weightedBayesAdmit_isThreshold p0 p1 w0 w1 hmlr with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  have hset : thresholdSet n cut =
      finiteWeightedBayesAdmitSet (finiteLawOfPosPMF p0) (finiteLawOfPosPMF p1) w0 w1 := by
    ext x
    exact (hcut x).symm
  calc
    weightedBayesRisk p0 p1 w0 w1 (thresholdSet n cut)
        = finiteWeightedRisk (finiteLawOfPosPMF p0) (finiteLawOfPosPMF p1) w0 w1
            (thresholdSet n cut) :=
      weightedBayesRisk_eq_finiteWeightedRisk p0 p1 w0 w1 (thresholdSet n cut)
    _ = finiteWeightedRisk (finiteLawOfPosPMF p0) (finiteLawOfPosPMF p1) w0 w1
          (finiteWeightedBayesAdmitSet (finiteLawOfPosPMF p0) (finiteLawOfPosPMF p1) w0 w1) := by
      rw [hset]
    _ ≤ finiteWeightedRisk (finiteLawOfPosPMF p0) (finiteLawOfPosPMF p1) w0 w1 R :=
      finiteWeightedBayesAdmitSet_optimal (finiteLawOfPosPMF p0) (finiteLawOfPosPMF p1)
        w0 w1 R
    _ = weightedBayesRisk p0 p1 w0 w1 R :=
      (weightedBayesRisk_eq_finiteWeightedRisk p0 p1 w0 w1 R).symm

/-- The threshold Bayes admit rule minimizes finite Bayes risk. -/
theorem threshold_bayesRisk_optimal {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ R : Set (Support n),
      bayesRisk p0 p1 prior (thresholdSet n cut) ≤ bayesRisk p0 p1 prior R :=
  weighted_threshold_bayesRisk_optimal p0 p1 prior.compl prior.prob hmlr

/-- The cost-sensitive Bayes admit rule minimizes finite cost-sensitive Bayes risk. -/
theorem costed_threshold_bayesRisk_optimal {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (costs : DecisionCosts) (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ R : Set (Support n),
      costedBayesRisk p0 p1 prior costs (thresholdSet n cut) ≤
        costedBayesRisk p0 p1 prior costs R :=
  weighted_threshold_bayesRisk_optimal p0 p1 (costs.falseAccept * prior.compl)
    (costs.falseReject * prior.prob) hmlr

end OrdvecFormalization
