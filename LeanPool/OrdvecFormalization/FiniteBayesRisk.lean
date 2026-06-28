/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteExperiment

/-!
# Finite Bayes-risk wrappers

This file gives Bayes-risk and cost-sensitive Bayes-risk names to the generic
finite weighted-risk API.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- Finite Bayes risk for arbitrary full observations. -/
noncomputable def finiteBayesRisk {Ω : Type} [Fintype Ω] (p0 p1 : FiniteLaw Ω)
    (prior : Prior) (R : Set Ω) : ℝ≥0 :=
  finiteWeightedRisk p0 p1 prior.compl prior.prob R

/-- Finite cost-sensitive Bayes risk for arbitrary full observations. -/
noncomputable def finiteCostedBayesRisk {Ω : Type} [Fintype Ω] (p0 p1 : FiniteLaw Ω)
    (prior : Prior) (costs : DecisionCosts) (R : Set Ω) : ℝ≥0 :=
  finiteWeightedRisk p0 p1 (costs.falseAccept * prior.compl)
    (costs.falseReject * prior.prob) R

end OrdvecFormalization
