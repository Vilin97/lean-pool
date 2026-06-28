/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteDecision

/-!
# Monotone likelihood ratio

This file states MLR in cross-multiplication form and proves that it makes the
Bayes admit predicate monotone.
-/

open scoped NNReal

namespace OrdvecFormalization

/--
Weighted Bayes admission predicate.

The rule admits `H₁` at `x` exactly when the weighted loss of admitting is no
larger than the weighted loss of rejecting.
-/
def weightedBayesAdmit {n : ℕ} (p0 p1 : PosPMF n) (w0 w1 : ℝ≥0)
    (x : Support n) : Prop :=
  w0 * p0.mass x ≤ w1 * p1.mass x

/-- Bayes admits `H₁` at `x` exactly when the pointwise `H₁` loss is no larger. -/
def bayesAdmit {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior) (x : Support n) : Prop :=
  weightedBayesAdmit p0 p1 prior.compl prior.prob x

/--
Cross-multiplication monotone likelihood ratio.

This avoids division in the theorem statement; strict positivity is used only
when canceling a common factor in the monotonicity proof.
-/
def HasMLR {n : ℕ} (p0 p1 : PosPMF n) : Prop :=
  ∀ x y : Support n, x ≤ y → p1.mass x * p0.mass y ≤ p1.mass y * p0.mass x

/-- MLR implies that any weighted Bayes admit predicate is monotone on the support. -/
theorem mlr_monotone_weightedBayesAdmit {n : ℕ} (p0 p1 : PosPMF n) (w0 w1 : ℝ≥0)
    (hmlr : HasMLR p0 p1) :
    Monotone (weightedBayesAdmit p0 p1 w0 w1) := by
  intro x y hxy hx
  dsimp [weightedBayesAdmit] at hx ⊢
  have hleft :
      w0 * p0.mass x * p0.mass y ≤ w1 * p1.mass x * p0.mass y := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_left hx (p0.mass y)
  have hright :
      w1 * p1.mass x * p0.mass y ≤ w1 * p1.mass y * p0.mass x := by
    simpa [mul_assoc] using mul_le_mul_right (hmlr x y hxy) w1
  have hchain :
      w0 * p0.mass y * p0.mass x ≤ w1 * p1.mass y * p0.mass x := by
    calc
      w0 * p0.mass y * p0.mass x =
          w0 * p0.mass x * p0.mass y := by
        ac_rfl
      _ ≤ w1 * p1.mass x * p0.mass y := hleft
      _ ≤ w1 * p1.mass y * p0.mass x := hright
  exact (mul_le_mul_iff_left₀ (p0.pos x)).mp hchain

/-- MLR implies that the Bayes admit predicate is monotone on the support. -/
theorem mlr_monotone_bayesAdmit {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (hmlr : HasMLR p0 p1) :
    Monotone (bayesAdmit p0 p1 prior) :=
  mlr_monotone_weightedBayesAdmit p0 p1 prior.compl prior.prob hmlr

/-- Likelihood ratio at a support point, written with nonnegative division. -/
noncomputable def likelihoodRatio {n : ℕ} (p0 p1 : PosPMF n) (x : Support n) : ℝ≥0 :=
  p1.mass x / p0.mass x

/-- The weighted Bayes cutoff in likelihood-ratio coordinates. -/
noncomputable def weightedLikelihoodCutoff (w0 w1 : ℝ≥0) (hw1 : 0 < w1) : ℝ≥0 :=
  have _ : w1 ≠ 0 := ne_of_gt hw1
  w0 / w1

/-- The usual prior-odds cutoff in likelihood-ratio coordinates. -/
noncomputable def priorOddsCutoff (prior : Prior) (hprior : 0 < prior.prob) : ℝ≥0 :=
  weightedLikelihoodCutoff prior.compl prior.prob hprior

/--
Weighted Bayes admission is equivalent to exceeding the likelihood-ratio
cutoff, when the reject-side weight is positive.
-/
theorem weightedBayesAdmit_iff_cutoff_le_likelihoodRatio {n : ℕ}
    (p0 p1 : PosPMF n) {w0 w1 : ℝ≥0} (hw1 : 0 < w1) (x : Support n) :
    weightedBayesAdmit p0 p1 w0 w1 x ↔
      weightedLikelihoodCutoff w0 w1 hw1 ≤ likelihoodRatio p0 p1 x := by
  unfold weightedBayesAdmit weightedLikelihoodCutoff likelihoodRatio
  rw [div_le_div_iff₀ hw1 (p0.pos x)]
  simp [mul_comm]

/--
Bayes admission is equivalent to exceeding the prior-odds likelihood-ratio
cutoff, when the `H₁` prior is positive.
-/
theorem bayesAdmit_iff_priorOddsCutoff_le_likelihoodRatio {n : ℕ}
    (p0 p1 : PosPMF n) (prior : Prior) (hprior : 0 < prior.prob) (x : Support n) :
    bayesAdmit p0 p1 prior x ↔ priorOddsCutoff prior hprior ≤ likelihoodRatio p0 p1 x := by
  simpa [bayesAdmit, priorOddsCutoff, Prior.compl] using
    weightedBayesAdmit_iff_cutoff_le_likelihoodRatio p0 p1 hprior x

end OrdvecFormalization
