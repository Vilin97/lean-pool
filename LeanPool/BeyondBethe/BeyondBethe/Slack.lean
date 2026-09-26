/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Bethe
public import LeanPool.BeyondBethe.BeyondBethe.Sequential
public import Mathlib.Tactic

/-! # Slack -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- Row score `s(p)=H(p)+T(p)` from paper (24). -/
noncomputable def rowScore
    {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  shannonEntropy p + rowT p

/-- Direct cancellation between the Bethe objective and the row corrections.
This is the algebraic core of paper Lemma 10. -/
theorem bethe_add_rowCorrection_eq_logWeight_add_rowScore
    {m : ℕ} (A P : Matrix (Fin m) (Fin m) ℝ) :
    betheObjective A P + ∑ i, rowCorrection (P i) =
      (∑ i, ∑ j, P i j * Real.log (A i j)) +
        ∑ i, rowScore (P i) := by
  rw [betheObjective]
  simp_rw [betheRowObjective, rowCorrection, rowScore, shannonEntropy]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The averaged KL term `D` in the paper, specialized to the Gibbs law and
its assignment marginals. -/
noncomputable def gibbsSequentialDivergence
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  averagedSequentialDivergence
    (gibbsProbability A) (assignmentMarginal A)

theorem neg_logMarginals_add_rowT_eq_rowScore
    {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) :
    -(∑ i, ∑ j, P i j * Real.log (P i j)) + ∑ i, rowT (P i) =
      ∑ i, rowScore (P i) := by
  have hneg : -(∑ i, ∑ j, P i j * Real.log (P i j)) =
      ∑ i, ∑ j, -(P i j * Real.log (P i j)) := by
    simp
  simp_rw [rowScore, shannonEntropy, Real.negMulLog_def,
    Finset.sum_add_distrib]
  rw [hneg]
  ring_nf

/-- Entropy form of the averaged sequential divergence, now proved directly
for the Gibbs law rather than taken as a premise. -/
theorem gibbsSequentialDivergence_eq_entropy
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    gibbsSequentialDivergence A =
      -shannonEntropy (gibbsProbability A) +
        ∑ i, rowScore (assignmentMarginal A i) := by
  unfold gibbsSequentialDivergence averagedSequentialDivergence
  calc
    uniformAverage (fun π : Equiv.Perm (Fin m) ↦
        finiteKL (gibbsProbability A)
          (sequentialLikelihood (assignmentMarginal A) π)) =
        -shannonEntropy (gibbsProbability A) -
          (∑ i, ∑ j, assignmentMarginal A i j *
            Real.log (assignmentMarginal A i j)) +
          ∑ i, rowT (assignmentMarginal A i) :=
      averagedSequentialKL_identity
        (gibbsProbability_pos A hA)
        (assignmentMarginal_strictProbabilityVector A hA)
        (gibbs_hasAssignmentMarginals A)
    _ = -shannonEntropy (gibbsProbability A) +
          ∑ i, rowScore (assignmentMarginal A i) := by
      rw [← neg_logMarginals_add_rowT_eq_rowScore (assignmentMarginal A)]
      ring

theorem gibbsSequentialDivergence_nonneg
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    0 ≤ gibbsSequentialDivergence A := by
  exact averagedSequentialDivergence_nonneg
    (gibbsProbability_isProbabilityVector A hA)
    (gibbsProbability_pos A hA)
    (assignmentMarginal_strictProbabilityVector A hA)

/-- Paper Lemma 6 (exact sequential identity), with every probability and
normalization assertion discharged. -/
theorem gibbs_exact_sequential_identity
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    Real.log (Matrix.permanent A) =
      betheObjective A (assignmentMarginal A) +
        (∑ i, rowCorrection (assignmentMarginal A i)) -
          gibbsSequentialDivergence A := by
  have hGibbs := gibbsEntropy_identity A hA
  have hD := gibbsSequentialDivergence_eq_entropy A hA
  have hBethe := bethe_add_rowCorrection_eq_logWeight_add_rowScore
    A (assignmentMarginal A)
  linarith

/-- Entropy form of the sequential divergence, paper Lemma 10, derived from
the Gibbs entropy identity and the exact sequential identity. -/
theorem entropy_form_of_sequential_identity
    {m : ℕ} (A P : Matrix (Fin m) (Fin m) ℝ)
    {logPermanent divergence gibbsEntropy : ℝ}
    (hGibbs : gibbsEntropy = logPermanent -
      ∑ i, ∑ j, P i j * Real.log (A i j))
    (hseq : logPermanent =
      betheObjective A P + (∑ i, rowCorrection (P i)) - divergence) :
    divergence = -gibbsEntropy + ∑ i, rowScore (P i) := by
  rw [bethe_add_rowCorrection_eq_logWeight_add_rowScore A P] at hseq
  linarith

/-- Slack in the upper half of the Bethe sandwich, in logarithmic
coordinates. -/
noncomputable def betheSlack (n : ℕ) (logBethe logPermanent : ℝ) : ℝ :=
  n * (Real.log 2 / 2) + logBethe - logPermanent

/-- Loss from evaluating the Bethe objective away from its maximizer. -/
def betheSuboptimality (logBethe objectiveValue : ℝ) : ℝ :=
  logBethe - objectiveValue

/-- Paper Lemma 7 is an exact algebraic consequence of Lemma 6.  This version
separates that closed algebra from the probabilistic proof of the sequential
identity. -/
theorem slack_decomposition_of_sequential_identity
    {m : ℕ} (g : Fin m → ℝ)
    {logBethe logPermanent objectiveValue divergence : ℝ}
    (hseq : logPermanent =
      objectiveValue + (∑ i, g i) - divergence) :
    betheSlack m logBethe logPermanent =
      betheSuboptimality logBethe objectiveValue +
        (∑ i, (Real.log 2 / 2 - g i)) + divergence := by
  rw [betheSlack, betheSuboptimality, hseq]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin]
  ring

/-- The same identity in the paper's `rowDeficit` notation. -/
theorem slack_decomposition_rowDeficit
    {m : ℕ} (p : Fin m → Fin m → ℝ)
    {logBethe logPermanent objectiveValue divergence : ℝ}
    (hseq : logPermanent =
      objectiveValue + (∑ i, rowCorrection (p i)) - divergence) :
    betheSlack m logBethe logPermanent =
      betheSuboptimality logBethe objectiveValue +
        (∑ i, rowDeficit (p i)) + divergence := by
  simpa only [rowDeficit] using
    slack_decomposition_of_sequential_identity
      (fun i ↦ rowCorrection (p i)) hseq

theorem terms_le_slack_of_decomposition
    {slack sub row divergence : ℝ}
    (hsub : 0 ≤ sub) (hrow : 0 ≤ row) (hdiv : 0 ≤ divergence)
    (h : slack = sub + row + divergence) :
    sub ≤ slack ∧ row ≤ slack ∧ divergence ≤ slack := by
  subst slack
  constructor
  · linarith
  constructor <;> linarith

end BeyondBethe
