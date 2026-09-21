/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Transfer
import LeanPool.BeyondBethe.BeyondBethe.Slack
import Mathlib.Tactic

/-! # Transfer Identity -/

open scoped BigOperators

namespace BeyondBethe

/-- The row contribution `h_B` used in the transfer identity. -/
noncomputable def betheEntropyContribution
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  shannonEntropy p + ∑ j, (1 - p j) * Real.log (1 - p j)

/-- Logarithmic form of the KKT factorization.  It is the exact form needed
for the transfer identity; exponentiating the row and column potentials gives
the positive scalings in the paper. -/
def HasLogKKT
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (A X : Matrix ι ι ℝ) (r c : ι → ℝ) : Prop :=
  ∀ i j, Real.log (A i j) = r i + c j +
    (1 + τ) * Real.log (X i j) + Real.log (1 - X i j)

noncomputable def regularizedBetheCoordinate
    (τ a x : ℝ) : ℝ :=
  x * Real.log a + Real.negMulLog x +
    (1 - x) * Real.log (1 - x) + τ * Real.negMulLog x

theorem regularizedBetheObjective_eq_sum_coordinates
    {ι : Type*} [Fintype ι] (τ : ℝ) (A X : Matrix ι ι ℝ) :
    regularizedBetheObjective τ A X =
      ∑ i, ∑ j, regularizedBetheCoordinate τ (A i j) (X i j) := by
  rw [regularizedBetheObjective, betheObjective, totalRowEntropy]
  simp_rw [betheRowObjective, shannonEntropy, regularizedBetheCoordinate]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

theorem betheEntropyContribution_add_regularizer_eq_sum
    {ι : Type*} [Fintype ι] (τ : ℝ) (P : Matrix ι ι ℝ) :
    ∑ i, (betheEntropyContribution (P i) + τ * shannonEntropy (P i)) =
      ∑ i, ∑ j, (Real.negMulLog (P i j) +
        (1 - P i j) * Real.log (1 - P i j) +
        τ * Real.negMulLog (P i j)) := by
  simp_rw [betheEntropyContribution, shannonEntropy, Finset.mul_sum,
    ← Finset.sum_add_distrib]

theorem rowScore_eq_rowCorrection_add_betheEntropyContribution
    {m : ℕ} (p : Fin m → ℝ) :
    rowScore p = rowCorrection p + betheEntropyContribution p := by
  rw [rowScore, rowCorrection, betheEntropyContribution]
  ring

/-- The upper-bound algebra in paper Lemma 16.  The hypotheses name exactly
the three analytic/optimization inputs used in the paper: regularized
suboptimality, the size of the entropy regularizer, and the exact slack
decomposition. -/
theorem global_transfer_upper_of_slack
    {n : ℕ} {τ ξ E Eτ gibbsEntropy divergence slack : ℝ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hEτ : Eτ ≤ E + ξ * n)
    (hregularizer : τ * totalRowEntropy P ≤ ξ * n)
    (hdivergence : divergence =
      -gibbsEntropy + ∑ i, rowScore (P i))
    (hslack : slack = E + (∑ i, rowDeficit (P i)) + divergence) :
    Eτ + ∑ i, (betheEntropyContribution (P i) +
        τ * shannonEntropy (P i)) ≤
      slack + 2 * ξ * n + gibbsEntropy - n * (Real.log 2 / 2) := by
  have hscore : (∑ i, rowScore (P i)) =
      (∑ i, rowCorrection (P i)) +
        ∑ i, betheEntropyContribution (P i) := by
    simp_rw [rowScore_eq_rowCorrection_add_betheEntropyContribution]
    exact Finset.sum_add_distrib
  have hentropy : (∑ i, betheEntropyContribution (P i)) =
      gibbsEntropy + divergence - ∑ i, rowCorrection (P i) := by
    linarith
  have hregularizerSum :
      (∑ i, τ * shannonEntropy (P i)) =
        τ * totalRowEntropy P := by
    rw [totalRowEntropy, Finset.mul_sum]
  have hdeficit : (∑ i, rowDeficit (P i)) =
      n * (Real.log 2 / 2) - ∑ i, rowCorrection (P i) := by
    simp_rw [rowDeficit, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    rw [Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_add_distrib, hentropy, hregularizerSum]
  linarith

theorem neg_regularizedCoordinate_add_entropy
    (τ a x : ℝ) :
    -regularizedBetheCoordinate τ a x +
        (Real.negMulLog x + (1 - x) * Real.log (1 - x) +
          τ * Real.negMulLog x) =
      -x * Real.log a := by
  rw [regularizedBetheCoordinate]
  ring

theorem regularizedCoordinate_of_logKKT
    (τ x R C : ℝ) :
    x * (R + C + (1 + τ) * Real.log x + Real.log (1 - x)) +
        Real.negMulLog x + (1 - x) * Real.log (1 - x) +
        τ * Real.negMulLog x =
      x * (R + C) + Real.log (1 - x) := by
  rw [Real.negMulLog_def]
  ring

theorem rowColumnPotential_sum_eq
    {ι : Type*} [Fintype ι]
    {X P : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    (hP : IsDoublyStochastic P) (r c : ι → ℝ) :
    (∑ i, ∑ j, X i j * (r i + c j)) =
      ∑ i, ∑ j, P i j * (r i + c j) := by
  have hrowX : (∑ i, ∑ j, X i j * r i) = ∑ i, r i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hX.row_sum i, one_mul]
  have hrowP : (∑ i, ∑ j, P i j * r i) = ∑ i, r i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hP.row_sum i, one_mul]
  have hcolX : (∑ i, ∑ j, X i j * c j) = ∑ j, c j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, hX.col_sum j, one_mul]
  have hcolP : (∑ i, ∑ j, P i j * c j) = ∑ j, c j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, hP.col_sum j, one_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  linarith

theorem log_one_div_transferU
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) (j : ι) :
    Real.log (1 / transferU τ p j) =
      -(1 + τ) * Real.log (p j) - Real.log (1 - p j) +
        Real.log (complementProduct p) := by
  rw [transferU_eq_div_complementProduct hp j, one_div_div]
  have hpPow : 0 < (p j) ^ (1 + τ) :=
    Real.rpow_pos_of_pos (hp.2 j).1 _
  have hcomp : 0 < 1 - p j := sub_pos.mpr (hp.2 j).2
  have hq : 0 < complementProduct p := complementProduct_pos hp
  rw [Real.log_div hq.ne' (mul_ne_zero hpPow.ne' hcomp.ne'),
    Real.log_mul hpPow.ne' hcomp.ne', Real.log_rpow (hp.2 j).1]
  ring

/-- Paper Lemma 16, the exact global transfer identity, assuming the KKT
equations.  No optimization theorem or analytic approximation is used in
this algebraic step. -/
theorem global_transfer_identity_of_logKKT
    {n : ℕ} {τ : ℝ} {A X P : Matrix (Fin n) (Fin n) ℝ}
    {r c : Fin n → ℝ}
    (hX : IsDoublyStochastic X) (hP : IsDoublyStochastic P)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hKKT : HasLogKKT τ A X r c) :
    (regularizedBetheObjective τ A X - regularizedBetheObjective τ A P) +
        ∑ i, (betheEntropyContribution (P i) + τ * shannonEntropy (P i)) =
      ∑ i, ∑ j, P i j * Real.log (1 / transferU τ (X i) j) := by
  unfold HasLogKKT at hKKT
  have hPcancel :
      -(∑ i, ∑ j, regularizedBetheCoordinate τ (A i j) (P i j)) +
          ∑ i, ∑ j, (Real.negMulLog (P i j) +
            (1 - P i j) * Real.log (1 - P i j) +
            τ * Real.negMulLog (P i j)) =
        -(∑ i, ∑ j, P i j * Real.log (A i j)) := by
    calc
      -(∑ i, ∑ j, regularizedBetheCoordinate τ (A i j) (P i j)) +
          ∑ i, ∑ j, (Real.negMulLog (P i j) +
            (1 - P i j) * Real.log (1 - P i j) +
            τ * Real.negMulLog (P i j)) =
        ∑ i, ∑ j, (-regularizedBetheCoordinate τ (A i j) (P i j) +
          (Real.negMulLog (P i j) +
            (1 - P i j) * Real.log (1 - P i j) +
            τ * Real.negMulLog (P i j))) := by
          simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      _ = ∑ i, ∑ j, -(P i j * Real.log (A i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [neg_regularizedCoordinate_add_entropy]
        ring
      _ = -(∑ i, ∑ j, P i j * Real.log (A i j)) := by
        simp only [Finset.sum_neg_distrib]
  have hcancel :
      (regularizedBetheObjective τ A X - regularizedBetheObjective τ A P) +
          ∑ i, (betheEntropyContribution (P i) + τ * shannonEntropy (P i)) =
        regularizedBetheObjective τ A X -
          ∑ i, ∑ j, P i j * Real.log (A i j) := by
    rw [regularizedBetheObjective_eq_sum_coordinates,
      regularizedBetheObjective_eq_sum_coordinates,
      betheEntropyContribution_add_regularizer_eq_sum]
    linarith
  have hphiX :
      regularizedBetheObjective τ A X =
        (∑ i, ∑ j, X i j * (r i + c j)) +
          ∑ i, ∑ j, Real.log (1 - X i j) := by
    rw [regularizedBetheObjective_eq_sum_coordinates]
    simp_rw [regularizedBetheCoordinate, hKKT,
      regularizedCoordinate_of_logKKT]
    simp only [Finset.sum_add_distrib]
  have hlogAP :
      (∑ i, ∑ j, P i j * Real.log (A i j)) =
        (∑ i, ∑ j, P i j * (r i + c j)) +
          ∑ i, ∑ j, P i j *
            ((1 + τ) * Real.log (X i j) + Real.log (1 - X i j)) := by
    simp_rw [hKKT]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hpot := rowColumnPotential_sum_eq hX hP r c
  have hq : ∀ i,
      Real.log (complementProduct (X i)) =
        ∑ j, Real.log (1 - X i j) := by
    intro i
    rw [complementProduct, Real.log_prod]
    intro j _
    exact (sub_pos.mpr ((hXint i).2 j).2).ne'
  have hweightedQ :
      (∑ i, ∑ j, P i j * (∑ k, Real.log (1 - X i k))) =
        ∑ i, ∑ k, Real.log (1 - X i k) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hP.row_sum i, one_mul]
  have hcostNeg :
      (∑ i, ∑ j, P i j *
        (-(1 + τ) * Real.log (X i j) - Real.log (1 - X i j))) =
      -(∑ i, ∑ j, P i j *
        ((1 + τ) * Real.log (X i j) + Real.log (1 - X i j))) := by
    calc
      (∑ i, ∑ j, P i j *
        (-(1 + τ) * Real.log (X i j) - Real.log (1 - X i j))) =
        ∑ i, ∑ j, -(P i j *
          ((1 + τ) * Real.log (X i j) + Real.log (1 - X i j))) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = -(∑ i, ∑ j, P i j *
        ((1 + τ) * Real.log (X i j) + Real.log (1 - X i j))) := by
          simp only [Finset.sum_neg_distrib]
  have htransferCost :
      (∑ i, ∑ j, P i j * Real.log (1 / transferU τ (X i) j)) =
        -(∑ i, ∑ j, P i j *
          ((1 + τ) * Real.log (X i j) + Real.log (1 - X i j))) +
          ∑ i, ∑ k, Real.log (1 - X i k) := by
    calc
      (∑ i, ∑ j, P i j * Real.log (1 / transferU τ (X i) j)) =
          ∑ i, ∑ j, P i j *
            (-(1 + τ) * Real.log (X i j) - Real.log (1 - X i j) +
              Real.log (complementProduct (X i))) := by
        simp_rw [log_one_div_transferU (hXint _)]
      _ = (∑ i, ∑ j, P i j *
            (-(1 + τ) * Real.log (X i j) - Real.log (1 - X i j))) +
          ∑ i, ∑ j, P i j * Real.log (complementProduct (X i)) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ = -(∑ i, ∑ j, P i j *
            ((1 + τ) * Real.log (X i j) + Real.log (1 - X i j))) +
          ∑ i, ∑ k, Real.log (1 - X i k) := by
        rw [hcostNeg]
        simp_rw [hq]
        rw [hweightedQ]
  rw [hcancel, hphiX, hlogAP, htransferCost]
  linarith

/-- Paper Lemma 16 in its upper-bound form, with the KKT and slack inputs
kept explicit. -/
theorem global_transfer_upper_of_logKKT_and_slack
    {n : ℕ} {τ ξ E gibbsEntropy divergence slack : ℝ}
    {A X P : Matrix (Fin n) (Fin n) ℝ} {r c : Fin n → ℝ}
    (hX : IsDoublyStochastic X) (hP : IsDoublyStochastic P)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hKKT : HasLogKKT τ A X r c)
    (hEτ : regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A P ≤ E + ξ * n)
    (hregularizer : τ * totalRowEntropy P ≤ ξ * n)
    (hdivergence : divergence =
      -gibbsEntropy + ∑ i, rowScore (P i))
    (hslack : slack = E + (∑ i, rowDeficit (P i)) + divergence) :
    ∑ i, ∑ j, P i j * Real.log (1 / transferU τ (X i) j) ≤
      slack + 2 * ξ * n + gibbsEntropy - n * (Real.log 2 / 2) := by
  rw [← global_transfer_identity_of_logKKT hX hP hXint hKKT]
  exact global_transfer_upper_of_slack P hEτ hregularizer
    hdivergence hslack

end BeyondBethe
