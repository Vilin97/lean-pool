/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Entropy
import Mathlib.Tactic

/-! # Gibbs -/

open scoped BigOperators

namespace BeyondBethe

/-- Weight of a permutation in the permanent expansion.  Mathlib's permanent
uses columns as the domain of the permutation and rows as its image. -/
noncomputable def permutationWeight
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (σ : Equiv.Perm n) : ℝ :=
  ∏ j, A (σ j) j

theorem sum_permutationWeight_eq_permanent
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    ∑ σ : Equiv.Perm n, permutationWeight A σ = Matrix.permanent A := by
  rfl

/-- The unnormalized Gibbs marginal that row `i` is matched to column `j`. -/
noncomputable def marginalNumerator
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i j : n) : ℝ :=
  ∑ σ : Equiv.Perm n, if σ j = i then permutationWeight A σ else 0

/-- Assignment marginals of the Gibbs law. -/
noncomputable def assignmentMarginal
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i j : n) : ℝ :=
  marginalNumerator A i j / Matrix.permanent A

theorem sum_marginalNumerator_col
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (j : n) :
    ∑ i, marginalNumerator A i j = Matrix.permanent A := by
  classical
  simp_rw [marginalNumerator]
  rw [Finset.sum_comm]
  calc
    (∑ σ : Equiv.Perm n,
        ∑ i : n, if σ j = i then permutationWeight A σ else 0)
        = ∑ σ : Equiv.Perm n, permutationWeight A σ := by
          apply Finset.sum_congr rfl
          intro σ _
          simp
    _ = Matrix.permanent A := sum_permutationWeight_eq_permanent A

theorem sum_marginalNumerator_row
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i : n) :
    ∑ j, marginalNumerator A i j = Matrix.permanent A := by
  classical
  simp_rw [marginalNumerator]
  rw [Finset.sum_comm]
  calc
    (∑ σ : Equiv.Perm n,
        ∑ j : n, if σ j = i then permutationWeight A σ else 0)
        = ∑ σ : Equiv.Perm n, permutationWeight A σ := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.sum_eq_single (σ.symm i)]
          · simp
          · intro j _ hj
            have hne : σ j ≠ i := by
              intro hji
              apply hj
              simpa using congrArg σ.symm hji
            simp [hne]
          · simp
    _ = Matrix.permanent A := sum_permutationWeight_eq_permanent A

theorem assignmentMarginal_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Matrix.Nonnegative A)
    (i j : n) :
    0 ≤ assignmentMarginal A i j := by
  unfold assignmentMarginal marginalNumerator
  exact div_nonneg
    (Finset.sum_nonneg fun σ _ ↦ by
      split_ifs
      · exact Finset.prod_nonneg fun k _ ↦ hA (σ k) k
      · rfl)
    (Matrix.permanent_nonneg_real A hA)

theorem assignmentMarginal_row_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hper : Matrix.permanent A ≠ 0) (i : n) :
    ∑ j, assignmentMarginal A i j = 1 := by
  simp_rw [assignmentMarginal]
  rw [← Finset.sum_div, sum_marginalNumerator_row]
  exact div_self hper

theorem assignmentMarginal_col_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hper : Matrix.permanent A ≠ 0) (j : n) :
    ∑ i, assignmentMarginal A i j = 1 := by
  simp_rw [assignmentMarginal]
  rw [← Finset.sum_div, sum_marginalNumerator_col]
  exact div_self hper

theorem assignmentMarginal_doublyStochastic
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Matrix.Nonnegative A)
    (hper : Matrix.permanent A ≠ 0) :
    IsDoublyStochastic (assignmentMarginal A) := by
  exact ⟨assignmentMarginal_nonneg A hA,
    assignmentMarginal_row_sum A hper,
    assignmentMarginal_col_sum A hper⟩

/-- Gibbs probability of a permutation. -/
noncomputable def gibbsProbability
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (σ : Equiv.Perm n) : ℝ :=
  permutationWeight A σ / Matrix.permanent A

theorem permutationWeight_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j)
    (σ : Equiv.Perm n) :
    0 < permutationWeight A σ := by
  rw [permutationWeight]
  exact Finset.prod_pos fun j _ ↦ hA (σ j) j

theorem permanent_pos_of_positive
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j) :
    0 < Matrix.permanent A := by
  rw [← sum_permutationWeight_eq_permanent A]
  exact Finset.sum_pos (fun σ _ ↦ permutationWeight_pos A hA σ)
    ⟨Equiv.refl n, Finset.mem_univ _⟩

theorem assignmentMarginal_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j)
    (i j : n) :
    0 < assignmentMarginal A i j := by
  have hper := permanent_pos_of_positive A hA
  apply div_pos _ hper
  rw [marginalNumerator]
  apply Finset.sum_pos'
  · intro σ _
    split_ifs
    · exact (permutationWeight_pos A hA σ).le
    · rfl
  · refine ⟨Equiv.swap j i, Finset.mem_univ _, ?_⟩
    simp only [Equiv.swap_apply_left, ite_eq_left]
    exact permutationWeight_pos A hA (Equiv.swap j i)

theorem assignmentMarginal_strictProbabilityVector
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j) (i : n) :
    IsStrictProbabilityVector (assignmentMarginal A i) := by
  have hper := permanent_pos_of_positive A hA
  exact ⟨
    (assignmentMarginal_doublyStochastic A
      (fun r c ↦ (hA r c).le) hper.ne').row_probability i,
    assignmentMarginal_pos A hA i⟩

theorem gibbsProbability_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j)
    (σ : Equiv.Perm n) :
    0 < gibbsProbability A σ := by
  exact div_pos (permutationWeight_pos A hA σ)
    (permanent_pos_of_positive A hA)

theorem gibbsProbability_isProbabilityVector
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j) :
    IsProbabilityVector (gibbsProbability A) := by
  constructor
  · intro σ
    exact (gibbsProbability_pos A hA σ).le
  · simp_rw [gibbsProbability]
    rw [← Finset.sum_div,
      sum_permutationWeight_eq_permanent,
      div_self (permanent_pos_of_positive A hA).ne']

theorem assignmentMarginal_eq_gibbs_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i j : n) :
    assignmentMarginal A i j =
      ∑ σ : Equiv.Perm n,
        if σ j = i then gibbsProbability A σ else 0 := by
  unfold assignmentMarginal marginalNumerator gibbsProbability
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

/-- Expectation under a column marginal, written either over rows or over
permutations. -/
theorem assignmentMarginal_expectation_col
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (f : n → ℝ) (j : n) :
    ∑ i, assignmentMarginal A i j * f i =
      ∑ σ : Equiv.Perm n, gibbsProbability A σ * f (σ j) := by
  classical
  simp_rw [assignmentMarginal_eq_gibbs_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_eq_single (σ j)]
  · simp
  · intro i _ hi
    have hne : σ j ≠ i := Ne.symm hi
    simp [hne]
  · simp

theorem log_permutationWeight
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j)
    (σ : Equiv.Perm n) :
    Real.log (permutationWeight A σ) =
      ∑ j, Real.log (A (σ j) j) := by
  rw [permutationWeight, Real.log_prod]
  intro j _
  exact (hA (σ j) j).ne'

/-- Entropy identity for the Gibbs law, used in paper Lemma 10. -/
theorem gibbsEntropy_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 < A i j) :
    shannonEntropy (gibbsProbability A) =
      Real.log (Matrix.permanent A) -
        ∑ i, ∑ j, assignmentMarginal A i j * Real.log (A i j) := by
  have hper : 0 < Matrix.permanent A := permanent_pos_of_positive A hA
  have hμsum := (gibbsProbability_isProbabilityVector A hA).sum_eq_one
  have hentry : ∀ σ : Equiv.Perm n,
      Real.negMulLog (gibbsProbability A σ) =
        gibbsProbability A σ * Real.log (Matrix.permanent A) -
          gibbsProbability A σ * Real.log (permutationWeight A σ) := by
    intro σ
    have hw := permutationWeight_pos A hA σ
    simp only [Real.negMulLog_def]
    rw [gibbsProbability, Real.log_div hw.ne' hper.ne']
    ring
  rw [shannonEntropy]
  simp_rw [hentry]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
  simp_rw [log_permutationWeight A hA, Finset.mul_sum]
  apply congrArg (fun x ↦ Real.log (Matrix.permanent A) - x)
  calc
    ∑ σ, ∑ j, gibbsProbability A σ * Real.log (A (σ j) j) =
        ∑ j, ∑ σ, gibbsProbability A σ * Real.log (A (σ j) j) :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, assignmentMarginal A i j * Real.log (A i j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (assignmentMarginal_expectation_col A
        (fun i ↦ Real.log (A i j)) j).symm
    _ = ∑ i, ∑ j, assignmentMarginal A i j * Real.log (A i j) :=
      Finset.sum_comm

end BeyondBethe
