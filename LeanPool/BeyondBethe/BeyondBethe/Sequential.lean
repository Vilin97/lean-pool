/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Gibbs
public import LeanPool.BeyondBethe.BeyondBethe.Transfer
public import LeanPool.BeyondBethe.BeyondBethe.SequentialNormalization
public import Mathlib.Tactic

/-! # Sequential -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- A distribution on Mathlib permutations has row-column marginals `P` in
the orientation `σ column = row`. -/
def HasAssignmentMarginals
    {n : ℕ} (μ : Equiv.Perm (Fin n) → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, P i j = ∑ σ, if σ j = i then μ σ else 0

theorem gibbs_hasAssignmentMarginals
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    HasAssignmentMarginals (gibbsProbability A) (assignmentMarginal A) := by
  intro i j
  exact assignmentMarginal_eq_gibbs_sum A i j

/-- The column ordering induced by a row ordering `π` and a matching `σ`.
Mathlib represents `σ` from columns to rows, hence the inverse here. -/
def inducedColumnOrder
    {n : ℕ} (π σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.trans σ.symm

/-- For a fixed row order, sending a matching to its induced column order is
a bijection. -/
def inducedColumnOrderEquiv
    {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := inducedColumnOrder π σ
  invFun θ := θ.symm.trans π
  left_inv σ := by
    ext i
    simp [inducedColumnOrder, Equiv.trans_apply]
  right_inv θ := by
    ext i
    simp [inducedColumnOrder, Equiv.trans_apply]

theorem orderedSuffixWeight_eq_suffixMass
    {n : ℕ} (W : Fin n → Fin n → ℝ)
    (θ : Equiv.Perm (Fin n)) (t : Fin n) :
    orderedSuffixWeight W θ t = suffixMass (W t) θ (θ t) := by
  rw [suffixMass, ← Equiv.sum_comp θ]
  simp [orderedSuffixWeight]

/-- Likelihood of a matching under the sequential experiment for a fixed row
ordering. -/
noncomputable def sequentialLikelihood
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (π σ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i, P i (σ.symm i) /
    suffixMass (P i) (inducedColumnOrder π σ) (σ.symm i)

/-- The paper's row-indexed formula is exactly the canonical sequential
likelihood after reindexing the rows by `π`. -/
theorem sequentialLikelihood_eq_ordered
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (π σ : Equiv.Perm (Fin n)) :
    sequentialLikelihood P π σ =
      orderedSequentialLikelihood
        (fun t j ↦ P (π t) j) (inducedColumnOrder π σ) := by
  rw [sequentialLikelihood, orderedSequentialLikelihood,
    ← Equiv.prod_comp π]
  apply Finset.prod_congr rfl
  intro t _
  change P (π t) (σ.symm (π t)) /
      suffixMass (P (π t)) (inducedColumnOrder π σ)
        (σ.symm (π t)) =
    P (π t) ((inducedColumnOrder π σ) t) /
      orderedSuffixWeight (fun s j ↦ P (π s) j)
        (inducedColumnOrder π σ) t
  rw [orderedSuffixWeight_eq_suffixMass]
  rfl

theorem sequentialLikelihood_pos
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (π σ : Equiv.Perm (Fin n)) :
    0 < sequentialLikelihood P π σ := by
  rw [sequentialLikelihood]
  apply Finset.prod_pos
  intro i _
  exact div_pos ((hP i).2 (σ.symm i))
    (suffixMass_pos (hP i).1 ((hP i).2 (σ.symm i)) _)

/-- For every fixed row order, the sequential likelihood is a probability
vector.  This closes the normalization that is implicit in the paper's
description of the sequential experiment. -/
theorem sequentialLikelihood_isProbabilityVector
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (π : Equiv.Perm (Fin n)) :
    IsProbabilityVector (sequentialLikelihood P π) := by
  constructor
  · intro σ
    exact (sequentialLikelihood_pos hP π σ).le
  · simp_rw [sequentialLikelihood_eq_ordered]
    calc
      ∑ σ : Equiv.Perm (Fin n),
          orderedSequentialLikelihood (fun t j ↦ P (π t) j)
            (inducedColumnOrder π σ) =
          ∑ θ : Equiv.Perm (Fin n),
            orderedSequentialLikelihood (fun t j ↦ P (π t) j) θ :=
        Equiv.sum_comp (inducedColumnOrderEquiv π)
          (orderedSequentialLikelihood (fun t j ↦ P (π t) j))
      _ = 1 := orderedSequentialLikelihood_sum_eq_one n
        (fun t j ↦ P (π t) j) (fun t j ↦ (hP (π t)).2 j)

theorem finiteKL_sequential_nonneg
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    {p : Equiv.Perm (Fin n) → ℝ}
    (hp : IsProbabilityVector p) (hppos : ∀ σ, 0 < p σ)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (π : Equiv.Perm (Fin n)) :
    0 ≤ finiteKL p (sequentialLikelihood P π) :=
  finiteKL_nonneg hp (sequentialLikelihood_isProbabilityVector hP π)
    hppos (sequentialLikelihood_pos hP π)

theorem log_sequentialLikelihood
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (π σ : Equiv.Perm (Fin n)) :
    Real.log (sequentialLikelihood P π σ) =
      ∑ i, (Real.log (P i (σ.symm i)) -
        Real.log (suffixMass (P i) (inducedColumnOrder π σ) (σ.symm i))) := by
  rw [sequentialLikelihood, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_div ((hP i).2 (σ.symm i)).ne'
      (suffixMass_pos (hP i).1 ((hP i).2 (σ.symm i)) _).ne']
  · intro i _
    exact (div_pos ((hP i).2 (σ.symm i))
      (suffixMass_pos (hP i).1 ((hP i).2 (σ.symm i)) _)).ne'

/-- Right composition by a fixed permutation is a bijection on orderings. -/
def permTransEquiv {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun (π : Equiv.Perm (Fin n)) := π.trans τ
  invFun (θ : Equiv.Perm (Fin n)) := θ.trans τ.symm
  left_inv π := by
    ext i
    simp [Equiv.trans_apply]
  right_inv θ := by
    ext i
    simp [Equiv.trans_apply]

theorem uniformAverage_perm_trans
    {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ)
    (τ : Equiv.Perm (Fin n)) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦ f (π.trans τ)) = uniformAverage f := by
  rw [uniformAverage, uniformAverage]
  congr 1
  exact (permTransEquiv τ).sum_comp f

/-- Averaging an induced column ordering over uniform row orderings gives the
uniform average over column orderings. -/
theorem average_induced_suffix
    {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    uniformAverage (fun π ↦
      Real.log (suffixMass p (inducedColumnOrder π σ) j)) =
    uniformAverage (fun θ ↦ Real.log (suffixMass p θ j)) := by
  exact uniformAverage_perm_trans
    (fun θ ↦ Real.log (suffixMass p θ j)) σ.symm

theorem uniformAverage_const {α : Type*} [Fintype α] [Nonempty α]
    (c : ℝ) : uniformAverage (fun _ : α ↦ c) = c := by
  rw [uniformAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [Fintype.card_ne_zero]

theorem uniformAverage_sub
    {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage (fun x ↦ f x - g x) =
      uniformAverage f - uniformAverage g := by
  simp [uniformAverage, Finset.sum_sub_distrib, sub_div]

theorem uniformAverage_add
    {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage (fun x ↦ f x + g x) =
      uniformAverage f + uniformAverage g := by
  simp [uniformAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_sum
    {α ι : Type*} [Fintype α] [Fintype ι]
    (f : α → ι → ℝ) :
    uniformAverage (fun x ↦ ∑ i, f x i) =
      ∑ i, uniformAverage (fun x ↦ f x i) := by
  rw [uniformAverage]
  simp_rw [uniformAverage, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem uniformAverage_const_mul
    {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformAverage (fun x ↦ c * f x) = c * uniformAverage f := by
  simp [uniformAverage, ← Finset.mul_sum, mul_div_assoc]

theorem uniformAverage_nonneg
    {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ uniformAverage f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ ↦ hf x) (Nat.cast_nonneg _)

/-- Marginal expectation for the column assigned to a fixed row. -/
theorem marginal_expectation_row
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P)
    (i : Fin n) (f : Fin n → ℝ) :
    ∑ σ, μ σ * f (σ.symm i) = ∑ j, P i j * f j := by
  classical
  simp_rw [hmarg i, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp
  · intro j _ hj
    have hne : σ j ≠ i := by
      intro h
      apply hj
      simpa using congrArg σ.symm h
    simp [hne]
  · simp

/-- Rewriting `T(p)` by first fixing the sampled coordinate and then
averaging the ordering. -/
theorem rowT_eq_sum_mul_average_suffix
    {n : ℕ} (p : Fin n → ℝ) :
    rowT p = ∑ j, p j * uniformAverage (fun θ : Equiv.Perm (Fin n) ↦
      Real.log (suffixMass p θ j)) := by
  unfold rowT uniformAverage
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  ring

/-- The expected log numerator of the sequential likelihood is determined by
the assignment marginals. -/
theorem expected_log_sequential_numerator
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P) :
    ∑ σ, μ σ * (∑ i, Real.log (P i (σ.symm i))) =
      ∑ i, ∑ j, P i j * Real.log (P i j) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact marginal_expectation_row hmarg i (fun j ↦ Real.log (P i j))

/-- Averaging the log denominators in the sequential likelihood gives the
sum of the row suffix scores. -/
theorem averaged_log_sequential_denominator
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
      ∑ σ, μ σ * (∑ i,
        Real.log (suffixMass (P i) (inducedColumnOrder π σ) (σ.symm i)))) =
      ∑ i, rowT (P i) := by
  rw [uniformAverage_sum]
  simp_rw [uniformAverage_const_mul, uniformAverage_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have havg : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n),
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass (P i) (inducedColumnOrder π σ) (σ.symm i))) =
      uniformAverage (fun θ : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass (P i) θ (σ.symm i))) :=
    fun σ i ↦ average_induced_suffix (P i) σ (σ.symm i)
  simp_rw [havg]
  apply Finset.sum_congr rfl
  intro i _
  let f : Fin n → ℝ := fun j ↦
    uniformAverage (fun θ : Equiv.Perm (Fin n) ↦
      Real.log (suffixMass (P i) θ j))
  calc
    ∑ σ, μ σ * uniformAverage (fun θ : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass (P i) θ (σ.symm i))) =
        ∑ j, P i j * f j := marginal_expectation_row hmarg i f
    _ = rowT (P i) := (rowT_eq_sum_mul_average_suffix (P i)).symm

/-- Exact entropy expansion of the averaged sequential KL divergence. -/
theorem averagedSequentialKL_identity
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hμpos : ∀ σ, 0 < μ σ)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (hmarg : HasAssignmentMarginals μ P) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
      finiteKL μ (sequentialLikelihood P π)) =
      -shannonEntropy μ - (∑ i, ∑ j, P i j * Real.log (P i j)) +
        ∑ i, rowT (P i) := by
  have hKL : ∀ π : Equiv.Perm (Fin n),
      finiteKL μ (sequentialLikelihood P π) =
        -shannonEntropy μ -
          ∑ σ, μ σ * Real.log (sequentialLikelihood P π σ) := by
    intro π
    exact finiteKL_eq_neg_entropy_sub hμpos
      (sequentialLikelihood_pos hP π)
  have hlog : uniformAverage (fun π : Equiv.Perm (Fin n) ↦
      ∑ σ, μ σ * Real.log (sequentialLikelihood P π σ)) =
      (∑ i, ∑ j, P i j * Real.log (P i j)) - ∑ i, rowT (P i) := by
    have hpoint : ∀ π : Equiv.Perm (Fin n),
        (∑ σ, μ σ * Real.log (sequentialLikelihood P π σ)) =
          (∑ σ, μ σ * (∑ i, Real.log (P i (σ.symm i)))) -
            ∑ σ, μ σ * (∑ i,
              Real.log (suffixMass (P i)
                (inducedColumnOrder π σ) (σ.symm i))) := by
      intro π
      calc
        ∑ σ, μ σ * Real.log (sequentialLikelihood P π σ) =
            ∑ σ, μ σ * (∑ i,
              (Real.log (P i (σ.symm i)) -
                Real.log (suffixMass (P i)
                  (inducedColumnOrder π σ) (σ.symm i)))) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [log_sequentialLikelihood hP]
        _ = (∑ σ, μ σ * (∑ i, Real.log (P i (σ.symm i)))) -
              ∑ σ, μ σ * (∑ i,
                Real.log (suffixMass (P i)
                  (inducedColumnOrder π σ) (σ.symm i))) := by
          simp_rw [Finset.sum_sub_distrib, mul_sub,
            Finset.sum_sub_distrib]
    simp_rw [hpoint]
    rw [uniformAverage_sub,
      uniformAverage_const,
      averaged_log_sequential_denominator hmarg,
      expected_log_sequential_numerator hmarg]
  simp_rw [hKL]
  rw [uniformAverage_sub, uniformAverage_const, hlog]
  ring

/-- Average divergence between a target law and the sequential laws over all
row orderings. -/
noncomputable def averagedSequentialDivergence
    {n : ℕ} (μ : Equiv.Perm (Fin n) → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  uniformAverage (fun π : Equiv.Perm (Fin n) ↦
    finiteKL μ (sequentialLikelihood P π))

theorem averagedSequentialDivergence_nonneg
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    {p : Equiv.Perm (Fin n) → ℝ}
    (hp : IsProbabilityVector p) (hppos : ∀ σ, 0 < p σ)
    (hP : ∀ i, IsStrictProbabilityVector (P i)) :
    0 ≤ averagedSequentialDivergence p P := by
  apply uniformAverage_nonneg
  intro π
  exact finiteKL_sequential_nonneg hp hppos hP π

end BeyondBethe
