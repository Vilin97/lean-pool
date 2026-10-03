/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ODE
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Finite coefficient matrices as continuous linear maps

A Galerkin weak form starts as a finite matrix of scalar time coefficients. This module assembles
those entries as a bounded operator on the real `PiLp` coefficient space and transfers entrywise
a.e. strong measurability to that operator-valued coefficient.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace AVenhance.Infra.Parabolic.FourierGalerkin

variable {n : ℕ}

/-- The rank-one coefficient map that sends coordinate `j` to coordinate `i`. -/
def matrixRankOne (i j : Fin n) : Coefficients n →L[ℝ] Coefficients n :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).smulRight
    (PiLp.single 2 (β := fun _ : Fin n => ℝ) i (1 : ℝ))

/-- Assemble a scalar real matrix as an operator on the Euclidean coefficient space. -/
def matrixCoefficientCLM (A : Fin n → Fin n → ℝ) :
    Coefficients n →L[ℝ] Coefficients n :=
  ∑ i, ∑ j, A i j • matrixRankOne i j

@[simp]
theorem matrixRankOne_apply (i j : Fin n) (c : Coefficients n) :
    matrixRankOne i j c = c j • PiLp.single 2 (β := fun _ : Fin n => ℝ) i (1 : ℝ) := by
  simp [matrixRankOne]

@[simp]
theorem matrixCoefficientCLM_apply (A : Fin n → Fin n → ℝ) (c : Coefficients n)
    (i : Fin n) :
    matrixCoefficientCLM A c i = ∑ j, A i j * c j := by
  classical
  simp [matrixCoefficientCLM, matrixRankOne, PiLp.proj_apply,
    ContinuousLinearMap.smulRight_apply, Pi.single_apply]

theorem MatrixOperator.matrixProjection_norm_le (j : Fin n) :
    ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff
    (f := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j) (by norm_num)]
  intro c
  rw [PiLp.proj_apply]
  simpa using PiLp.norm_apply_le c j

theorem MatrixOperator.matrixRankOne_norm_le (i j : Fin n) :
    ‖matrixRankOne i j‖ ≤ 1 := by
  rw [matrixRankOne, ContinuousLinearMap.norm_smulRight_apply]
  have hs : ‖PiLp.single 2 (β := fun _ : Fin n => ℝ) i (1 : ℝ)‖ = 1 := by
    simp [PiLp.norm_single]
  calc
    ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j‖ *
        ‖PiLp.single 2 (β := fun _ : Fin n => ℝ) i (1 : ℝ)‖ ≤ 1 * 1 := by
      exact mul_le_mul (MatrixOperator.matrixProjection_norm_le j) hs.le (norm_nonneg _) (by
          norm_num)
    _ = 1 := by norm_num

/-- The matrix operator norm is at most the sum of the absolute values of its entries. -/
theorem matrixCoefficientCLM_norm_le (A : Fin n → Fin n → ℝ) :
    ‖matrixCoefficientCLM A‖ ≤ ∑ i, ∑ j, |A i j| := by
  classical
  calc
    ‖matrixCoefficientCLM A‖ ≤ ∑ i, ‖∑ j, A i j • matrixRankOne i j‖ := by
      simp only [matrixCoefficientCLM]
      exact norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖A i j • matrixRankOne i j‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, |A i j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖A i j • matrixRankOne i j‖ = |A i j| * ‖matrixRankOne i j‖ := norm_smul _ _
        _ ≤ |A i j| := by
          exact mul_le_of_le_one_right (abs_nonneg _) (MatrixOperator.matrixRankOne_norm_le i j)

/-- A uniform scalar bound on every matrix entry gives a dimension-explicit operator bound. -/
theorem matrixCoefficientCLM_norm_le_uniform (A : Fin n → Fin n → ℝ) {K : ℝ}
    (hA : ∀ i j, |A i j| ≤ K) :
    ‖matrixCoefficientCLM A‖ ≤ (n : ℝ) ^ 2 * K := by
  classical
  calc
    ‖matrixCoefficientCLM A‖ ≤ ∑ i, ∑ j, |A i j| := matrixCoefficientCLM_norm_le A
    _ ≤ ∑ i : Fin n, ∑ _j : Fin n, K := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hA i j
    _ = (n : ℝ) ^ 2 * K := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem MatrixOperator.aestronglyMeasurable_finset_sum {ι : Type*} {β : Type*}
    [NormedAddCommGroup β] {μ : Measure ℝ}
    (s : Finset ι) (f : ι → ℝ → β)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun t => ∑ i ∈ s, f i t) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact aestronglyMeasurable_const
  | @insert a s ha ih =>
    have heq : (fun t => ∑ i ∈ insert a s, f i t) =
        fun t => f a t + ∑ i ∈ s, f i t := by
      funext t
      exact Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Entrywise a.e. strong measurability passes to the finite operator matrix. -/
theorem matrixCoefficientCLM_aestronglyMeasurable
    {A : ℝ → Fin n → Fin n → ℝ} {μ : Measure ℝ}
    (hA : ∀ i j, AEStronglyMeasurable (fun t => A t i j) μ) :
    AEStronglyMeasurable (fun t => matrixCoefficientCLM (A t)) μ := by
  classical
  have hrow (i : Fin n) :
      AEStronglyMeasurable (fun t => ∑ j, A t i j • matrixRankOne i j) μ := by
    apply MatrixOperator.aestronglyMeasurable_finset_sum Finset.univ
    intro j hj
    exact (hA i j).smul_const (matrixRankOne i j)
  apply MatrixOperator.aestronglyMeasurable_finset_sum Finset.univ
  intro i hi
  exact hrow i

end AVenhance.Infra.Parabolic.FourierGalerkin

end
