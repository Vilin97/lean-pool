/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ClusterFactors
import LeanPool.BeyondBethe.BeyondBethe.CapacityOrder
import Mathlib.Analysis.MeanInequalities

/-! # Certificate Capacity -/

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

noncomputable def linearCapacityValue
    {ι : Type*} [Fintype ι]
    (u α : ι → ℝ) : ℝ :=
  ∏ i, (u i / α i) ^ (α i)

theorem positiveLinearPolynomial_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u z : ι → ℝ) :
    (positiveLinearPolynomial u).eval z = ∑ i, u i * z i := by
  rw [positiveLinearPolynomial, eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_monomial]
  simp

theorem linearCapacityValue_mul_realMonomial
    {ι : Type*} [Fintype ι]
    {u α z : ι → ℝ}
    (hu : ∀ i, 0 < u i) (hα : ∀ i, 0 < α i)
    (hz : ∀ i, 0 < z i) :
    linearCapacityValue u α * realMonomial z α =
      ∏ i, (u i * z i / α i) ^ (α i) := by
  rw [linearCapacityValue, realMonomial, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.mul_rpow (le_of_lt (div_pos (hu i) (hα i)))
    (le_of_lt (hz i))]
  congr 1
  field_simp

theorem linearCapacityValue_le_ratio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u α z : ι → ℝ}
    (hu : ∀ i, 0 < u i) (hα : ∀ i, 0 < α i)
    (hαsum : ∑ i, α i = 1) (hz : ∀ i, 0 < z i) :
    linearCapacityValue u α ≤
      (positiveLinearPolynomial u).eval z / realMonomial z α := by
  rw [le_div_iff₀ (realMonomial_pos hz α),
    linearCapacityValue_mul_realMonomial hu hα hz,
    positiveLinearPolynomial_eval]
  calc
    (∏ i, (u i * z i / α i) ^ (α i)) ≤
        ∑ i, α i * (u i * z i / α i) := by
          exact Real.geom_mean_le_arith_mean_weighted Finset.univ α
            (fun i ↦ u i * z i / α i)
            (fun i _ ↦ le_of_lt (hα i)) hαsum
            (fun i _ ↦ le_of_lt (div_pos (mul_pos (hu i) (hz i)) (hα i)))
    _ = ∑ i, u i * z i := by
          apply Finset.sum_congr rfl
          intro i _
          field_simp [ne_of_gt (hα i)]

theorem linearCapacityValue_le_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u α : ι → ℝ}
    (hu : ∀ i, 0 < u i) (hα : ∀ i, 0 < α i)
    (hαsum : ∑ i, α i = 1) :
    linearCapacityValue u α ≤
      polynomialCapacity α (positiveLinearPolynomial u) := by
  apply le_polynomialCapacity_of_le_ratio
  intro z hz
  exact linearCapacityValue_le_ratio hu hα hαsum hz

/-- Exact weighted AM--GM capacity of a positive linear form. -/
theorem linearCapacityValue_eq_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u α : ι → ℝ}
    (hu : ∀ i, 0 < u i) (hα : ∀ i, 0 < α i)
    (hαsum : ∑ i, α i = 1) :
    linearCapacityValue u α =
      polynomialCapacity α (positiveLinearPolynomial u) := by
  apply le_antisymm
  · exact linearCapacityValue_le_capacity hu hα hαsum
  · let z : ι → ℝ := fun i ↦ α i / u i
    have hz : ∀ i, 0 < z i := fun i ↦ div_pos (hα i) (hu i)
    have hupper := polynomialCapacity_le_ratio
      (p := positiveLinearPolynomial u)
      (positiveLinearPolynomial_nonnegativeCoefficients
        (fun i ↦ le_of_lt (hu i))) α z hz
    have heval : (positiveLinearPolynomial u).eval z = 1 := by
      rw [positiveLinearPolynomial_eval]
      calc
        (∑ i, u i * z i) = ∑ i, α i := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [z]
          field_simp [ne_of_gt (hu i)]
        _ = 1 := hαsum
    have hterm : ∀ i,
        (z i) ^ (α i) = ((u i / α i) ^ (α i))⁻¹ := by
      intro i
      have hratio : z i = (u i / α i)⁻¹ := by
        dsimp [z]
        field_simp [ne_of_gt (hu i), ne_of_gt (hα i)]
      rw [hratio, Real.inv_rpow (le_of_lt (div_pos (hu i) (hα i)))]
    have hmono : realMonomial z α = (linearCapacityValue u α)⁻¹ := by
      rw [realMonomial, linearCapacityValue]
      simp_rw [hterm]
      exact Finset.prod_inv_distrib _
    rw [heval, hmono, one_div, inv_inv] at hupper
    exact hupper

noncomputable def selectorCapacityValue
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (α : κ × ι → ℝ) : ℝ :=
  ∏ j, linearCapacityValue (fun _ : κ ↦ 1) (fun c ↦ α (c, j))

theorem columnSelector_eval
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ × ι → ℝ) :
    (columnSelector κ ι).eval z = ∏ j, ∑ c, z (c, j) := by
  rw [columnSelector_eq_product, columnSelectorProduct, eval_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [eval_sum]
  simp

theorem realMonomial_eq_prod_columns
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (z α : κ × ι → ℝ) :
    realMonomial z α =
      ∏ j, realMonomial (fun c ↦ z (c, j)) (fun c ↦ α (c, j)) := by
  rw [realMonomial]
  simp only [realMonomial, Fintype.prod_prod_type]
  exact Finset.prod_comm

theorem selectorCapacityValue_mul_realMonomial
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {α : κ × ι → ℝ} {z : κ × ι → ℝ}
    (hα : ∀ v, 0 < α v) (hz : ∀ v, 0 < z v) :
    selectorCapacityValue α * realMonomial z α =
      ∏ j, (linearCapacityValue (fun _ : κ ↦ 1)
          (fun c ↦ α (c, j)) *
        realMonomial (fun c ↦ z (c, j)) (fun c ↦ α (c, j))) := by
  rw [selectorCapacityValue, realMonomial_eq_prod_columns,
    ← Finset.prod_mul_distrib]

theorem selectorCapacityValue_le_ratio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {α : κ × ι → ℝ} {z : κ × ι → ℝ}
    (hα : ∀ v, 0 < α v)
    (hαcol : ∀ j, ∑ c, α (c, j) = 1)
    (hz : ∀ v, 0 < z v) :
    selectorCapacityValue α ≤
      (columnSelector κ ι).eval z / realMonomial z α := by
  rw [le_div_iff₀ (realMonomial_pos hz α), columnSelector_eval,
    selectorCapacityValue_mul_realMonomial hα hz]
  apply Finset.prod_le_prod₀
  · intro j _
    exact mul_nonneg
      (Finset.prod_nonneg fun c _ ↦ Real.rpow_nonneg
        (le_of_lt (div_pos (by norm_num) (hα (c, j)))) _)
      (le_of_lt (realMonomial_pos (fun c ↦ hz (c, j))
        (fun c ↦ α (c, j))))
  · intro j _
    have hlin := linearCapacityValue_le_ratio
      (u := fun _ : κ ↦ 1) (α := fun c ↦ α (c, j))
      (z := fun c ↦ z (c, j))
      (fun _ ↦ by norm_num) (fun c ↦ hα (c, j))
      (hαcol j) (fun c ↦ hz (c, j))
    rw [le_div_iff₀ (realMonomial_pos (fun c ↦ hz (c, j))
      (fun c ↦ α (c, j)))] at hlin
    simpa only [positiveLinearPolynomial_eval, one_mul] using hlin

theorem selectorCapacityValue_le_capacity
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {α : κ × ι → ℝ}
    (hα : ∀ v, 0 < α v)
    (hαcol : ∀ j, ∑ c, α (c, j) = 1) :
    selectorCapacityValue α ≤
      polynomialCapacity α (columnSelector κ ι) := by
  apply le_polynomialCapacity_of_le_ratio
  intro z hz
  exact selectorCapacityValue_le_ratio hα hαcol hz

noncomputable def clusterProductCapacityValue
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (α : C.Cluster × Fin n → ℝ) : ℝ :=
  ∏ c, polynomialCapacity (fun j ↦ α (c, j))
    (injectionPolynomial (fun k j ↦ A (C.rows ⟨c, k⟩) j))

theorem rowClusterProduct_eval_eq_prod_injection
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (z : C.Cluster × Fin n → ℝ) :
    (rowClusterProduct A C).eval z =
      ∏ c, (injectionPolynomial
        (fun k j ↦ A (C.rows ⟨c, k⟩) j)).eval (fun j ↦ z (c, j)) := by
  rw [rowClusterProduct, eval_prod]
  apply Finset.prod_congr rfl
  intro c _
  rw [rowClusterPolynomial_eq_rename_injectionPolynomial,
    eval_rename]
  rfl

theorem realMonomial_eq_prod_clusters
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (z α : κ × ι → ℝ) :
    realMonomial z α =
      ∏ c, realMonomial (fun j ↦ z (c, j)) (fun j ↦ α (c, j)) := by
  rw [realMonomial]
  simp only [realMonomial, Fintype.prod_prod_type]

theorem clusterProductCapacityValue_nonneg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hA : Matrix.Nonnegative A) (α : C.Cluster × Fin n → ℝ) :
    0 ≤ clusterProductCapacityValue A C α := by
  rw [clusterProductCapacityValue]
  exact Finset.prod_nonneg fun c _ ↦ polynomialCapacity_nonneg
    (injectionPolynomial_nonnegativeCoefficients
      (fun k j ↦ hA (C.rows ⟨c, k⟩) j)) _

theorem clusterProductCapacityValue_le_ratio
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hA : Matrix.Nonnegative A) (α : C.Cluster × Fin n → ℝ)
    (z : C.Cluster × Fin n → ℝ) (hz : ∀ v, 0 < z v) :
    clusterProductCapacityValue A C α ≤
      (rowClusterProduct A C).eval z / realMonomial z α := by
  rw [clusterProductCapacityValue,
    rowClusterProduct_eval_eq_prod_injection,
    realMonomial_eq_prod_clusters, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod₀
  · intro c _
    exact polynomialCapacity_nonneg
      (injectionPolynomial_nonnegativeCoefficients
        (fun k j ↦ hA (C.rows ⟨c, k⟩) j)) _
  · intro c _
    exact polynomialCapacity_le_ratio
      (injectionPolynomial_nonnegativeCoefficients
        (fun k j ↦ hA (C.rows ⟨c, k⟩) j))
      (fun j ↦ α (c, j)) (fun j ↦ z (c, j))
      (fun j ↦ hz (c, j))

theorem clusterProductCapacityValue_le_capacity
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hA : Matrix.Nonnegative A) (α : C.Cluster × Fin n → ℝ) :
    clusterProductCapacityValue A C α ≤
      polynomialCapacity α (rowClusterProduct A C) := by
  apply le_polynomialCapacity_of_le_ratio
  intro z hz
  exact clusterProductCapacityValue_le_ratio C hA α z hz

end BeyondBethe
