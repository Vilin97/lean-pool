/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ClusterFactors
import LeanPool.BeyondBethe.BeyondBethe.Birkhoff
import Mathlib.Tactic

/-! # Cluster Alpha -/

open scoped BigOperators

namespace BeyondBethe

/-- The total `X`-mass which a row cluster sends to a column.  This is the
vector `alpha` used when the stable coefficient inequality is applied to the
cluster polynomial and the column selector. -/
noncomputable def clusterAlpha
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    C.Cluster × Fin n → ℝ :=
  fun v ↦ ∑ k, X (C.rows ⟨v.1, k⟩) v.2

theorem clusterAlpha_nonnegative
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : IsDoublyStochastic X) (v : C.Cluster × Fin n) :
    0 ≤ clusterAlpha X C v := by
  rw [clusterAlpha]
  exact Finset.sum_nonneg fun k _ ↦ hX.nonnegative (C.rows ⟨v.1, k⟩) v.2

theorem clusterAlpha_pos
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : ∀ i j, 0 < X i j) {c : C.Cluster} (hc : 0 < C.size c)
    (j : Fin n) :
    0 < clusterAlpha X C (c, j) := by
  rw [clusterAlpha]
  letI : Nonempty (Fin (C.size c)) := ⟨⟨0, hc⟩⟩
  exact Finset.sum_pos
    (fun k _ ↦ hX (C.rows ⟨c, k⟩) j)
    Finset.univ_nonempty

theorem clusterAlpha_row_sum
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : IsDoublyStochastic X) (c : C.Cluster) :
    ∑ j, clusterAlpha X C (c, j) = C.size c := by
  change ∑ j, ∑ k, X (C.rows ⟨c, k⟩) j = C.size c
  rw [Finset.sum_comm]
  simp_rw [hX.row_sum]
  simp

theorem clusterAlpha_col_sum
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : IsDoublyStochastic X) (j : Fin n) :
    ∑ c, clusterAlpha X C (c, j) = 1 := by
  change ∑ c, ∑ k, X (C.rows ⟨c, k⟩) j = 1
  rw [← Fintype.sum_sigma']
  calc
    (∑ s : Σ c, Fin (C.size c), X (C.rows s) j) =
        ∑ i, X i j := Equiv.sum_comp C.rows (fun i ↦ X i j)
    _ = 1 := hX.col_sum j

theorem clusterAlpha_le_one
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : IsDoublyStochastic X) (c : C.Cluster) (j : Fin n) :
    clusterAlpha X C (c, j) ≤ 1 := by
  let e : Fin (C.size c) → (Σ d, Fin (C.size d)) := fun k ↦ ⟨c, k⟩
  have he : Function.Injective e := by
    intro k l h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hslice :
      clusterAlpha X C (c, j) =
        ∑ s ∈ (Finset.univ.image e), X (C.rows s) j := by
    rw [clusterAlpha, Finset.sum_image he.injOn]
  rw [hslice, ← hX.col_sum j]
  calc
    (∑ s ∈ (Finset.univ.image e), X (C.rows s) j) ≤
        ∑ s : Σ d, Fin (C.size d), X (C.rows s) j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun s _ _ ↦ hX.nonnegative (C.rows s) j)
    _ = ∑ i, X i j := Equiv.sum_comp C.rows (fun i ↦ X i j)

theorem clusterAlpha_total_sum
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : IsDoublyStochastic X) :
    ∑ v, clusterAlpha X C v = n := by
  rw [Fintype.sum_prod_type]
  simp_rw [clusterAlpha_row_sum C hX]
  exact_mod_cast sum_clusterSizes_eq C

theorem clusterAlpha_in_unit_interval
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : IsDoublyStochastic X) (v : C.Cluster × Fin n) :
    0 ≤ clusterAlpha X C v ∧ clusterAlpha X C v ≤ 1 := by
  exact ⟨clusterAlpha_nonnegative C hX v,
    clusterAlpha_le_one C hX v.1 v.2⟩

theorem clusterAlpha_pos_of_singletonPairs
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hX : ∀ i j, 0 < X i j) (hclusters : IsSingletonPairClustering C)
    (v : C.Cluster × Fin n) :
    0 < clusterAlpha X C v := by
  apply clusterAlpha_pos C hX (c := v.1)
  rcases hclusters v.1 with h | h <;> omega

end BeyondBethe
