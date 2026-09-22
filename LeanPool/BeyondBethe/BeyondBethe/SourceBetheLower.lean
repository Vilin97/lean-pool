/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ClusterCertificate
import LeanPool.BeyondBethe.BeyondBethe.Optimizer

/-! # Source Bethe Lower -/

open scoped BigOperators

namespace BeyondBethe

/-!
# The lower half of the Bethe sandwich

The stable-coefficient theorem contains Gurvits's Bethe lower bound as the
special case in which every row is a singleton cluster.  This file makes that
reduction explicit.  Once the stable-coefficient theorem is closed, there is
no separate Schrijver/Gurvits interface left in the development.
-/

/-- The clustering with one named singleton cluster for each row. -/
noncomputable def singletonRowClustering (n : ℕ) : RowClustering n where
  Cluster := Fin n
  clusterFintype := inferInstance
  clusterDecidableEq := inferInstance
  size := fun _ ↦ 1
  rows := Equiv.sigmaUnique (Fin n) (fun _ ↦ Fin 1)

@[simp] theorem singletonRowClustering_size (n : ℕ)
    (i : (singletonRowClustering n).Cluster) :
    (singletonRowClustering n).size i = 1 := rfl

@[simp] theorem singletonRowClustering_rows (n : ℕ)
    (s : Σ c : (singletonRowClustering n).Cluster,
      Fin ((singletonRowClustering n).size c)) :
    (singletonRowClustering n).rows s = s.1 := by
  rfl

theorem singletonRowClustering_singletonPairs (n : ℕ) :
    IsSingletonPairClustering (singletonRowClustering n) := by
  intro i
  exact Or.inl rfl

@[simp] theorem singletonClusterRow_singletonRowClustering
    {n : ℕ} (i : Fin n) :
    singletonClusterRow (singletonRowClustering n) i rfl = i := by
  rfl

theorem paperClusterFactor_singletonRowClustering
    {n : ℕ} (hn : 2 ≤ n)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A) (hX : IsDoublyStochastic X)
    (hXpos : ∀ i j, 0 < X i j) (i : Fin n) :
    paperClusterFactor A X (singletonRowClustering n)
        (singletonRowClustering_singletonPairs n) i =
      singletonFactor A X i := by
  unfold paperClusterFactor
  rw [dif_pos (show (singletonRowClustering n).size i = 1 from rfl)]
  rfl

/-- Gurvits's pointwise Bethe lower certificate, obtained from the
stable-coefficient theorem with singleton clusters. -/
theorem exp_betheObjective_le_permanent_of_stableCoefficient
    {n : ℕ} (hn : 2 ≤ n)
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A) (hX : IsDoublyStochastic X)
    (hXpos : ∀ i j, 0 < X i j) :
    Real.exp (betheObjective A X) ≤ Matrix.permanent A := by
  have hcert := pairedLowerCertificate_for_clustering stableCoefficient
    (singletonRowClustering n) hn hA hX hXpos
    (singletonRowClustering_singletonPairs n)
  rw [← prod_singletonFactor_eq_exp_betheObjective]
  calc
    (∏ i, singletonFactor A X i) =
        ∏ i, paperClusterFactor A X (singletonRowClustering n)
          (singletonRowClustering_singletonPairs n) i := by
            apply Finset.prod_congr rfl
            intro i _
            exact (paperClusterFactor_singletonRowClustering hn hA hX hXpos i).symm
    _ ≤ Matrix.permanent A := hcert

/-- The lower half of the Bethe sandwich for positive matrices. -/
theorem bethePermanent_le_permanent_of_positive
    {n : ℕ} (hn : 2 ≤ n)
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.Positive A) :
    bethePermanent A ≤ Matrix.permanent A := by
  have hper : 0 < Matrix.permanent A := permanent_pos_of_positive A hA
  have hlog : betheLogValue A ≤ Real.log (Matrix.permanent A) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let C : ℝ := n * Real.log n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg n)
      (Real.log_nonneg hn1)
    let τ : ℝ := ε / (C + 1)
    have hτ : 0 < τ := div_pos hε (by linarith)
    obtain ⟨X, hX, hmax⟩ := exists_regularizedBetheMaximizer τ A
    have hXpos := regularizedBetheMaximizer_positive
      (show 1 < n by omega) hτ hA hX hmax
    have hvalue := betheLogValue_le_regularizedMaximizer
      (show 1 < n by omega) hτ.le hA hX hmax
    have hcert := exp_betheObjective_le_permanent_of_stableCoefficient
      hn stableCoefficient hA hX hXpos
    have hobjective : betheObjective A X ≤
        Real.log (Matrix.permanent A) :=
      (Real.le_log_iff_exp_le hper).mpr hcert
    have hbudget : τ * C ≤ ε := by
      dsimp only [τ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < C + 1)]
      nlinarith
    dsimp only [C] at hvalue hbudget
    linarith
  have hmatch : Matrix.HasPerfectMatching A := positiveMatrix_hasPerfectMatching hA
  rw [bethePermanent, ite_eq_left hmatch]
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hper] at hexp

end BeyondBethe
