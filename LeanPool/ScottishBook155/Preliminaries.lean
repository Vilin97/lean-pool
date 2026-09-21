/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.Paper1

/-!
# Fixed short scale implies global nonexpansiveness

This module formalizes the line-segment subdivision argument from the
preliminaries of `paper1`.
-/

namespace ScottishBook155

open AffineMap

theorem dist_image_le_of_subdivision
    {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [PseudoMetricSpace N]
    {r : ℝ} {V : M → N} (hshort : PreservesUpTo r V)
    {x y : M} (n : ℕ) (hn : 0 < n) (hstep : dist x y / (n : ℝ) ≤ r) :
    dist (V x) (V y) ≤ dist x y := by
  let z : ℕ → M := fun k => lineMap x y ((k : ℝ) / (n : ℝ))
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  have hz0 : z 0 = x := by simp [z]
  have hzn : z n = y := by simp [z, hnreal]
  have hzstep (k : ℕ) : dist (z k) (z (k + 1)) = dist x y / (n : ℝ) := by
    dsimp only [z]
    rw [dist_lineMap_lineMap]
    rw [Real.dist_eq, abs_of_nonpos]
    · field_simp [hnreal]
      norm_num [Nat.cast_add, Nat.cast_one]
    · have hnposreal : 0 < (n : ℝ) := by positivity
      have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ k
      exact sub_nonpos.mpr (div_le_div_of_nonneg_right hk hnposreal.le)
  calc
    dist (V x) (V y) = dist (V (z 0)) (V (z n)) := by rw [hz0, hzn]
    _ ≤ ∑ k ∈ Finset.range n, dist (V (z k)) (V (z (k + 1))) :=
      dist_le_range_sum_dist (fun k => V (z k)) n
    _ = ∑ k ∈ Finset.range n, dist (z k) (z (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply hshort
      rw [hzstep]
      exact hstep
    _ = ∑ _k ∈ Finset.range n, (dist x y / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact hzstep k
    _ = dist x y := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hnreal]

theorem preservesUpTo_nonexpansive
    {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [PseudoMetricSpace N]
    {r : ℝ} (hr : 0 < r) {V : M → N} (hshort : PreservesUpTo r V) :
    ∀ x y, dist (V x) (V y) ≤ dist x y := by
  intro x y
  obtain ⟨n, hn⟩ := exists_nat_gt (dist x y / r)
  have hratio_nonneg : 0 ≤ dist x y / r := div_nonneg dist_nonneg hr.le
  have hnpos : 0 < n := by
    exact_mod_cast lt_of_le_of_lt hratio_nonneg hn
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hdist_lt : dist x y < (n : ℝ) * r := (div_lt_iff₀ hr).mp hn
  have hstep : dist x y / (n : ℝ) ≤ r := by
    apply le_of_lt
    apply (div_lt_iff₀ hnrealpos).2
    simpa [mul_comm] using hdist_lt
  exact dist_image_le_of_subdivision hshort n hnpos hstep

end ScottishBook155
