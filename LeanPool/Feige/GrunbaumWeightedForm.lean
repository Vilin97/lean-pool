/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Constants
import LeanPool.Feige.GrunbaumImport

/-!
# Weighted halfspaces on the Euclidean standard simplex

This file aligns the weighted linear form used in Feige's simplex argument
with the positive-dimensional Euclidean model used by the Grünbaum
formalization.
-/

open scoped BigOperators
open Set

namespace Feige

noncomputable section

/-- The weighted coordinate functional on Mathlib's Euclidean-space model. -/
def euclideanSimplexLinearForm {n : ℕ} (y : Fin n → ℝ) :
    Grunbaum.SimplexE n →L[ℝ] ℝ :=
  ∑ i, y i • (EuclideanSpace.proj i :
    Grunbaum.SimplexE n →L[ℝ] ℝ)

@[simp]
theorem euclideanSimplexLinearForm_apply {n : ℕ}
    (y : Fin n → ℝ) (x : Grunbaum.SimplexE n) :
    euclideanSimplexLinearForm y x = ∑ i, y i * x i := by
  simp [euclideanSimplexLinearForm]

theorem euclideanSimplexLinearForm_comp_simplexToEuclidean
    {n : ℕ} (y x : Fin n → ℝ) :
    euclideanSimplexLinearForm y (simplexToEuclidean n x) =
      simplexLinearForm y x := by
  simp [simplexLinearForm]

theorem euclideanSimplexLinearForm_ne_zero_of_sum_pos
    {n : ℕ} {y : Fin n → ℝ} (hy : 0 < ∑ i, y i) :
    euclideanSimplexLinearForm y ≠ 0 := by
  intro hzero
  have hcoord : ∀ i, y i = 0 := by
    intro i
    have happ := congrArg
      (fun L : Grunbaum.SimplexE n →L[ℝ] ℝ ↦
        L (EuclideanSpace.single i 1)) hzero
    simpa [euclideanSimplexLinearForm, PiLp.single_apply] using happ
  have : (∑ i, y i) = 0 := by simp [hcoord]
  linarith

/-- The weighted form evaluated at the standard-simplex volume centroid. -/
theorem euclideanSimplexLinearForm_centroid
    {n : ℕ} (y : Fin n → ℝ) :
    euclideanSimplexLinearForm y (Grunbaum.simplexCentroid n) =
      (∑ i, y i) / ((n : ℝ) + 1) := by
  rw [euclideanSimplexLinearForm_apply]
  simp_rw [Grunbaum.simplexCentroid_apply n]
  rw [div_eq_mul_inv, Finset.sum_mul]

/-- In dimension `d + 1`, the `δ = 1` large-sum hypothesis in §2.2 puts
the simplex centroid in the upper halfspace `1 ≤ L_y`. -/
theorem one_le_euclideanSimplexLinearForm_centroid
    {d : ℕ} (y : Fin (d + 1) → ℝ)
    (hsum : ((d + 1 : ℕ) : ℝ) + 1 ≤ ∑ i, y i) :
    1 ≤ euclideanSimplexLinearForm y
      (Grunbaum.simplexFullBody d).centroid := by
  rw [Grunbaum.simplexFullBody_centroid,
    euclideanSimplexLinearForm_centroid]
  exact (le_div_iff₀ (by positivity :
    0 < (((d + 1 : ℕ) : ℝ) + 1))).2 (by simpa using hsum)

theorem grunbaumConstant_eq_sharpConstant (d : ℕ) :
    Grunbaum.grunbaumConstant d = sharpConstant (d + 1) := by
  simp only [Grunbaum.grunbaumConstant, sharpConstant, Nat.cast_add,
    Nat.cast_one]
  congr 1
  ring

end

end Feige
