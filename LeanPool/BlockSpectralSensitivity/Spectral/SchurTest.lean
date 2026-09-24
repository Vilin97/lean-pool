/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Schur test for the L2 operator norm

General real-matrix lemmas about the L2 operator norm, used in Section 11.3 of `bs_lambda.txt`,
where the oriented overlap matrix `R` is bounded through `‖R‖₂ ≤ sqrt (‖R‖₁ ‖R‖∞)`, i.e. by the
geometric mean of the maximum column sum and the maximum row sum.

Nothing here mentions the Boolean cube: every statement is about an arbitrary real matrix, and
none of them was found in Mathlib.  Mathlib's scoped `Matrix.Norms.L2Operator` norm has no
transpose lemma, no converse of `Matrix.l2_opNorm_mulVec` from which to deduce an operator
bound, no `l1_opNorm`, and no Schur test.  These are therefore upstream candidates rather than
duplicates, and are stated in the `Matrix` namespace accordingly.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}

/-- Over `ℝ` the transpose coincides with the conjugate transpose, so it preserves the L2
operator norm. -/
theorem l2_opNorm_transpose [DecidableEq m] (A : Matrix m n ℝ) : ‖Aᵀ‖ = ‖A‖ := by
  rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]

/-- Converse of `Matrix.l2_opNorm_mulVec`: if every Euclidean vector `v` satisfies
`‖A *ᵥ v‖ ≤ C * ‖v‖`, then the L2 operator norm of `A` is at most `C`.  This is the entry point
for the Schur test of Section 11.3 of `bs_lambda.txt`. -/
theorem l2_opNorm_le_of_norm_mulVec_le (A : Matrix m n ℝ) (hC : 0 ≤ C)
    (h : ∀ v : EuclideanSpace ℝ n, ‖(EuclideanSpace.equiv m ℝ).symm (A *ᵥ v)‖ ≤ C * ‖v‖) :
    ‖A‖ ≤ C := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hC h

/-- Sum-level form of `Matrix.l2_opNorm_le_of_norm_mulVec_le`: it suffices to bound
`∑ i, (A *ᵥ v) i ^ 2` by `C ^ 2 * ∑ j, v j ^ 2` for every plain vector `v`.  Used for the Schur
test in Section 11.3 of `bs_lambda.txt`. -/
theorem l2_opNorm_le_of_sum_sq_mulVec_le (A : Matrix m n ℝ) (hC : 0 ≤ C)
    (h : ∀ v : n → ℝ, ∑ i, (A *ᵥ v) i ^ 2 ≤ C ^ 2 * ∑ j, v j ^ 2) :
    ‖A‖ ≤ C :=
  l2_opNorm_le_of_norm_mulVec_le A hC fun v ↦
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg v))).mp <| by
      simpa [EuclideanSpace.norm_sq_eq, mul_pow] using h _

/-- Sum form of `Matrix.l2_opNorm_mulVec`: the defining operator bound, with both norms
squared and written out as sums. -/
theorem sum_sq_mulVec_le (A : Matrix m n ℝ) (v : n → ℝ) :
    ∑ i, (A *ᵥ v) i ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, v j ^ 2 := by
  have h := l2_opNorm_mulVec A ((EuclideanSpace.equiv n ℝ).symm v)
  simpa [mul_pow, EuclideanSpace.norm_sq_eq, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **Schur test.**  For a matrix `R` with nonnegative entries whose row sums are bounded by `a`
and whose column sums are bounded by `b`, the L2 operator norm satisfies `‖R‖ ≤ sqrt (a * b)`.
This is the "standard induced-norm inequality" `‖R‖₂ ≤ sqrt (‖R‖₁ ‖R‖∞)` invoked at the end of
Section 11.3 of `bs_lambda.txt`. -/
theorem l2_opNorm_le_sqrt_of_row_col_sums (R : Matrix m n ℝ) (hR : ∀ i j, 0 ≤ R i j) {a b : ℝ}
    (hrow : ∀ i, ∑ j, R i j ≤ a) (hcol : ∀ j, ∑ i, R i j ≤ b) :
    ‖R‖ ≤ Real.sqrt (a * b) := by
  -- If either index type is empty then `R` vanishes and the bound is trivial; otherwise a
  -- single row and a single column witness `0 ≤ a` and `0 ≤ b`.
  rcases isEmpty_or_nonempty m with hm | hm
  · simp [Subsingleton.elim R 0]
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Subsingleton.elim R 0]
  obtain ⟨i₀⟩ := hm
  obtain ⟨j₀⟩ := hn
  have ha : 0 ≤ a := (Finset.sum_nonneg fun j _ ↦ hR i₀ j).trans (hrow i₀)
  have hb : 0 ≤ b := (Finset.sum_nonneg fun i _ ↦ hR i j₀).trans (hcol j₀)
  refine l2_opNorm_le_of_sum_sq_mulVec_le R (Real.sqrt_nonneg _) fun v ↦ ?_
  rw [Real.sq_sqrt (mul_nonneg ha hb)]
  -- Cauchy-Schwarz row by row, with the weights `R i ·`.
  have step (i : m) : (R *ᵥ v) i ^ 2 ≤ a * ∑ j, R i j * v j ^ 2 :=
    (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ ↦ hR i j)
      (fun j _ ↦ mul_nonneg (hR i j) (sq_nonneg _)) fun j _ ↦ le_of_eq (by ring)).trans <|
      mul_le_mul_of_nonneg_right (hrow i) <|
        Finset.sum_nonneg fun j _ ↦ mul_nonneg (hR i j) (sq_nonneg _)
  calc ∑ i, (R *ᵥ v) i ^ 2
      ≤ ∑ i, a * ∑ j, R i j * v j ^ 2 := Finset.sum_le_sum fun i _ ↦ step i
    _ = a * ∑ j, (∑ i, R i j) * v j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ ≤ a * ∑ j, b * v j ^ 2 := by
        gcongr with j
        exact hcol j
    _ = a * b * ∑ j, v j ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

end Matrix
