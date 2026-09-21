/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Affine-disk Crouzeix--Palencia inequality

This file transports the centered unit-disk Crouzeix--Palencia estimate to
an arbitrary enclosing disk by the usual affine normalization.

## Main declaration

* `norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_sub_smul_one_lt`
  -- the unconditional polynomial bound on an arbitrary open operator-norm disk.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.AffineDisk
import LeanPool.OperatorTheory.Operator.Crouzeix.CircleSymmetrized

open scoped InnerProductSpace Polynomial

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- **Affine-disk Crouzeix--Palencia inequality.** If `A - cI` has norm strictly less than
`R`, polynomial evaluation at `A` is bounded by `(1 + √2)` times the polynomial sup-norm
on `closedBall c R`. -/
theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_sub_smul_one_lt
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) := by
  have hR : 0 < R := (norm_nonneg (A - c • (1 : E →L[ℂ] E))).trans_lt hA
  let T : E →L[ℂ] E := ((R : ℂ)⁻¹) • (A - c • 1)
  let q : ℂ[X] := p.affineComposition (R : ℂ) c
  have hT : ‖T‖ < 1 := by
    dsimp only [T]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact (inv_mul_lt_one₀ hR).mpr hA
  have hEval : Polynomial.aeval T q = Polynomial.aeval A p := by
    dsimp only [q]
    rw [Polynomial.aeval_affineComposition]
    congr 1
    dsimp only [T]
    rw [smul_smul]
    have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [mul_inv_cancel₀ hR0, one_smul, sub_add_cancel]
  calc
    ‖Polynomial.aeval A p‖ = ‖Polynomial.aeval T q‖ := congrArg norm hEval.symm
    _ ≤ (1 + Real.sqrt 2) *
        polynomialSupNorm q (Metric.closedBall (0 : ℂ) 1) :=
      norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt T hT q
    _ = (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) := by
      rw [polynomialSupNorm_affineComposition_closedBall p c hR.le]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
