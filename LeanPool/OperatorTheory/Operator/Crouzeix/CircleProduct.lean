/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.AffinePolynomial
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleAuxiliary
public import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Circle-model support for the Crouzeix--Palencia product bound

This file supplies the operator-norm assembly for L4.2e on a centered disk.
First, affine polynomial transport scales von Neumann's inequality from the
unit disk to `closedBall 0 R`.  Second, if the polynomial auxiliary operator
on the enclosing circle has been identified with
`star (p.eval 0) • 1`, submultiplicativity gives the sharp product estimate.

The auxiliary identification is deliberately an explicit hypothesis: it is
the conjugate-boundary circle Cauchy calculation, separate from the norm
assembly proved here.

## Main declarations

* `norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le` -- von Neumann's
  inequality on a centered disk of positive radius.
* `norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one`
  -- the sharp circle-model product estimate from the scalar auxiliary
  identification.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le` -- the sharp
  product estimate for the actual centered-disk auxiliary operator.
-/

@[expose] public section

open Complex Polynomial Set
open scoped InnerProductSpace Pointwise

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Von Neumann's inequality scaled from the unit disk to a centered disk:
if `‖A‖ ≤ R` and `0 < R`, then polynomial evaluation at `A` is bounded by
the polynomial sup norm on `closedBall 0 R`. -/
theorem norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le
    (A : E →L[ℂ] E) {R : ℝ} (hR : 0 < R) (hA : ‖A‖ ≤ R)
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
  let T : E →L[ℂ] E := (R : ℂ)⁻¹ • A
  let q := p.affineComposition (R : ℂ) 0
  have hT : ‖T‖ ≤ 1 := by
    dsimp only [T]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (inv_mul_le_one₀ hR).mpr hA
  have hEval : Polynomial.aeval T q = Polynomial.aeval A p := by
    dsimp only [q]
    rw [Polynomial.aeval_affineComposition]
    dsimp only [T]
    simp only [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne'), one_smul,
      zero_smul, add_zero]
  have hImage : ((fun z : ℂ => (R : ℂ) * z + 0) ''
      Metric.closedBall (0 : ℂ) 1) = Metric.closedBall (0 : ℂ) R := by
    simp only [add_zero, ← smul_eq_mul, Set.image_smul, smul_unitClosedBall,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  calc
    ‖Polynomial.aeval A p‖ = ‖Polynomial.aeval T q‖ := congrArg norm hEval.symm
    _ ≤ polynomialSupNorm q (Metric.closedBall (0 : ℂ) 1) :=
      vonNeumann_inequality T hT q
    _ = polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
      dsimp only [q]
      rw [polynomialSupNorm_affineComposition_image, hImage]

/-- On a centered disk, the scalar auxiliary identification
`G = star (p.eval 0) • 1` implies the sharp L4.2e product estimate.  The
subsingleton branch makes the result valid for the zero Hilbert space, where
the continuous-linear-map algebra does not have `NormOneClass`. -/
theorem norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
    (A : E →L[ℂ] E) {R : ℝ} (hR : 0 < R) (hA : ‖A‖ ≤ R)
    (p : Polynomial ℂ) (G : E →L[ℂ] E)
    (hG : G = star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p * G‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p * G = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m := polynomialSupNorm p (Metric.closedBall (0 : ℂ) R)
  have hpA : ‖Polynomial.aeval A p‖ ≤ m :=
    norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le A hR hA p
  have hp0 : ‖Polynomial.eval 0 p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall (0 : ℂ) R))
      (Metric.mem_closedBall_self hR.le)
  rw [hG]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E)‖ := norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * ‖Polynomial.eval 0 p‖ := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ m * m := mul_le_mul hpA hp0 (norm_nonneg _) ((norm_nonneg _).trans hpA)
    _ = polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 := by
      simp only [m, pow_two]

/-- **Centered-disk L4.2e product bound.**  For `‖A‖ < R`, the actual
conjugate-polynomial auxiliary operator on `ball 0 R` satisfies the sharp
product estimate. -/
theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 :=
  norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
    A ((norm_nonneg A).trans_lt hR) hR.le p _
      (crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one A hR p)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
