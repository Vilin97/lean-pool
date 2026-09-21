/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Affine-disk support for the Crouzeix--Palencia product bound

Once the polynomial auxiliary operator on a circle centered at `c` is the
scalar operator `star (p(c)) • 1`, the sharp L4.2e product estimate follows
from von Neumann's inequality on that disk and the scalar sup-norm bound at
its center.

## Main declaration

* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one`
  -- the sharp product estimate on an arbitrary positive-radius disk from
  the explicit scalar auxiliary identity.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le` -- the unconditional
  arbitrary-center disk estimate under strict operator-norm enclosure.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.AffineAuxiliary
import LeanPool.OperatorTheory.Operator.Crouzeix.AffineDisk

open Complex Polynomial Set
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- On a disk centered at `c`, the scalar auxiliary identity
`G = star (p(c)) • 1` implies the sharp L4.2e product estimate. -/
theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ ≤ R) (p : Polynomial ℂ)
    (hG : crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      star (Polynomial.eval c p) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m := polynomialSupNorm p (Metric.closedBall c R)
  have hpA : ‖Polynomial.aeval A p‖ ≤ m :=
    norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le A c hR hA p
  have hpc : ‖Polynomial.eval c p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
      (Metric.mem_closedBall_self hR.le)
  rw [hG]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval c p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval c p) • (1 : E →L[ℂ] E)‖ := norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * ‖Polynomial.eval c p‖ := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ m * m := mul_le_mul hpA hpc (norm_nonneg _) ((norm_nonneg _).trans hpA)
    _ = polynomialSupNorm p (Metric.closedBall c R) ^ 2 := by
      simp only [m, pow_two]

/-- **Affine-disk L4.2e product bound.** If `‖A - cI‖ < R`, the actual polynomial auxiliary
operator on `ball c R` satisfies the sharp squared sup-norm estimate. -/
theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) ^ 2 :=
  norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
    A c ((norm_nonneg (A - c • 1)).trans_lt hA) hA.le p
      (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one A c hA p)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
