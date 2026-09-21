/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.AffinePolynomial
import LeanPool.OperatorTheory.Operator.Crouzeix.AuxOperator
import LeanPool.OperatorTheory.Operator.Crouzeix.CircleAuxiliary
import LeanPool.OperatorTheory.Operator.Crouzeix.CircleCauchy

/-!
# Affine transport of the polynomial auxiliary operator

Translation of the circle center is accompanied by translation of the
operator and precomposition of the polynomial.  The parameterized auxiliary
contour is unchanged under these three simultaneous operations.

## Main declaration

* `crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift` --
  transports the auxiliary operator from `ball c R` to the centered ball,
  given the explicit translated-resolvent identity.
* `crouzeixPolynomialAuxiliaryOperator_ball_center` -- the unconditional
  transport identity, using the resolvent translation formula.
* `crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one` -- the resulting
  scalar auxiliary identity on an arbitrary enclosing disk.
-/

open Complex MeasureTheory
open scoped InnerProductSpace Interval Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The polynomial auxiliary contour on `ball c R` agrees with the centered
contour for `A - cI` and the translated polynomial `z ↦ p(z + c)`, provided
the corresponding translated-resolvent identity is available. -/
theorem crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ)
    (hshift : ∀ z : ℂ, resolvent (A - c • (1 : E →L[ℂ] E)) z =
      resolvent A (z + c)) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      crouzeixPolynomialAuxiliaryOperator
        (A - c • (1 : E →L[ℂ] E)) (SmoothJordanDomain.ball 0 R hR)
          (p.affineComposition 1 c) := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change deriv (circleMap c R) t •
      (star (Polynomial.eval (circleMap c R t) p) •
        resolvent A (circleMap c R t)) =
    deriv (circleMap 0 R) t •
      (star (Polynomial.eval (circleMap 0 R t) (p.affineComposition 1 c)) •
        resolvent (A - c • (1 : E →L[ℂ] E)) (circleMap 0 R t))
  have hmap : circleMap c R t = circleMap 0 R t + c := by
    rw [← circleMap_sub_center c R t]
    ring
  have hderiv : deriv (circleMap c R) t = deriv (circleMap 0 R) t := by
    rw [deriv_circleMap, deriv_circleMap]
  rw [hderiv, hmap, hshift, Polynomial.eval_affineComposition, one_mul]

/-- Translating the circle center, the operator, and the polynomial leaves
the polynomial auxiliary contour operator unchanged. -/
theorem crouzeixPolynomialAuxiliaryOperator_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      crouzeixPolynomialAuxiliaryOperator
        (A - c • (1 : E →L[ℂ] E)) (SmoothJordanDomain.ball 0 R hR)
          (p.affineComposition 1 c) :=
  crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
    A c hR p (resolvent_sub_smul_one_shift A c)

variable [CompleteSpace E]

/-- If `‖A - cI‖ < R`, the polynomial auxiliary operator on the disk centered at `c` is the
constant operator `star (p.eval c) • 1`. -/
theorem crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R ((norm_nonneg (A - c • 1)).trans_lt hA)) p =
      star (Polynomial.eval c p) • (1 : E →L[ℂ] E) := by
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center]
  rw [crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one
    (A - c • (1 : E →L[ℂ] E)) hA]
  simp only [Polynomial.eval_affineComposition, one_mul, zero_add]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
