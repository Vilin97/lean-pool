/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.AffineDisk
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleAuxiliary
public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanion
public import LeanPool.OperatorTheory.Operator.Crouzeix.SpectralAuxiliaryCenter
public import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann

/-!
# The scalar Crouzeix companion on a disk

On a circle, conjugating a polynomial turns every positive centered monomial
into a negative Laurent mode.  Consequently, the scalar Cauchy companion is
constant throughout the disk: only the conjugate value at the center
survives.

Rather than duplicate the Laurent-series calculation, this file realizes an
interior scalar `z` as the one-dimensional multiplication operator on `ℂ`.
The exact operator circle-auxiliary identity then gives the scalar result after
passing the contour integral through evaluation at `1`.  A small resolvent
lemma identifies that evaluated operator kernel with `(sigma - z)⁻¹`.

This supplies an unconditional model of the companion construction,
continuous extension, and sharp contraction.  The corresponding assertions
for a general smooth convex boundary still require the Plemelj argument.

## Main declarations

* `crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center` -- the exact
  constant value of the companion in an arbitrary disk.
* `crouzeixPolynomialScalarCompanion_ball_eq_eval_zero` -- its centered form.
* `norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall`
  -- sharp contraction on an arbitrary closed disk.
* `norm_crouzeixPolynomialScalarCompanion_ball_le_polynomialSupNorm_closedBall`
  -- the centered contraction.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

/-- For every interior point of a disk, the scalar Crouzeix companion is the
constant `star (p.eval c)`, where `c` is the center. -/
theorem crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z =
      star (Polynomial.eval c p) := by
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ z
  have hAc : ‖A - c • (1 : ℂ →L[ℂ] ℂ)‖ < R := by
    have heq : A - c • (1 : ℂ →L[ℂ] ℂ) =
        ContinuousLinearMap.toSpanSingleton ℂ (z - c) := by
      apply ContinuousLinearMap.ext
      intro x
      change x * z - c * x = x * (z - c)
      ring
    rw [heq, ContinuousLinearMap.norm_toSpanSingleton]
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  calc
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p 1 :=
      crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
        (SmoothJordanDomain.ball c R hR) p hz
    _ = (star (Polynomial.eval c p) • (1 : ℂ →L[ℂ] ℂ)) 1 := by
      rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
        A c hAc p]
    _ = star (Polynomial.eval c p) := by
      change star (Polynomial.eval c p) * (1 : ℂ) = _
      rw [mul_one]

/-- For every interior point of a centered disk, the scalar Crouzeix
companion is the constant `star (p.eval 0)`. -/
theorem crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball 0 R hR) p z =
      star (Polynomial.eval 0 p) :=
  crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center 0 hR p hz

/-- The scalar companion on an arbitrary disk is contractive for the
polynomial sup norm on the corresponding closed disk. -/
theorem
    norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    ‖crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) := by
  rw [crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center c hR p hz,
    norm_star]
  exact norm_eval_le_polynomialSupNorm p
    (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
    (Metric.mem_closedBall_self hR.le)

/-- The scalar companion on a centered disk is contractive for the polynomial
sup norm on the closed disk. -/
theorem norm_crouzeixPolynomialScalarCompanion_ball_le_polynomialSupNorm_closedBall
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball 0 R hR) p z‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
  exact
    norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall
      0 hR p hz

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
