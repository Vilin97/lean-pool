/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.AffineAuxiliary
public import LeanPool.OperatorTheory.Operator.NumericalRange.Bounded
public import LeanPool.OperatorTheory.Operator.SpectralSet.Normal
public import LeanPool.OperatorTheory.Operator.SpectralSet.SpectrumInNR

/-!
# The auxiliary product bound for aligned circles and normal polynomial values

The fixed-domain auxiliary product estimate against the closed numerical
range is false for arbitrary containing circles: an off-center contour can
sample `p` at a point unrelated to the control set.  This file records a
correct strengthened branch.  If the individual value `p(A)` is star-normal
and the circle center belongs to `closure (numericalRange A)`, spectral
calculus controls `p(A)` by the numerical-range sup norm, while center
membership controls the scalar value appearing in the affine-circle
auxiliary identity.

## Main declarations

* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval`
  proves the literal L4.2e product conclusion when the individual value
  `p(A)` is star-normal.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal`
  specializes the result to a star-normal operator.
-/

@[expose] public section

open Complex Polynomial Set
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- If the individual value `p(A)` is star-normal, an enclosing circle centered
at a point of the closed numerical range satisfies the sharp auxiliary product
bound with the closed numerical range itself as control set. -/
theorem
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hc : c ∈ closure (numericalRange A)) (p : Polynomial ℂ)
    [IsStarNormal (Polynomial.aeval A p)] :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m := polynomialSupNorm p (closure (numericalRange A))
  have hcompact : IsCompact (closure (numericalRange A)) :=
    (isBounded_numericalRange A).isCompact_closure
  have hpA : ‖Polynomial.aeval A p‖ ≤ m :=
    norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval A hcompact
      (spectrum_subset_closure_numericalRange A) p
  have hpc : ‖Polynomial.eval c p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hcompact) hc
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA p]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval c p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval c p) • (1 : E →L[ℂ] E)‖ :=
      norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * ‖Polynomial.eval c p‖ := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ m * m :=
      mul_le_mul hpA hpc (norm_nonneg _)
        ((norm_nonneg _).trans hpA)
    _ = polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
      rw [pow_two]

/-- For a star-normal operator, an enclosing circle centered at a point of
the closed numerical range satisfies the sharp auxiliary product bound with
the closed numerical range itself as control set. -/
theorem
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hc : c ∈ closure (numericalRange A)) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  have hnormal : IsStarNormal (Polynomial.aeval A p) := by
    rw [← cfc_polynomial p A]
    exact cfc_predicate _ A
  let _ := hnormal
  exact
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval
      A c hA hc p

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
