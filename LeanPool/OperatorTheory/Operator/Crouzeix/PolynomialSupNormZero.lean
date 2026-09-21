/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# The zero case for polynomial sup norms on infinite compact sets

Normalization arguments for the Crouzeix--Palencia auxiliary estimates divide
by the polynomial sup norm.  This file isolates the complementary zero case:
a polynomial whose sup norm on an infinite compact subset of the complex plane
is zero must itself be zero.  Positive-radius closed disks are recorded as the
principal geometric specialization.

## Main declarations

* `polynomial_eq_zero_of_polynomialSupNorm_eq_zero` -- vanishing of the sup
  norm on an infinite compact set forces the polynomial to vanish.
* `polynomial_eq_zero_of_polynomialSupNorm_closedBall_eq_zero` -- the closed
  disk specialization.
* `polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite` --
  normalized sharp auxiliary bounds extend to every polynomial on an infinite
  compact set.
* `polynomial_auxiliary_bounds_of_normalized_closedBall` -- normalized sharp
  auxiliary bounds imply the corresponding bounds for every polynomial on a
  nondegenerate closed disk, including the zero sup-norm case.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.PalenciaSupport
import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset

open Polynomial ContinuousLinearMap

universe u

/-- A closed disk of positive radius contains infinitely many points. -/
private theorem infinite_closedBall_of_pos (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (Metric.closedBall c R).Infinite := by
  have hball : (Metric.ball c R).Infinite := by
    apply Set.Infinite.of_accPt
    exact Metric.isOpen_ball.preperfect c (Metric.mem_ball_self hR)
  exact hball.mono Metric.ball_subset_closedBall

/-- A complex polynomial with zero sup norm on an infinite compact set is the
zero polynomial. -/
theorem polynomial_eq_zero_of_polynomialSupNorm_eq_zero
    (p : ℂ[X]) {K : Set ℂ} (hK : IsCompact K) (hKinf : K.Infinite)
    (hzero : polynomialSupNorm p K = 0) : p = 0 := by
  apply p.eq_of_infinite_eval_eq 0
  apply hKinf.mono
  intro z hz
  have hle : ‖p.eval z‖ ≤ 0 := by
    simpa only [hzero] using norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz
  have hpz : p.eval z = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  change p.eval z = Polynomial.eval z (0 : ℂ[X])
  simpa only [eval_zero] using hpz

/-- A complex polynomial with zero sup norm on a closed disk of positive
radius is the zero polynomial. -/
theorem polynomial_eq_zero_of_polynomialSupNorm_closedBall_eq_zero
    (p : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hzero : polynomialSupNorm p (Metric.closedBall c R) = 0) :
    p = 0 :=
  polynomial_eq_zero_of_polynomialSupNorm_eq_zero p (isCompact_closedBall c R)
    (infinite_closedBall_of_pos c hR) hzero

section AuxiliaryBounds

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- On an infinite compact set, sharp auxiliary bounds for all polynomials of
sup norm one imply the correctly scaled bounds for every polynomial.  This
complements `polynomial_auxiliary_bounds_of_normalized`, whose division
argument assumes that the sup norm is positive. -/
theorem polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (hK : IsCompact K) (hKinf : K.Infinite) (p : Polynomial ℂ)
    (hnormalized : ∀ q : Polynomial ℂ,
      polynomialSupNorm q K = 1 →
        ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
          2 * polynomialSupNorm p K ∧
      ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          polynomialSupNorm p K ^ 2 := by
  by_cases hm : polynomialSupNorm p K = 0
  · have hp : p = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero p hK hKinf hm
    subst p
    have haux : crouzeixPolynomialAuxiliaryOperator A Omega 0 = 0 := by
      calc
        crouzeixPolynomialAuxiliaryOperator A Omega 0 =
            crouzeixPolynomialAuxiliaryOperator A Omega (0 • (1 : Polynomial ℂ)) := by
              rw [zero_smul]
        _ = star (0 : ℂ) •
            crouzeixPolynomialAuxiliaryOperator A Omega 1 :=
              crouzeixPolynomialAuxiliaryOperator_smul A Omega 0 1
        _ = 0 := by simp only [star_zero, zero_smul]
    rw [map_zero, haux, star_zero, add_zero, norm_zero, hm, mul_zero]
    constructor <;> norm_num
  · exact polynomial_auxiliary_bounds_of_normalized A Omega
      K p
      (lt_of_le_of_ne (polynomialSupNorm_nonneg p _) (Ne.symm hm)) hnormalized

/-- On a closed disk of positive radius, normalized sharp auxiliary bounds
imply the correctly scaled bounds for every polynomial. -/
theorem polynomial_auxiliary_bounds_of_normalized_closedBall
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (c : ℂ) {R : ℝ}
    (hR : 0 < R) (p : Polynomial ℂ)
    (hnormalized : ∀ q : Polynomial ℂ,
      polynomialSupNorm q (Metric.closedBall c R) = 1 →
        ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
          2 * polynomialSupNorm p (Metric.closedBall c R) ∧
      ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          polynomialSupNorm p (Metric.closedBall c R) ^ 2 :=
  polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite A Omega
    (Metric.closedBall c R) (isCompact_closedBall c R)
      (infinite_closedBall_of_pos c hR) p hnormalized

end AuxiliaryBounds

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
