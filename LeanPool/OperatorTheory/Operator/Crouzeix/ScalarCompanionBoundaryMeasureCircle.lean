/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# The boundary double-layer probability measure on a circle

For a positively oriented circle and a base point `xi` on that circle, the
scalar boundary double-layer density is `1 / (2 pi)` away from the unique
parameter value representing `xi` and is zero at that parameter by the
inverse-at-zero convention.  The exceptional singleton has measure zero, so
the density is nonnegative and has total mass one.

This completely discharges the geometric probability-measure interface in
the disk model and recovers the sharp boundary-phase invariant for every
polynomial through the general boundary-measure theorem.

## Main declarations

* `crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne` -- the
  pointwise density away from the base point;
* `integral_crouzeixBoundaryDoubleLayerDensity_ball` -- its total mass is one;
* `crouzeixBoundaryDoubleLayerDensity_ball_nonneg` -- its pointwise sign;
* `crouzeixBoundaryPhaseContractive_ball_of_boundaryDoubleLayerDensity` --
  sharp phase contractivity on every positive-radius disk.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionBoundaryMeasure

open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real

private theorem im_circleChordLogDeriv_eq_half
    (u v : ℂ) (huv : u ≠ v)
    (hnorm : Complex.normSq u = Complex.normSq v) :
    ((u * I) * (u - v)⁻¹).im = 1 / 2 := by
  have hd : Complex.normSq (u - v) ≠ 0 := by
    intro hzero
    exact sub_ne_zero.mpr huv (Complex.normSq_eq_zero.mp hzero)
  rw [← div_eq_mul_inv, Complex.div_im, ← sub_div]
  have hnum : (u * I).im * (u - v).re -
      (u * I).re * (u - v).im = Complex.normSq (u - v) / 2 := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, Complex.sub_re, Complex.sub_im,
      Complex.normSq_apply] at hnorm ⊢
    linarith
  rw [hnum]
  field_simp [hd]

/-- Away from its boundary base point, the double-layer density of a
positive circle is the constant `1 / (2 pi)`. -/
theorem crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) (t : ℝ)
    (hne : circleMap c R t ≠ xi) :
    crouzeixBoundaryDoubleLayerDensity
        (SmoothJordanDomain.ball c R hR) xi t = (2 * Real.pi)⁻¹ := by
  let u := circleMap 0 R t
  let v := xi - c
  have hd : circleMap c R t - xi = u - v := by
    dsimp only [u, v]
    rw [← circleMap_sub_center c R t]
    ring
  have huv : u ≠ v := by
    apply sub_ne_zero.mp
    rw [← hd]
    exact sub_ne_zero.mpr hne
  have hunorm : Complex.normSq u = R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    dsimp only [u]
    rw [norm_circleMap_zero, abs_of_pos hR]
  have hvnorm : ‖v‖ = R := by
    dsimp only [v]
    simpa only [dist_eq_norm] using (Metric.mem_sphere.mp hxi)
  have hnorm : Complex.normSq u = Complex.normSq v := by
    rw [hunorm, Complex.normSq_eq_norm_sq, hvnorm]
  have hhalf := im_circleChordLogDeriv_eq_half u v huv hnorm
  unfold crouzeixBoundaryDoubleLayerDensity
  change (deriv (circleMap c R) t *
      (circleMap c R t - xi)⁻¹).im / Real.pi = _
  rw [deriv_circleMap, hd]
  change ((u * I) * (u - v)⁻¹).im / Real.pi = _
  rw [hhalf]
  field_simp [Real.pi_ne_zero]

/-- The boundary double-layer density of a positive circle has total mass
one at every boundary base point. -/
theorem integral_crouzeixBoundaryDoubleLayerDensity_ball
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity
        (SmoothJordanDomain.ball c R hR) xi t) = 1 := by
  have hfrontier : xi ∈ frontier
      (SmoothJordanDomain.ball c R hR).carrier := by
    change xi ∈ frontier (Metric.ball c R)
    rw [frontier_ball c hR.ne']
    exact hxi
  calc
    (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity
          (SmoothJordanDomain.ball c R hR) xi t) =
        ∫ _t in (0 : ℝ)..(2 * Real.pi), (2 * Real.pi)⁻¹ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_boundaryParam_ne_of_mem_frontier
        (SmoothJordanDomain.ball c R hR) hfrontier] with t ht
      intro htI
      exact
        crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
          hR hxi t (ht htI)
    _ = 1 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      exact mul_inv_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero)

/-- The boundary double-layer density of a positive circle is everywhere
nonnegative, including its inverse-at-zero value at the base point. -/
theorem crouzeixBoundaryDoubleLayerDensity_ball_nonneg
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) (t : ℝ) :
    0 ≤ crouzeixBoundaryDoubleLayerDensity
      (SmoothJordanDomain.ball c R hR) xi t := by
  by_cases hne : circleMap c R t ≠ xi
  · rw [
      crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
        hR hxi t hne]
    exact inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)
  · have heq : circleMap c R t = xi := not_ne_iff.mp hne
    unfold crouzeixBoundaryDoubleLayerDensity
    change 0 ≤ (deriv (circleMap c R) t *
      (circleMap c R t - xi)⁻¹).im / Real.pi
    rw [heq, sub_self, inv_zero, mul_zero, zero_im, zero_div]

/-- Every polynomial satisfies the sharp boundary-phase invariant on a
positive-radius disk, obtained from the explicit circle probability
density. -/
theorem crouzeixBoundaryPhaseContractive_ball_of_boundaryDoubleLayerDensity
    {c : ℂ} {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive
      (SmoothJordanDomain.ball c R hR) p := by
  apply crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
  · intro xi hxi
    apply
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
    apply integral_crouzeixBoundaryDoubleLayerDensity_ball hR
    change xi ∈ frontier (Metric.ball c R) at hxi
    rwa [frontier_ball c hR.ne'] at hxi
  · intro xi hxi
    apply integral_crouzeixBoundaryDoubleLayerDensity_ball hR
    change xi ∈ frontier (Metric.ball c R) at hxi
    rwa [frontier_ball c hR.ne'] at hxi
  · intro xi hxi t _ht
    apply crouzeixBoundaryDoubleLayerDensity_ball_nonneg hR
    change xi ∈ frontier (Metric.ball c R) at hxi
    rwa [frontier_ball c hR.ne'] at hxi

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
