/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.GeneralSymmetrized
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanion

/-!
# Quantitative decay of the scalar companion

The scalar Crouzeix--Palencia companion is a Cauchy transform supported on
the compact Jordan frontier.  This file records the elementary quantitative
part of its exterior normalization: the numerator is uniformly bounded on
the parameter interval, so the transform is bounded by the reciprocal of
the distance to the frontier and therefore tends to zero at infinity.

These facts are useful inputs to a future Plemelj jump argument.  They do not
assert boundary continuity or the sharp companion contraction.

## Main declarations

* `exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator` -- a
  uniform parameter-interval numerator bound.
* `exists_nonneg_bound_boundaryParam_deriv` -- a domain-only bound for the
  boundary speed.
* `norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation` -- the
  explicit inverse-separation estimate.
* `norm_crouzeixPolynomialScalarCompanion_le_infDist` -- its canonical
  distance-to-frontier form.
* `exists_uniform_norm_crouzeixPolynomialScalarCompanion_le_infDist` -- one
  domain constant controls all polynomials by their frontier sup norm.
* `tendsto_crouzeixPolynomialScalarCompanion_cocompact` -- the exterior
  companion tends to zero at infinity.
-/

open Complex Filter Set
open scoped Interval Real

/-- The speed of a smooth Jordan parametrization is uniformly bounded on the
compact parameter interval. -/
theorem exists_nonneg_bound_boundaryParam_deriv
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D := by
  have hderiv : ContinuousOn (deriv Omega.boundaryParam)
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  have himage : IsCompact
      (deriv Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.image_of_continuousOn hderiv
  obtain ⟨D, hD⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    himage.isBounded
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨le_rfl, Real.two_pi_pos.le⟩
  have hD_nonneg : 0 ≤ D := by
    have hmem := hD ⟨0, hzero, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact (norm_nonneg _).trans hmem
  refine ⟨D, hD_nonneg, fun t ht ↦ ?_⟩
  have hmem := hD ⟨t, ht, rfl⟩
  rwa [Metric.mem_closedBall, dist_zero_right] at hmem

/-- The numerator of the parameterized scalar Cauchy companion is uniformly
bounded on the compact interval `[0, 2 * pi]`. -/
theorem exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C := by
  have hintegrand : ContinuousOn
      (fun t ↦ deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p))
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn.mul
      ((p.continuous.comp
        Omega.boundaryParam_contDiff.continuous).star.continuousOn)
  have himage : IsCompact
      ((fun t ↦ deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)) ''
          Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.image_of_continuousOn hintegrand
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    himage.isBounded
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨le_rfl, Real.two_pi_pos.le⟩
  have hC_nonneg : 0 ≤ C := by
    have hmem := hC ⟨0, hzero, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact (norm_nonneg _).trans hmem
  refine ⟨C, hC_nonneg, fun t ht ↦ ?_⟩
  have hmem := hC ⟨t, ht, rfl⟩
  rwa [Metric.mem_closedBall, dist_zero_right] at hmem

/-- If every point on the parametrized frontier is at least `delta` away
from `z`, a numerator bound `C` gives the expected `C / delta` estimate for
the normalized scalar Cauchy companion. -/
theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {delta C : ℝ}
    (hdelta : 0 < delta) (hC_nonneg : 0 ≤ C)
    (hC : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C)
    (hsep : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      delta ≤ ‖Omega.boundaryParam t - z‖) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi * (C * delta⁻¹)) := by
  have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) *
          (Omega.boundaryParam t - z)⁻¹)‖ ≤ C * delta⁻¹ := by
    intro t ht
    have hdenpos : 0 < ‖Omega.boundaryParam t - z‖ :=
      hdelta.trans_le (hsep t ht)
    have hinv : ‖Omega.boundaryParam t - z‖⁻¹ ≤ delta⁻¹ :=
      (inv_le_inv₀ hdenpos hdelta).2 (hsep t ht)
    have hCt := hC t ht
    rw [norm_mul] at hCt
    simp only [smul_eq_mul, ← mul_assoc, norm_mul, norm_inv]
    exact mul_le_mul hCt hinv (inv_nonneg.mpr (norm_nonneg _)) hC_nonneg
  unfold crouzeixPolynomialScalarCompanion
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)

/-- Away from the frontier, the preceding estimate specializes to the
minimal distance from `z` to that frontier. -/
theorem norm_crouzeixPolynomialScalarCompanion_le_infDist
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C)
    (hz : z ∉ frontier Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (C * (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by
  have hfrontier : Omega.boundaryParam 0 ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  have hnonempty : (frontier Omega.carrier).Nonempty := ⟨_, hfrontier⟩
  have hdist_pos : 0 < Metric.infDist z (frontier Omega.carrier) :=
    (isClosed_frontier.notMem_iff_infDist_pos hnonempty).mp hz
  apply norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
    Omega p hdist_pos hC_nonneg hC
  intro t ht
  have htfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  simpa only [dist_eq_norm, norm_sub_rev] using
    (Metric.infDist_le_dist_of_mem htfrontier :
      Metric.infDist z (frontier Omega.carrier) ≤
        dist z (Omega.boundaryParam t))

/-- A domain-only boundary-speed bound and the canonical frontier polynomial
sup norm give a fully uniform inverse-distance estimate. -/
theorem
    norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D)
    (hz : z ∉ frontier Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          ((D * polynomialSupNorm p (frontier Omega.carrier)) *
            (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by
  apply norm_crouzeixPolynomialScalarCompanion_le_infDist Omega p
    (mul_nonneg hD_nonneg (polynomialSupNorm_nonneg p _))
  · intro t ht
    rw [norm_mul, norm_star]
    exact mul_le_mul (hD t ht)
      (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega p t)
      (norm_nonneg _) hD_nonneg
  · exact hz

/-- One nonnegative constant depending only on the smooth Jordan domain
controls the scalar companions of every polynomial away from the frontier. -/
theorem exists_uniform_norm_crouzeixPolynomialScalarCompanion_le_infDist
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (z : ℂ),
      z ∉ frontier Omega.carrier →
      ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            ((D * polynomialSupNorm p (frontier Omega.carrier)) *
              (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun p z hz ↦
    norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm
      Omega p hD_nonneg hD hz⟩

/-- The distance from a point to a compact Jordan frontier tends to infinity
as the point tends to infinity. -/
theorem tendsto_infDist_frontier_cocompact_atTop
    (Omega : SmoothJordanDomain) :
    Tendsto (fun z : ℂ ↦ Metric.infDist z (frontier Omega.carrier))
      (cocompact ℂ) atTop := by
  let y : ℂ := Omega.boundaryParam 0
  have hy : y ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  have hdist : Tendsto (fun z : ℂ ↦ dist z y) (cocompact ℂ) atTop :=
    tendsto_dist_right_cocompact_atTop y
  have hshift : Tendsto
      (fun z : ℂ ↦ dist z y + (-Metric.diam (frontier Omega.carrier)))
      (cocompact ℂ) atTop :=
    tendsto_atTop_add_const_right (cocompact ℂ)
      (-Metric.diam (frontier Omega.carrier)) hdist
  refine tendsto_atTop_mono' (cocompact ℂ) ?_ hshift
  filter_upwards with z
  have hbound := Metric.dist_le_infDist_add_diam
    (x := z) Omega.isCompact_frontier.isBounded hy
  linarith

/-- The exterior scalar companion has the canonical Cauchy-transform
normalization: it tends to zero at infinity. -/
theorem tendsto_crouzeixPolynomialScalarCompanion_cocompact
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (cocompact ℂ) (nhds 0) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator Omega p
  have hinf := tendsto_infDist_frontier_cocompact_atTop Omega
  have hinv : Tendsto
      (fun z : ℂ ↦ (Metric.infDist z (frontier Omega.carrier))⁻¹)
      (cocompact ℂ) (nhds 0) := hinf.inv_tendsto_atTop
  have hmajorant : Tendsto
      (fun z : ℂ ↦ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (C * (Metric.infDist z (frontier Omega.carrier))⁻¹)))
      (cocompact ℂ) (nhds 0) := by
    have hscaled :=
      (tendsto_const_nhds.mul hinv : Tendsto
        (fun z : ℂ ↦
          (‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)) *
            (Metric.infDist z (frontier Omega.carrier))⁻¹)
        (cocompact ℂ) (nhds
          ((‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)) * 0)))
    simpa only [mul_zero] using hscaled.congr'
      (Eventually.of_forall fun z ↦ by ring)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Eventually.of_forall fun z ↦ norm_nonneg
      (crouzeixPolynomialScalarCompanion Omega p z))
  · filter_upwards [Omega.isCompact_frontier.compl_mem_cocompact] with z hz
    exact norm_crouzeixPolynomialScalarCompanion_le_infDist
      Omega p hC_nonneg hC hz
  · exact hmajorant

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
