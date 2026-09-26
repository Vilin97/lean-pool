/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionBoundary
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Regularized Plemelj reduction for the scalar companion

At a prospective boundary point `xi`, split the scalar Cauchy companion as

`C(h)(z) = h(xi) C(1)(z) + C(h - h(xi))(z)`.

The first term is just the normalized winding kernel.  The second has a
cancelled numerator and is the regularized transform carrying the genuinely
singular boundary analysis.  This file proves the split exactly and shows
that, once the winding kernel is normalized to one in the carrier,
convergence of the regularized transform gives the Plemelj limit, the
canonical continuous extension, and the maximum-modulus reduction.

No convergence or sharp boundary estimate for the regularized transform is
asserted here; those are the remaining analytic inputs.

## Main declarations

* `crouzeixScalarCauchyKernel` -- the normalized scalar winding kernel.
* `crouzeixPolynomialScalarCompanionRegularized` -- the transform with its
  boundary datum cancelled at `xi`.
* `crouzeixPolynomialScalarCompanionRegularized_add_C` -- cancellation makes
  the regularized transform invariant under constant polynomial shifts.
* `crouzeixPolynomialScalarCompanionRegularized_smul` -- the regularized
  transform and boundary value are conjugate-homogeneous.
* `contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self` --
  cancellation makes the boundary-point kernel genuinely integrable.
* `crouzeixPolynomialScalarCompanion_eq_regularized_add` -- the exact split
  away from the frontier.
* `tendsto_crouzeixPolynomialScalarCompanion_of_regularized` -- regularized
  convergence implies the actual Plemelj boundary limit.
* `crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized` --
  the canonical closure construction preserves polynomial addition.
* `norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary` -- the
  sharp interior reduction in terms of the explicit regularized values.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Interval Real

/-- The normalized scalar Cauchy kernel of the parametrized frontier.  For a
positively oriented Jordan curve it is `1` in the carrier and `0` outside the
closed domain. -/
noncomputable def crouzeixScalarCauchyKernel
    (Omega : SmoothJordanDomain) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral (fun sigma ↦ (sigma - z)⁻¹) Omega.boundaryParam

/-- The scalar companion regularized at `xi` by subtracting the boundary
datum at `xi` from its numerator. -/
noncomputable def crouzeixPolynomialScalarCompanionRegularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral
      (fun sigma ↦
        (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
          (sigma - z)⁻¹)
      Omega.boundaryParam

/-- The explicit prospective interior boundary value: the original datum at
`xi` plus the regularized transform evaluated at `xi`. -/
noncomputable def crouzeixPolynomialScalarCompanionBoundaryValue
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) : ℂ :=
  star (Polynomial.eval xi p) +
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi

/-- Adding a constant polynomial does not change the cancelled regularized
transform.  Thus all singular boundary analysis may be normalized by
subtracting the polynomial value at the selected boundary point. -/
theorem crouzeixPolynomialScalarCompanionRegularized_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega
        (p + Polynomial.C a) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
  unfold crouzeixPolynomialScalarCompanionRegularized
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Polynomial.eval_add, Polynomial.eval_C, star_add]
  ring

/-- The cancelled regularized transform is conjugate-homogeneous in the
polynomial argument. -/
theorem crouzeixPolynomialScalarCompanionRegularized_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi z =
      star a *
        crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
  unfold crouzeixPolynomialScalarCompanionRegularized
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma (a • p)) -
            star (Polynomial.eval xi (a • p))) *
          (sigma - z)⁻¹) =
        fun sigma ↦ star a •
          ((star (Polynomial.eval sigma p) -
              star (Polynomial.eval xi p)) * (sigma - z)⁻¹) := by
    funext sigma
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, contourIntegral_smul]
  simp only [smul_eq_mul]
  ring

/-- The regularized transform of the zero polynomial vanishes. -/
@[simp] theorem crouzeixPolynomialScalarCompanionRegularized_zero
    (Omega : SmoothJordanDomain) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega 0 xi z = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialScalarCompanionRegularized_smul
      Omega 0 (0 : Polynomial ℂ) xi z)

/-- Regularized boundary convergence is preserved by polynomial scaling. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi : ℂ)
    {l : Filter ℂ}
    (h : Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      l
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi)
      l
      (nhds (crouzeixPolynomialScalarCompanionRegularized
        Omega (a • p) xi xi)) := by
  have hfun :
      crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi =
        fun z ↦ star a *
          crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
    funext z
    exact crouzeixPolynomialScalarCompanionRegularized_smul
      Omega a p xi z
  rw [hfun]
  exact tendsto_const_nhds.mul h

/-- The canonical boundary-point normalization has zero value at `xi`. -/
theorem eval_sub_C_eval_eq_zero (p : Polynomial ℂ) (xi : ℂ) :
    Polynomial.eval xi (p - Polynomial.C (Polynomial.eval xi p)) = 0 := by
  simp only [Polynomial.eval_sub, Polynomial.eval_C, sub_self]

/-- Regularization is unchanged after replacing `p` by the canonical
polynomial `p - C (p.eval xi)` that vanishes at `xi`. -/
theorem crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega
        (p - Polynomial.C (Polynomial.eval xi p)) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
  simpa only [sub_eq_add_neg, ← Polynomial.C_neg] using
    (crouzeixPolynomialScalarCompanionRegularized_add_C
      Omega p (-Polynomial.eval xi p) xi z)

/-- Regularized boundary convergence is equivalent for `p` and its
boundary-point normalization. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval_iff
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ)
    (l : Filter ℂ) :
    Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi)
        l
        (nhds (crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi xi)) ↔
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        l
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  have hfun :
      crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi =
        crouzeixPolynomialScalarCompanionRegularized Omega p xi := by
    funext z
    exact crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
      Omega p xi z
  rw [hfun]

/-- The Plemelj value splits into the conjugate boundary datum plus the
boundary value of the polynomial normalized to vanish at `xi`. -/
theorem crouzeixPolynomialScalarCompanionBoundaryValue_eq_add_normalized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionBoundaryValue Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_sub_C_eval,
    eval_sub_C_eval_eq_zero]
  simp only [star_zero, zero_add]

/-- The explicit Plemelj boundary value is conjugate-affine under addition
of a constant polynomial. -/
theorem crouzeixPolynomialScalarCompanionBoundaryValue_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega
        (p + Polynomial.C a) xi =
      star a + crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_add_C]
  simp only [Polynomial.eval_add, Polynomial.eval_C, star_add]
  ring

/-- The explicit Plemelj boundary value is conjugate-homogeneous in the
polynomial argument. -/
theorem crouzeixPolynomialScalarCompanionBoundaryValue_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega (a • p) xi =
      star a *
        crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_smul]
  have heval : star (Polynomial.eval xi (a • p)) =
      star a * star (Polynomial.eval xi p) := by
    rw [Polynomial.eval_smul]
    change (starRingEnd ℂ) (a * Polynomial.eval xi p) =
      (starRingEnd ℂ) a * (starRingEnd ℂ) (Polynomial.eval xi p)
    exact map_mul (starRingEnd ℂ) a (Polynomial.eval xi p)
  rw [heval]
  ring

/-- The explicit Plemelj boundary value for the zero polynomial vanishes. -/
@[simp] theorem crouzeixPolynomialScalarCompanionBoundaryValue_zero
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega 0 xi = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialScalarCompanionBoundaryValue_smul
      Omega 0 (0 : Polynomial ℂ) xi)

private theorem contourIntegrable_crouzeixScalarCauchyKernel
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    ContourIntegrable (fun sigma ↦ (sigma - z)⁻¹) Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · have hden : ContinuousOn (fun sigma : ℂ ↦ sigma - z)
        (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
      continuous_id.continuousOn.sub continuous_const.continuousOn
    apply hden.inv₀
    rintro sigma ⟨t, ht, rfl⟩ hzero
    apply hz
    have heq : Omega.boundaryParam t = z := sub_eq_zero.mp hzero
    rw [← heq, ← Omega.boundaryParam_range]
    exact mem_range_self t

private theorem contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    ContourIntegrable
      (fun sigma ↦
        (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
          (sigma - z)⁻¹)
      Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · have hden : ContinuousOn (fun sigma : ℂ ↦ sigma - z)
        (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
      continuous_id.continuousOn.sub continuous_const.continuousOn
    have hne : ∀ sigma ∈
        Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi), sigma - z ≠ 0 := by
      rintro sigma ⟨t, ht, rfl⟩ hzero
      apply hz
      have heq : Omega.boundaryParam t = z := sub_eq_zero.mp hzero
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    exact (p.continuous.star.continuousOn.sub
      continuous_const.continuousOn).mul (hden.inv₀ hne)

/-- Cancellation makes the regularized kernel contour-integrable at its own
base point, even when that point lies on the frontier.  Polynomial division
factors the numerator by `sigma - xi`; after conjugation and multiplication
by its inverse, the remaining singular factor has norm one. -/
theorem contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    ContourIntegrable
      (fun sigma ↦
        (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam := by
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  have hpoly : Polynomial.C (Polynomial.eval xi p) +
      (Polynomial.X - Polynomial.C xi) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C xi)
  have heval : ∀ sigma : ℂ,
      Polynomial.eval sigma p - Polynomial.eval xi p =
        (sigma - xi) * Polynomial.eval sigma q := by
    intro sigma
    have h := congrArg (Polynomial.eval sigma) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  let F : ℝ → ℂ := fun t ↦
    deriv Omega.boundaryParam t *
      ((star (Polynomial.eval (Omega.boundaryParam t) p) -
          star (Polynomial.eval xi p)) *
        (Omega.boundaryParam t - xi)⁻¹)
  let bound : ℝ → ℝ := fun t ↦
    ‖deriv Omega.boundaryParam t‖ *
      ‖Polynomial.eval (Omega.boundaryParam t) q‖
  have hboundCont : Continuous bound := by
    exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm.mul
      (q.continuous.comp
        Omega.boundaryParam_contDiff.continuous).norm
  have hboundInt : IntervalIntegrable bound volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hFstrong : StronglyMeasurable F := by
    dsimp only [F]
    exact
      (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).stronglyMeasurable.mul
        (((p.continuous.comp Omega.boundaryParam_contDiff.continuous).star.sub
            continuous_const).stronglyMeasurable.mul
          ((Omega.boundaryParam_contDiff.continuous.stronglyMeasurable.sub
            stronglyMeasurable_const).inv₀))
  have hnorm : ∀ t, ‖F t‖ ≤ bound t := by
    intro t
    by_cases hzero : Omega.boundaryParam t = xi
    · simp only [F, bound, hzero, sub_self, inv_zero, mul_zero, norm_zero]
      positivity
    · have hdiff : Omega.boundaryParam t - xi ≠ 0 :=
        sub_ne_zero.mpr hzero
      have hdiffNorm : ‖Omega.boundaryParam t - xi‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hdiff
      have hstar :
          star (Polynomial.eval (Omega.boundaryParam t) p) -
              star (Polynomial.eval xi p) =
            star (Omega.boundaryParam t - xi) *
              star (Polynomial.eval (Omega.boundaryParam t) q) := by
        rw [← star_sub, heval, star_mul]
        ring
      dsimp only [F, bound]
      rw [hstar]
      simp only [norm_mul, norm_star, norm_inv]
      calc
        ‖deriv Omega.boundaryParam t‖ *
              ((‖Omega.boundaryParam t - xi‖ *
                  ‖Polynomial.eval (Omega.boundaryParam t) q‖) *
                ‖Omega.boundaryParam t - xi‖⁻¹) =
            ‖deriv Omega.boundaryParam t‖ *
              (‖Polynomial.eval (Omega.boundaryParam t) q‖ *
                (‖Omega.boundaryParam t - xi‖ *
                  ‖Omega.boundaryParam t - xi‖⁻¹)) := by ring
        _ = ‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t) q‖ := by
          rw [mul_inv_cancel₀ hdiffNorm, mul_one]
        _ ≤ ‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t) q‖ := le_rfl
  unfold ContourIntegrable
  change IntervalIntegrable F volume (0 : ℝ) (2 * Real.pi)
  exact hboundInt.mono_fun hFstrong.aestronglyMeasurable.restrict
    (Eventually.of_forall fun t ↦ by
      change ‖F t‖ ≤ ‖bound t‖
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hnorm t)

/-- At the cancelled base point, the regularized transform is additive in
the polynomial argument.  The integrability needed for interval-integral
additivity is supplied by the preceding cancellation theorem. -/
theorem crouzeixPolynomialScalarCompanionRegularized_add_self
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi xi =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi xi +
        crouzeixPolynomialScalarCompanionRegularized Omega q xi xi := by
  have hp :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi
  have hq :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega q xi
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma (p + q)) -
            star (Polynomial.eval xi (p + q))) * (sigma - xi)⁻¹) =
        fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - xi)⁻¹ +
            (star (Polynomial.eval sigma q) - star (Polynomial.eval xi q)) *
              (sigma - xi)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_add, star_add]
    ring
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [hfun, contourIntegral_add hp hq]
  ring

/-- Away from the frontier, the regularized transform is additive in its
polynomial argument. -/
theorem crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z +
        crouzeixPolynomialScalarCompanionRegularized Omega q xi z := by
  have hp := contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
    Omega p xi hz
  have hq := contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
    Omega q xi hz
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma (p + q)) -
            star (Polynomial.eval xi (p + q))) * (sigma - z)⁻¹) =
        fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - z)⁻¹ +
            (star (Polynomial.eval sigma q) - star (Polynomial.eval xi q)) *
              (sigma - z)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_add, star_add]
    ring
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [hfun, contourIntegral_add hp hq]
  ring

/-- Regularized Plemelj convergence is stable under polynomial addition. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_add
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ)
    (hp : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hq : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega q xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega q xi xi))) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized
        Omega (p + q) xi xi)) := by
  rw [crouzeixPolynomialScalarCompanionRegularized_add_self]
  apply (hp.add hq).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier]
  intro hfrontier
  have hempty : z ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hz, hfrontier⟩
  exact hempty

/-- The explicit Plemelj boundary value is additive in the polynomial
argument. -/
theorem crouzeixPolynomialScalarCompanionBoundaryValue_add
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega (p + q) xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi +
        crouzeixPolynomialScalarCompanionBoundaryValue Omega q xi := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_add_self]
  simp only [Polynomial.eval_add, star_add]
  ring

private theorem contourIntegrable_crouzeixScalarCauchyKernel_const_mul
    (Omega : SmoothJordanDomain) (c : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    ContourIntegrable (fun sigma ↦ c * (sigma - z)⁻¹)
      Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · have hden : ContinuousOn (fun sigma : ℂ ↦ sigma - z)
        (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) :=
      continuous_id.continuousOn.sub continuous_const.continuousOn
    have hne : ∀ sigma ∈
        Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi), sigma - z ≠ 0 := by
      rintro sigma ⟨t, ht, rfl⟩ hzero
      apply hz
      have heq : Omega.boundaryParam t = z := sub_eq_zero.mp hzero
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    exact continuous_const.continuousOn.mul (hden.inv₀ hne)

/-- Away from the frontier, the scalar companion is exactly the sum of its
regularized transform and the boundary datum times the normalized winding
kernel. -/
theorem crouzeixPolynomialScalarCompanion_eq_regularized_add
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega p z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z +
        star (Polynomial.eval xi p) * crouzeixScalarCauchyKernel Omega z := by
  have hreg :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized
      Omega p xi hz
  have hkernel := contourIntegrable_crouzeixScalarCauchyKernel Omega hz
  have hconst := contourIntegrable_crouzeixScalarCauchyKernel_const_mul
    Omega (star (Polynomial.eval xi p)) hz
  have hfun :
      (fun sigma ↦ star (Polynomial.eval sigma p) * (sigma - z)⁻¹) =
        (fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - z)⁻¹ +
            star (Polynomial.eval xi p) * (sigma - z)⁻¹) := by
    funext sigma
    ring
  unfold crouzeixPolynomialScalarCompanion
    crouzeixPolynomialScalarCompanionRegularized crouzeixScalarCauchyKernel
  rw [hfun, contourIntegral_add hreg hconst,
    contourIntegral_const_mul (star (Polynomial.eval xi p)) hkernel]
  ring

/-- Away from the frontier, the full scalar companion is additive in its
polynomial argument. -/
theorem crouzeixPolynomialScalarCompanion_add
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega (p + q) z =
      crouzeixPolynomialScalarCompanion Omega p z +
        crouzeixPolynomialScalarCompanion Omega q z := by
  let xi : ℂ := Omega.boundaryParam 0
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add
      Omega (p + q) xi hz,
    crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi hz,
    crouzeixPolynomialScalarCompanion_eq_regularized_add Omega q xi hz,
    crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
      Omega p q xi hz]
  simp only [Polynomial.eval_add, star_add]
  ring

/-- Away from the frontier, adding a constant polynomial shifts the full
companion by the conjugate constant times the normalized winding kernel. -/
theorem crouzeixPolynomialScalarCompanion_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega (p + Polynomial.C a) z =
      star a * crouzeixScalarCauchyKernel Omega z +
        crouzeixPolynomialScalarCompanion Omega p z := by
  let xi : ℂ := Omega.boundaryParam 0
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add
      Omega (p + Polynomial.C a) xi hz,
    crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi hz,
    crouzeixPolynomialScalarCompanionRegularized_add_C]
  simp only [Polynomial.eval_add, Polynomial.eval_C, star_add]
  ring

private theorem not_mem_frontier_of_mem_carrier
    (Omega : SmoothJordanDomain) {z : ℂ} (hz : z ∈ Omega.carrier) :
    z ∉ frontier Omega.carrier := by
  intro hfrontier
  have hempty : z ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hz, hfrontier⟩
  exact hempty

/-- If the scalar winding kernel is normalized to one in the carrier, then
convergence of the cancelled transform at `xi` implies the actual Plemelj
limit there. -/
theorem tendsto_crouzeixPolynomialScalarCompanion_of_regularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (xi : ℂ)
    (hreg : Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  have hlim : Tendsto
      (fun z ↦ star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi z)
      (nhdsWithin xi Omega.carrier)
      (nhds (star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) :=
    tendsto_const_nhds.add hreg
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi
    (not_mem_frontier_of_mem_carrier Omega hz), hkernel z hz, mul_one]
  exact add_comm _ _

/-- Frontierwise convergence of the regularized transforms makes the
canonical closed companion extension continuous. -/
theorem
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by
  apply continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
    Omega p (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
  intro xi hxi
  exact tendsto_crouzeixPolynomialScalarCompanion_of_regularized
    Omega p hkernel xi (hreg xi hxi)

/-- Under the regularized convergence hypotheses, the canonical extension
takes the explicit regularized Plemelj value on the frontier. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
      Omega p (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
  · intro z hz
    exact tendsto_crouzeixPolynomialScalarCompanion_of_regularized
      Omega p hkernel z (hreg z hz)
  · exact hxi

/-- Under winding normalization and regularized Plemelj convergence for two
polynomials, the canonical closed companion extension preserves their sum on
the whole closure. -/
theorem crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hp : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hq : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega q xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega q xi xi)))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by
  have hsum : ∀ xi ∈ frontier Omega.carrier,
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi)
        (nhdsWithin xi Omega.carrier)
        (nhds (crouzeixPolynomialScalarCompanionRegularized
          Omega (p + q) xi xi)) := by
    intro xi hxi
    exact tendsto_crouzeixPolynomialScalarCompanionRegularized_add
      Omega p q xi (hp xi hxi) (hq xi hxi)
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Omega (p + q) hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq Omega q hz,
      crouzeixPolynomialScalarCompanion_add Omega p q
        (not_mem_frontier_of_mem_carrier Omega hz)]
  · rw [
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega (p + q) hkernel hsum hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega p hkernel hp hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega q hkernel hq hz,
      crouzeixPolynomialScalarCompanionBoundaryValue_add]

/-- Under winding normalization and regularized Plemelj convergence, the
canonical closed companion extension is conjugate-homogeneous on the whole
closure. -/
theorem crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hp : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by
  have hscaled : ∀ xi ∈ frontier Omega.carrier,
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi)
        (nhdsWithin xi Omega.carrier)
        (nhds (crouzeixPolynomialScalarCompanionRegularized
          Omega (a • p) xi xi)) := by
    intro xi hxi
    exact tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
      Omega a p xi (hp xi hxi)
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Omega (a • p) hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hz,
      crouzeixPolynomialScalarCompanion_smul]
  · rw [
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega (a • p) hkernel hscaled hz,
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
        Omega p hkernel hp hz,
      crouzeixPolynomialScalarCompanionBoundaryValue_smul]

/-- If the explicit regularized Plemelj values have norm at most `C` on the
frontier, the scalar companion has the same bound throughout the carrier. -/
theorem norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto
    Omega p (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
      hbounded
      (fun xi hxi ↦ tendsto_crouzeixPolynomialScalarCompanion_of_regularized
        Omega p hkernel xi (hreg xi hxi))
      hC hz

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
