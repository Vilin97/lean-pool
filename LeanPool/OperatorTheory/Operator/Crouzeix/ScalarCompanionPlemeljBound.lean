/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ProductBase
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionDecay
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPlemelj

/-!
# Quantitative bounds for the regularized Plemelj value

Polynomial division by `X - C xi` factors the cancelled boundary numerator.
Consequently, the apparent singular phase in the regularized self-value has
unit norm, and a bound on the speed of the boundary parametrization gives an
explicit estimate in terms of the frontier sup norm of the divided-difference
polynomial.

This is not the final sharp companion contraction: it isolates the additional
divided-difference term that a sharp boundary argument must control.

## Main declarations

* `norm_crouzeixPolynomialScalarCompanionRegularized_self_le` -- the explicit
  bound for a chosen boundary-speed constant.
* `crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic` -- the
  exact lower-degree phase-weighted contour representation.
* `crouzeixPolynomialBoundaryPhaseTransform` -- the named lower-degree phase
  contour carrying the remaining sharp frontier estimate.
* `crouzeixPolynomialBoundaryPhaseTransform_add` and `_smul` -- its
  conjugate-linear polynomial API.
* `norm_crouzeixPolynomialBoundaryPhaseTransform_le` -- its explicit
  domain-speed norm bound.
* `exists_uniform_norm_crouzeixPolynomialScalarCompanionRegularized_self_le`
  -- one domain-only constant works for all polynomials and base points.
* `norm_crouzeixPolynomialScalarCompanionBoundaryValue_le` -- the resulting
  quantitative bound for the explicit Plemelj boundary value.
-/

open Complex Set
open scoped Interval Real

/-- The phase-weighted conjugate Cauchy contour at a prospective boundary
point.  In the Plemelj recursion its polynomial argument is the strictly
lower-degree quotient `p /ₘ (X - C xi)`. -/
noncomputable def crouzeixPolynomialBoundaryPhaseTransform
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma q) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam

/-- The polynomial divided difference used at `xi` has degree exactly one
less, truncated at zero. -/
theorem natDegree_divByMonic_X_sub_C_eq_sub_one
    (p : Polynomial ℂ) (xi : ℂ) :
    (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree =
      p.natDegree - 1 := by
  rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C xi),
    Polynomial.natDegree_X_sub_C]

/-- For a positive-degree polynomial, the divided difference has strictly
smaller natural degree. -/
theorem natDegree_divByMonic_X_sub_C_lt
    (p : Polynomial ℂ) (xi : ℂ) (hp : 0 < p.natDegree) :
    (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree < p.natDegree := by
  rw [natDegree_divByMonic_X_sub_C_eq_sub_one]
  omega

/-- The regularized self-value is exactly a phase-weighted contour of the
strictly lower-degree divided difference.  The factor
`star (sigma - xi) * (sigma - xi)⁻¹` has norm one away from its removable
zero. -/
theorem crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        contourIntegral
          (fun sigma ↦
            star (sigma - xi) *
              star (Polynomial.eval sigma
                (p /ₘ (Polynomial.X - Polynomial.C xi))) *
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
  unfold crouzeixPolynomialScalarCompanionRegularized
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change deriv Omega.boundaryParam t *
      ((star (Polynomial.eval (Omega.boundaryParam t) p) -
          star (Polynomial.eval xi p)) *
        (Omega.boundaryParam t - xi)⁻¹) =
    deriv Omega.boundaryParam t *
      (star (Omega.boundaryParam t - xi) *
        star (Polynomial.eval (Omega.boundaryParam t) q) *
          (Omega.boundaryParam t - xi)⁻¹)
  rw [← star_sub, heval, star_mul]
  ring

/-- The explicit Plemelj boundary value consists of the conjugate boundary
datum and the phase-weighted contour of a lower-degree polynomial. -/
theorem crouzeixPolynomialScalarCompanionBoundaryValue_eq_divByMonic
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          contourIntegral
            (fun sigma ↦
              star (sigma - xi) *
                star (Polynomial.eval sigma
                  (p /ₘ (Polynomial.X - Polynomial.C xi))) *
                (sigma - xi)⁻¹)
            Omega.boundaryParam := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic]

/-- The regularized self-value is the named boundary phase transform of the
divided difference. -/
theorem
    crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi =
      crouzeixPolynomialBoundaryPhaseTransform Omega xi
        (p /ₘ (Polynomial.X - Polynomial.C xi)) := by
  unfold crouzeixPolynomialBoundaryPhaseTransform
  exact
    crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
      Omega p xi

/-- The explicit Plemelj boundary value is the conjugate point value plus
the lower-degree boundary phase transform. -/
theorem
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi)) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [
    crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform]

/-- The phase transform of `q` is itself the regularized self-value of the
polynomial `(X - C xi) * q`.  This realizes the lower-degree contour as the
same cancelled Cauchy construction already used by the Plemelj split. -/
theorem crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi q =
      crouzeixPolynomialScalarCompanionRegularized Omega
        ((Polynomial.X - Polynomial.C xi) * q) xi xi := by
  symm
  rw [
    crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform,
    Polynomial.mul_divByMonic_cancel_left q
      (Polynomial.monic_X_sub_C xi)]

/-- The phase-weighted contour is genuinely integrable, including at its
base point on the trace. -/
theorem contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) :
    ContourIntegrable
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma q) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam := by
  have h :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega ((Polynomial.X - Polynomial.C xi) * q) xi
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma
              ((Polynomial.X - Polynomial.C xi) * q)) -
            star (Polynomial.eval xi
              ((Polynomial.X - Polynomial.C xi) * q))) *
          (sigma - xi)⁻¹) =
        fun sigma ↦
          star (sigma - xi) * star (Polynomial.eval sigma q) *
            (sigma - xi)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul, star_zero, sub_zero, star_mul]
    ring
  rw [hfun] at h
  exact h

/-- The boundary phase transform is additive in its polynomial argument. -/
theorem crouzeixPolynomialBoundaryPhaseTransform_add
    (Omega : SmoothJordanDomain) (xi : ℂ) (p q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi (p + q) =
      crouzeixPolynomialBoundaryPhaseTransform Omega xi p +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi q := by
  unfold crouzeixPolynomialBoundaryPhaseTransform
  have hfun :
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma (p + q)) *
          (sigma - xi)⁻¹) =
        fun sigma ↦
          star (sigma - xi) * star (Polynomial.eval sigma p) *
              (sigma - xi)⁻¹ +
            star (sigma - xi) * star (Polynomial.eval sigma q) *
              (sigma - xi)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_add, star_add]
    ring
  rw [hfun, contourIntegral_add
    (contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
      Omega xi p)
    (contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
      Omega xi q)]
  ring

/-- The boundary phase transform is conjugate-homogeneous in its polynomial
argument. -/
theorem crouzeixPolynomialBoundaryPhaseTransform_smul
    (Omega : SmoothJordanDomain) (xi a : ℂ) (q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi (a • q) =
      star a * crouzeixPolynomialBoundaryPhaseTransform Omega xi q := by
  unfold crouzeixPolynomialBoundaryPhaseTransform
  have hfun :
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma (a • q)) *
          (sigma - xi)⁻¹) =
        fun sigma ↦ star a •
          (star (sigma - xi) * star (Polynomial.eval sigma q) *
            (sigma - xi)⁻¹) := by
    funext sigma
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, contourIntegral_smul]
  simp only [smul_eq_mul]
  ring

/-- The boundary phase transform of the zero polynomial vanishes. -/
@[simp] theorem crouzeixPolynomialBoundaryPhaseTransform_zero
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi 0 = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialBoundaryPhaseTransform_smul
      Omega xi 0 (0 : Polynomial ℂ))

/-- Degree-zero polynomials satisfy the sharp boundary-phase inequality
automatically: their divided difference and hence their phase transform
vanish.  This is the base case for any induction through the lower-degree
phase contour. -/
theorem
    norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hp : p.natDegree = 0) (xi : ℂ) :
    ‖star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  have hfrontier : (frontier Omega.carrier).Nonempty := by
    refine ⟨Omega.boundaryParam 0, ?_⟩
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  rw [Polynomial.eq_C_of_natDegree_eq_zero hp]
  have hdiv :
      Polynomial.C (p.coeff 0) /ₘ
          (Polynomial.X - Polynomial.C xi) = 0 := by
    apply (Polynomial.divByMonic_eq_zero_iff
      (Polynomial.monic_X_sub_C xi)).2
    rw [Polynomial.degree_X_sub_C]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  rw [hdiv, crouzeixPolynomialBoundaryPhaseTransform_zero,
    add_zero, Polynomial.eval_C, norm_star,
    polynomialSupNorm_C_of_nonempty _ hfrontier]

/-- The exact remaining sharp frontier inequality for the lower-degree phase
transform implies the sharp scalar-companion contraction in the carrier. -/
theorem
    norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Filter.Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_regularized_boundary
    Omega p hbounded hkernel hreg
  · intro xi hxi
    rw [
      crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
    exact hphase xi hxi
  · exact hz

/-- Under the same sharp phase inequality, the canonical Plemelj extension
is contractive on the entire closed domain. -/
theorem
    norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Filter.Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  apply norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
    Omega p (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      hbounded
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
        Omega p hkernel hreg)
      (fun _ hw ↦
        crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hw)
      (fun xi hxi ↦ ?_) hz
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      Omega p hkernel hreg hxi,
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
  exact hphase xi hxi

/-- A boundary-speed bound controls the regularized self-value by the
frontier sup norm of the divided-difference polynomial. -/
theorem norm_crouzeixPolynomialScalarCompanionRegularized_self_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (D * polynomialSupNorm
            (p /ₘ (Polynomial.X - Polynomial.C xi))
            (frontier Omega.carrier))) := by
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
  have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        ((star (Polynomial.eval (Omega.boundaryParam t) p) -
            star (Polynomial.eval xi p)) *
          (Omega.boundaryParam t - xi)⁻¹)‖ ≤
        D * polynomialSupNorm q (frontier Omega.carrier) := by
    intro t ht
    by_cases hzero : Omega.boundaryParam t = xi
    · simp only [hzero, sub_self, inv_zero, mul_zero, smul_zero, norm_zero]
      exact mul_nonneg hD_nonneg (polynomialSupNorm_nonneg q _)
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
      rw [hstar]
      simp only [smul_eq_mul, norm_mul, norm_star, norm_inv]
      calc
        ‖deriv Omega.boundaryParam t‖ *
              ((‖Omega.boundaryParam t - xi‖ *
                  ‖Polynomial.eval (Omega.boundaryParam t) q‖) *
                ‖Omega.boundaryParam t - xi‖⁻¹) =
            ‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t) q‖ := by
          calc
            _ = ‖deriv Omega.boundaryParam t‖ *
                (‖Polynomial.eval (Omega.boundaryParam t) q‖ *
                  (‖Omega.boundaryParam t - xi‖ *
                    ‖Omega.boundaryParam t - xi‖⁻¹)) := by ring
            _ = _ := by rw [mul_inv_cancel₀ hdiffNorm, mul_one]
        _ ≤ D * polynomialSupNorm q (frontier Omega.carrier) :=
          mul_le_mul (hD t ht)
            (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega q t)
            (norm_nonneg _) hD_nonneg
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)

/-- A boundary-speed bound controls the named phase transform directly by
the frontier sup norm of its polynomial argument. -/
theorem norm_crouzeixPolynomialBoundaryPhaseTransform_le
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialBoundaryPhaseTransform Omega xi q‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (D * polynomialSupNorm q (frontier Omega.carrier))) := by
  rw [crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul]
  have h := norm_crouzeixPolynomialScalarCompanionRegularized_self_le
    Omega ((Polynomial.X - Polynomial.C xi) * q) xi hD_nonneg hD
  have hquot :
      (Polynomial.X - Polynomial.C xi) * q /ₘ
          (Polynomial.X - Polynomial.C xi) = q :=
    Polynomial.mul_divByMonic_cancel_left q
      (Polynomial.monic_X_sub_C xi)
  rw [hquot] at h
  exact h

/-- One nonnegative constant depending only on the smooth Jordan domain
controls every regularized self-value. -/
theorem
    exists_uniform_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (xi : ℂ),
      ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun p xi ↦
    norm_crouzeixPolynomialScalarCompanionRegularized_self_le
      Omega p xi hD_nonneg hD⟩

/-- One nonnegative domain-only speed constant controls every boundary phase
transform, uniformly in its base point and polynomial argument. -/
theorem exists_uniform_norm_crouzeixPolynomialBoundaryPhaseTransform_le
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (xi : ℂ) (q : Polynomial ℂ),
      ‖crouzeixPolynomialBoundaryPhaseTransform Omega xi q‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm q (frontier Omega.carrier))) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun xi q ↦
    norm_crouzeixPolynomialBoundaryPhaseTransform_le
      Omega xi q hD_nonneg hD⟩

/-- At a frontier point, the explicit Plemelj value is bounded by the
polynomial frontier sup norm plus the divided-difference remainder bound. -/
theorem norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) +
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  calc
    ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
        ‖star (Polynomial.eval xi p)‖ +
          ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ :=
      norm_add_le _ _
    _ ≤ polynomialSupNorm p (frontier Omega.carrier) +
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by
      apply add_le_add
      · rw [norm_star]
        exact norm_eval_le_polynomialSupNorm p
          (bddAbove_norm_eval_image_of_isCompact p Omega.isCompact_frontier)
          hxi
      · exact norm_crouzeixPolynomialScalarCompanionRegularized_self_le
          Omega p xi hD_nonneg hD

/-- A single domain-only speed constant gives the preceding boundary-value
bound for every polynomial and every frontier point. -/
theorem exists_uniform_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (xi : ℂ),
      xi ∈ frontier Omega.carrier →
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
        polynomialSupNorm p (frontier Omega.carrier) +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
            (2 * Real.pi *
              (D * polynomialSupNorm
                (p /ₘ (Polynomial.X - Polynomial.C xi))
                (frontier Omega.carrier))) := by
  obtain ⟨D, hD_nonneg, hD⟩ := exists_nonneg_bound_boundaryParam_deriv Omega
  exact ⟨D, hD_nonneg, fun p xi hxi ↦
    norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
      Omega p hxi hD_nonneg hD⟩

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
