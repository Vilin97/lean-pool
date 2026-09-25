/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.PalenciaSupport
public import LeanPool.OperatorTheory.Operator.Crouzeix.ProductBase
public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionCircle
public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPlemelj

/-!
# The regularized Plemelj identity on a circle

This file discharges the regularized boundary-value inputs from
`ScalarCompanionPlemelj` in the centered-disk model.  If `xi` lies on the
circle and

`q = p /ₘ (X - C xi)`,

then polynomial division and the circle reflection identity turn the
cancelled boundary integrand into a constant multiple of the scalar
companion of `q` at zero.  The landed circle calculation evaluates that
companion exactly.

## Main declarations

* `crouzeixScalarCauchyKernel_ball_eq_one` -- winding normalization inside a
  centered disk.
* `crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq` -- the
  exact cancelled boundary integral.
* `tendsto_crouzeixPolynomialScalarCompanionRegularized_ball` -- regularized
  convergence at every circle point.
* `crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero` -- the
  explicit Plemelj value is the conjugate polynomial value at the center.
* `crouzeixPolynomialScalarCompanionClosedExtension_ball_eq_eval_zero` -- the
  canonical extension has that constant value on the closed disk.
* The corresponding declarations containing `_ball_center_` give all of
  these results for an arbitrary disk center.
* `crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq` --
  the canonical scalar companion produces the polynomial auxiliary operator.
* `exists_continuous_scalarCompanion_approximation_ball_center` -- the full
  continuous, contractive, polynomially approximable companion data on a disk.
* `exists_tendsto_polynomial_companions_ball_center` -- an exactly contractive
  constant polynomial sequence converging to the auxiliary operator.
-/

@[expose] public section

open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real

/-- The normalized scalar Cauchy kernel of a positively oriented centered
circle is one throughout its interior. -/
theorem crouzeixScalarCauchyKernel_ball_eq_one
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    crouzeixScalarCauchyKernel (SmoothJordanDomain.ball 0 R hR) z = 1 := by
  have hcomp := crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
    hR (Polynomial.C 1) hz
  simpa only [crouzeixPolynomialScalarCompanion, crouzeixScalarCauchyKernel,
    Polynomial.eval_C, star_one, one_mul] using hcomp

private theorem star_eq_sq_mul_inv_of_mem_centered_sphere
    {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) |R|) :
    star z = (R : ℂ) ^ 2 * z⁻¹ := by
  rw [← range_circleMap] at hz
  obtain ⟨t, rfl⟩ := hz
  change conj (circleMap 0 R t) = _
  rw [conj_circleMap_zero, circleMap_zero_inv]
  simp only [circleMap_zero, ofReal_neg, neg_mul, ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hR.ne']

private theorem ne_zero_of_mem_centered_sphere
    {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) |R|) : z ≠ 0 := by
  intro hzero
  rw [hzero, Metric.mem_sphere, dist_self, abs_of_pos hR] at hz
  linarith

/-- On a centered circle, the cancelled transform evaluated at its boundary
point is exactly the difference between the conjugate center and boundary
values of the polynomial. -/
theorem crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball 0 R hR) p xi xi =
      star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := by
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
  have hxi' : xi ∈ Metric.sphere (0 : ℂ) |R| := by
    simpa only [abs_of_pos hR] using hxi
  let c : ℂ := -((R : ℂ) ^ 2) * xi⁻¹
  have hintegral :
      circleIntegral
          (fun sigma ↦
            (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - xi)⁻¹)
          0 R =
        circleIntegral
          (fun sigma ↦ c *
            (star (Polynomial.eval sigma q) * sigma⁻¹))
          0 R := by
    apply circleIntegral.circleIntegral_congr_codiscreteWithin
    · filter_upwards [compl_singleton_mem_codiscreteWithin
          (s := Metric.sphere (0 : ℂ) |R|) xi,
        Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |R|)]
        with sigma hsigma_ne hsigma
      have hsigma_ne' : sigma ≠ xi := by simpa only [mem_compl_iff, mem_singleton_iff] using
        hsigma_ne
      have hsigma0 := ne_zero_of_mem_centered_sphere hR hsigma
      have hxi0 := ne_zero_of_mem_centered_sphere hR hxi'
      have hstar_sigma := star_eq_sq_mul_inv_of_mem_centered_sphere hR hsigma
      have hstar_xi := star_eq_sq_mul_inv_of_mem_centered_sphere hR hxi'
      have hstar_eval :
          star (Polynomial.eval sigma p) - star (Polynomial.eval xi p) =
            star (sigma - xi) * star (Polynomial.eval sigma q) := by
        rw [← star_sub, heval sigma, star_mul]
        ring
      rw [hstar_eval, star_sub, hstar_sigma, hstar_xi]
      dsimp only [c]
      field_simp [hsigma0, hxi0, hsigma_ne']
      all_goals ring
    · exact hR.ne'
  have hqcomp := crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
    hR q (Metric.mem_ball_self hR)
  have hqintegral :
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦ star (Polynomial.eval sigma q) * sigma⁻¹) 0 R =
        star (Polynomial.eval 0 q) := by
    unfold crouzeixPolynomialScalarCompanion at hqcomp
    change (2 * (Real.pi : ℂ) * I)⁻¹ *
        contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma q) * (sigma - 0)⁻¹)
          (circleMap 0 R) = star (Polynomial.eval 0 q) at hqcomp
    rw [contourIntegral_circleMap] at hqcomp
    simpa only [sub_zero] using hqcomp
  have hcq : c * star (Polynomial.eval 0 q) =
      star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := by
    have h0 := heval 0
    calc
      c * star (Polynomial.eval 0 q) =
          star (-xi * Polynomial.eval 0 q) := by
        rw [star_mul, star_neg,
          star_eq_sq_mul_inv_of_mem_centered_sphere hR hxi']
        dsimp only [c]
        ring
      _ = star (Polynomial.eval 0 p - Polynomial.eval xi p) := by
        rw [h0, zero_sub]
      _ = star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := star_sub _ _
  change (2 * (Real.pi : ℂ) * I)⁻¹ *
      circleIntegral
        (fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - xi)⁻¹)
        0 R = _
  rw [hintegral, circleIntegral.integral_const_mul]
  calc
    (2 * (Real.pi : ℂ) * I)⁻¹ *
          (c * circleIntegral
            (fun sigma ↦ star (Polynomial.eval sigma q) * sigma⁻¹) 0 R) =
        c * ((2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦ star (Polynomial.eval sigma q) * sigma⁻¹) 0 R) := by ring
    _ = c * star (Polynomial.eval 0 q) := by rw [hqintegral]
    _ = star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := hcq

/-- On a centered disk, the regularized transform converges at every
frontier point to its explicitly evaluated boundary integral. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_ball
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball 0 R hR) p xi)
      (nhdsWithin xi (Metric.ball (0 : ℂ) R))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball 0 R hR) p xi xi)) := by
  have hboundary :=
    crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq hR p hxi
  have heq :
      crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball 0 R hR) p xi =ᶠ[
            nhdsWithin xi (Metric.ball (0 : ℂ) R)]
        fun _ ↦ star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzfrontier : z ∉ frontier
        (SmoothJordanDomain.ball 0 R hR).carrier := by
      intro hfrontier
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← (SmoothJordanDomain.ball 0 R hR).isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hfrontier⟩
      exact hempty
    have hdecomp := crouzeixPolynomialScalarCompanion_eq_regularized_add
      (SmoothJordanDomain.ball 0 R hR) p xi
      hzfrontier
    rw [crouzeixPolynomialScalarCompanion_ball_eq_eval_zero hR p hz,
      crouzeixScalarCauchyKernel_ball_eq_one hR hz, mul_one] at hdecomp
    rw [hdecomp]
    ring
  rw [hboundary]
  exact tendsto_const_nhds.congr' heq.symm

/-- The explicit regularized Plemelj value on a centered circle is the
conjugate polynomial value at the disk center. -/
theorem crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionBoundaryValue
        (SmoothJordanDomain.ball 0 R hR) p xi =
      star (Polynomial.eval 0 p) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq hR p hxi]
  ring

/-- The canonical scalar-companion extension is continuous on the closed
centered disk, now obtained through the regularized Plemelj interface. -/
theorem
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball 0 R hR) p)
      (Metric.closedBall (0 : ℂ) R) := by
  have hcont :=
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
      (SmoothJordanDomain.ball 0 R hR) p
      (fun z hz ↦ crouzeixScalarCauchyKernel_ball_eq_one hR hz)
      (fun xi hxi ↦ by
        apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball hR p
        change xi ∈ frontier (Metric.ball (0 : ℂ) R) at hxi
        rwa [frontier_ball 0 hR.ne'] at hxi)
  rw [show (SmoothJordanDomain.ball 0 R hR).carrier =
      Metric.ball (0 : ℂ) R by rfl,
    closure_ball 0 hR.ne'] at hcont
  exact hcont

/-- The canonical closed extension of the centered-disk companion is the
constant `star (p.eval 0)` on the entire closed disk. -/
theorem crouzeixPolynomialScalarCompanionClosedExtension_ball_eq_eval_zero
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball 0 R hR) p z =
      star (Polynomial.eval 0 p) := by
  rw [← Metric.ball_union_sphere] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq
      (SmoothJordanDomain.ball 0 R hR) p hz,
      crouzeixPolynomialScalarCompanion_ball_eq_eval_zero hR p hz]
  · have hkernel : ∀ w ∈ (SmoothJordanDomain.ball 0 R hR).carrier,
        crouzeixScalarCauchyKernel (SmoothJordanDomain.ball 0 R hR) w = 1 :=
      fun w hw ↦ crouzeixScalarCauchyKernel_ball_eq_one hR hw
    have hreg : ∀ xi ∈ frontier (SmoothJordanDomain.ball 0 R hR).carrier,
        Tendsto
          (crouzeixPolynomialScalarCompanionRegularized
            (SmoothJordanDomain.ball 0 R hR) p xi)
          (nhdsWithin xi (SmoothJordanDomain.ball 0 R hR).carrier)
          (nhds
            (crouzeixPolynomialScalarCompanionRegularized
              (SmoothJordanDomain.ball 0 R hR) p xi xi)) := by
      intro xi hxi
      apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball hR p
      change xi ∈ frontier (Metric.ball (0 : ℂ) R) at hxi
      rwa [frontier_ball 0 hR.ne'] at hxi
    have hzfrontier : z ∈ frontier
        (SmoothJordanDomain.ball 0 R hR).carrier := by
      change z ∈ frontier (Metric.ball (0 : ℂ) R)
      rwa [frontier_ball 0 hR.ne']
    rw [crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      (SmoothJordanDomain.ball 0 R hR) p hkernel hreg hzfrontier,
      crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero hR p hz]

/-- The normalized scalar Cauchy kernel is one throughout the interior of an
arbitrarily centered positively oriented circle. -/
theorem crouzeixScalarCauchyKernel_ball_center_eq_one
    (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    crouzeixScalarCauchyKernel (SmoothJordanDomain.ball c R hR) z = 1 := by
  have hcomp := crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
    c hR (Polynomial.C 1) hz
  simpa only [crouzeixPolynomialScalarCompanion, crouzeixScalarCauchyKernel,
    Polynomial.eval_C, star_one, one_mul] using hcomp

private theorem star_sub_center_eq_sq_mul_inv_of_mem_sphere
    (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere c |R|) :
    star (z - c) = (R : ℂ) ^ 2 * (z - c)⁻¹ := by
  apply star_eq_sq_mul_inv_of_mem_centered_sphere hR
  rw [Metric.mem_sphere, dist_zero_right]
  simpa only [Metric.mem_sphere, dist_eq_norm] using hz

private theorem sub_center_ne_zero_of_mem_sphere
    (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere c |R|) : z - c ≠ 0 := by
  apply ne_zero_of_mem_centered_sphere hR
  rw [Metric.mem_sphere, dist_zero_right]
  simpa only [Metric.mem_sphere, dist_eq_norm] using hz

/-- On an arbitrary circle, the cancelled transform at a boundary point is
the difference between the conjugate polynomial values at the center and at
that boundary point. -/
theorem
    crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball c R hR) p xi xi =
      star (Polynomial.eval c p) - star (Polynomial.eval xi p) := by
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
  have hxi' : xi ∈ Metric.sphere c |R| := by
    simpa only [abs_of_pos hR] using hxi
  let factor : ℂ := -((R : ℂ) ^ 2) * (xi - c)⁻¹
  have hintegral :
      circleIntegral
          (fun sigma ↦
            (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - xi)⁻¹)
          c R =
        circleIntegral
          (fun sigma ↦ factor *
            (star (Polynomial.eval sigma q) * (sigma - c)⁻¹))
          c R := by
    apply circleIntegral.circleIntegral_congr_codiscreteWithin
    · filter_upwards [compl_singleton_mem_codiscreteWithin
          (s := Metric.sphere c |R|) xi,
        Filter.self_mem_codiscreteWithin (Metric.sphere c |R|)]
        with sigma hsigma_ne hsigma
      have hsigma_ne' : sigma ≠ xi := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hsigma_ne
      have hdiff : -xi + sigma ≠ 0 := by
        simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hsigma_ne'
      have hcenterDiff : sigma - c - (xi - c) ≠ 0 := by
        simpa only [sub_sub_sub_cancel_right] using sub_ne_zero.mpr hsigma_ne'
      have hsigma0 := sub_center_ne_zero_of_mem_sphere c hR hsigma
      have hxi0 := sub_center_ne_zero_of_mem_sphere c hR hxi'
      have hstar_sigma :=
        star_sub_center_eq_sq_mul_inv_of_mem_sphere c hR hsigma
      have hstar_xi :=
        star_sub_center_eq_sq_mul_inv_of_mem_sphere c hR hxi'
      have hstar_eval :
          star (Polynomial.eval sigma p) - star (Polynomial.eval xi p) =
            star (sigma - xi) * star (Polynomial.eval sigma q) := by
        rw [← star_sub, heval sigma, star_mul]
        ring
      rw [hstar_eval, show sigma - xi = (sigma - c) - (xi - c) by ring,
        star_sub, hstar_sigma, hstar_xi]
      dsimp only [factor]
      field_simp [hsigma0, hxi0, hsigma_ne', hdiff]
      all_goals
        try field_simp [hcenterDiff]
        ring
    · exact hR.ne'
  have hqcomp := crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
    c hR q (Metric.mem_ball_self hR)
  have hqintegral :
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦
              star (Polynomial.eval sigma q) * (sigma - c)⁻¹) c R =
        star (Polynomial.eval c q) := by
    unfold crouzeixPolynomialScalarCompanion at hqcomp
    change (2 * (Real.pi : ℂ) * I)⁻¹ *
        contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma q) * (sigma - c)⁻¹)
          (circleMap c R) = star (Polynomial.eval c q) at hqcomp
    rw [contourIntegral_circleMap] at hqcomp
    exact hqcomp
  have hfactor : factor * star (Polynomial.eval c q) =
      star (Polynomial.eval c p) - star (Polynomial.eval xi p) := by
    have hc := heval c
    have hstar_cxi : star (c - xi) = factor := by
      rw [show c - xi = -(xi - c) by ring, star_neg,
        star_sub_center_eq_sq_mul_inv_of_mem_sphere c hR hxi']
      dsimp only [factor]
      ring
    calc
      factor * star (Polynomial.eval c q) =
          star ((c - xi) * Polynomial.eval c q) := by
        rw [star_mul, hstar_cxi]
        ring
      _ = star (Polynomial.eval c p - Polynomial.eval xi p) := by rw [hc]
      _ = star (Polynomial.eval c p) - star (Polynomial.eval xi p) := star_sub _ _
  change (2 * (Real.pi : ℂ) * I)⁻¹ *
      circleIntegral
        (fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - xi)⁻¹)
        c R = _
  rw [hintegral, circleIntegral.integral_const_mul]
  calc
    (2 * (Real.pi : ℂ) * I)⁻¹ *
          (factor * circleIntegral
            (fun sigma ↦
              star (Polynomial.eval sigma q) * (sigma - c)⁻¹) c R) =
        factor * ((2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦
              star (Polynomial.eval sigma q) * (sigma - c)⁻¹) c R) := by ring
    _ = factor * star (Polynomial.eval c q) := by rw [hqintegral]
    _ = star (Polynomial.eval c p) - star (Polynomial.eval xi p) := hfactor

/-- The regularized transform converges at every boundary point of an
arbitrarily centered disk. -/
theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball c R hR) p xi)
      (nhdsWithin xi (Metric.ball c R))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball c R hR) p xi xi)) := by
  have hboundary :=
    crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
      c hR p hxi
  have heq :
      crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball c R hR) p xi =ᶠ[
            nhdsWithin xi (Metric.ball c R)]
        fun _ ↦ star (Polynomial.eval c p) - star (Polynomial.eval xi p) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzfrontier : z ∉ frontier
        (SmoothJordanDomain.ball c R hR).carrier := by
      intro hfrontier
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← (SmoothJordanDomain.ball c R hR).isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hfrontier⟩
      exact hempty
    have hdecomp := crouzeixPolynomialScalarCompanion_eq_regularized_add
      (SmoothJordanDomain.ball c R hR) p xi hzfrontier
    rw [crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center c hR p hz,
      crouzeixScalarCauchyKernel_ball_center_eq_one c hR hz, mul_one] at hdecomp
    rw [hdecomp]
    ring
  rw [hboundary]
  exact tendsto_const_nhds.congr' heq.symm

/-- The explicit Plemelj value on an arbitrary circle is the conjugate
polynomial value at its center. -/
theorem
    crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    crouzeixPolynomialScalarCompanionBoundaryValue
        (SmoothJordanDomain.ball c R hR) p xi =
      star (Polynomial.eval c p) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
    c hR p hxi]
  ring

/-- The canonical scalar-companion extension is continuous on every closed
disk. -/
theorem
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball c R hR) p)
      (Metric.closedBall c R) := by
  have hcont :=
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
      (SmoothJordanDomain.ball c R hR) p
      (fun z hz ↦ crouzeixScalarCauchyKernel_ball_center_eq_one c hR hz)
      (fun xi hxi ↦ by
        apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
          c hR p
        change xi ∈ frontier (Metric.ball c R) at hxi
        rwa [frontier_ball c hR.ne'] at hxi)
  rw [show (SmoothJordanDomain.ball c R hR).carrier =
      Metric.ball c R by rfl, closure_ball c hR.ne'] at hcont
  exact hcont

/-- The canonical closed extension of the companion on `ball c R` is the
constant `star (p.eval c)` throughout `closedBall c R`. -/
theorem
    crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall c R) :
    crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball c R hR) p z =
      star (Polynomial.eval c p) := by
  rw [← Metric.ball_union_sphere] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq
      (SmoothJordanDomain.ball c R hR) p hz,
      crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center c hR p hz]
  · have hkernel : ∀ w ∈ (SmoothJordanDomain.ball c R hR).carrier,
        crouzeixScalarCauchyKernel (SmoothJordanDomain.ball c R hR) w = 1 :=
      fun w hw ↦ crouzeixScalarCauchyKernel_ball_center_eq_one c hR hw
    have hreg : ∀ xi ∈ frontier (SmoothJordanDomain.ball c R hR).carrier,
        Tendsto
          (crouzeixPolynomialScalarCompanionRegularized
            (SmoothJordanDomain.ball c R hR) p xi)
          (nhdsWithin xi (SmoothJordanDomain.ball c R hR).carrier)
          (nhds
            (crouzeixPolynomialScalarCompanionRegularized
              (SmoothJordanDomain.ball c R hR) p xi xi)) := by
      intro xi hxi
      apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
        c hR p
      change xi ∈ frontier (Metric.ball c R) at hxi
      rwa [frontier_ball c hR.ne'] at hxi
    have hzfrontier : z ∈ frontier
        (SmoothJordanDomain.ball c R hR).carrier := by
      change z ∈ frontier (Metric.ball c R)
      rwa [frontier_ball c hR.ne']
    rw [crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      (SmoothJordanDomain.ball c R hR) p hkernel hreg hzfrontier,
      crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
        c hR p hz]

section AuxiliaryOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- On a disk containing the operator in norm, feeding the canonical closed
scalar companion to the auxiliary contour gives exactly the usual
conjugate-polynomial auxiliary operator. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR)
        (crouzeixPolynomialScalarCompanionClosedExtension
          (SmoothJordanDomain.ball c R hR) p) =
      crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R hR) p := by
  let q : Polynomial ℂ := Polynomial.C (Polynomial.eval c p)
  have hclosedAux :
      crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR)
          (crouzeixPolynomialScalarCompanionClosedExtension
            (SmoothJordanDomain.ball c R hR) p) =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) q := by
    unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
    congr 1
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _
    change deriv (circleMap c R) t •
        (crouzeixPolynomialScalarCompanionClosedExtension
            (SmoothJordanDomain.ball c R hR) p (circleMap c R t) •
          resolvent A (circleMap c R t)) =
      deriv (circleMap c R) t •
        (star (Polynomial.eval (circleMap c R t) q) •
          resolvent A (circleMap c R t))
    rw [crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
      c hR p (circleMap_mem_closedBall c hR.le t)]
    simp only [q, Polynomial.eval_C]
  calc
    crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR)
        (crouzeixPolynomialScalarCompanionClosedExtension
          (SmoothJordanDomain.ball c R hR) p) =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) q := hclosedAux
    _ = star (Polynomial.eval c p) • (1 : E →L[ℂ] E) := by
      simpa only [q, Polynomial.eval_C] using
        (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
          A c hA q)
    _ = crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p := by
      symm
      simpa using
        (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
          A c hA p)

/-- The disk model supplies all scalar-companion inputs used by the published
approximation route at once.  The canonical closed extension is continuous
on the boundary and sharply contractive on the closed disk; the constant
polynomial sequence agrees with it exactly, and its auxiliary contour is the
conjugate-polynomial auxiliary operator. -/
theorem exists_continuous_scalarCompanion_approximation_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
      ContinuousOn g
          ((SmoothJordanDomain.ball c R hR).boundaryParam ''
            Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ Metric.closedBall c R,
        ‖g z‖ ≤ polynomialSupNorm p (Metric.closedBall c R)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ Metric.closedBall c R →
        ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) g =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p := by
  refine ⟨
    crouzeixPolynomialScalarCompanionClosedExtension
      (SmoothJordanDomain.ball c R hR) p,
    fun _ ↦ Polynomial.C (star (Polynomial.eval c p)), ?_, ?_, ?_, ?_⟩
  · apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
        c hR p).mono
    rintro z ⟨t, _ht, rfl⟩
    exact circleMap_mem_closedBall c hR.le t
  · intro z hz
    rw [crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
      c hR p hz, norm_star]
    exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
      (Metric.mem_closedBall_self hR.le)
  · intro j z hz
    rw [Polynomial.eval_C,
      crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
        c hR p hz,
      sub_self, norm_zero]
    positivity
  · exact
      crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
        A c hR hA p

/-- The constant polynomial representing the closed disk companion evaluates
at `A` to the conjugate-polynomial auxiliary operator.  This is the exact
functional-calculus identification behind the disk instance of the published
companion route. -/
theorem aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    Polynomial.aeval A
        (Polynomial.C (star (Polynomial.eval c p))) =
      crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R hR) p := by
  rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  symm
  simpa using
    (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
      A c hA p)

/-- On an enclosing disk, the polynomial companions required by the
published approximation route can be chosen to be a constant sequence.  It
is exactly contractive for the closed-disk sup norm and its evaluations at
`A` converge (indeed, are equal) to the canonical auxiliary operator. -/
theorem exists_tendsto_polynomial_companions_ball_center
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) (Metric.closedBall c R) ≤
        polynomialSupNorm p (Metric.closedBall c R)) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
        (nhds (crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p)) := by
  refine ⟨fun _ ↦ Polynomial.C (star (Polynomial.eval c p)), ?_, ?_⟩
  · intro _
    rw [polynomialSupNorm_C_of_nonempty _
      (Metric.nonempty_closedBall.mpr hR.le), norm_star]
    exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
      (Metric.mem_closedBall_self hR.le)
  · rw [←
      aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
        A c hR hA p]
    exact tendsto_const_nhds

end AuxiliaryOperator

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
