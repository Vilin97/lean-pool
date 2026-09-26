/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPhaseInduction
public import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionRadial

/-!
# The boundary double-layer probability density

For a boundary point `xi` and a smooth parametrization `gamma`, the scalar
double-layer density is

`rho_xi(t) = Im (gamma'(t) / (gamma(t) - xi)) / pi`.

The Crouzeix--Palencia boundary companion is integration of the conjugate
polynomial datum against this density.  The key cancellation is exact: the
second half of the double-layer kernel is the conjugate of the contour of a
polynomial divided difference, hence integrates to zero on the closed curve.

Consequently, integrability, nonnegativity, and unit mass of this explicit
density imply the sharp boundary-phase contraction.  This file isolates
those two geometric facts rather than assuming the contraction itself.

## Main declarations

* `crouzeixBoundaryDoubleLayerDensity` -- the explicit real density;
* `contourIntegral_polynomial_eval_eq_zero` -- polynomial contours vanish on
  every smooth closed boundary;
* `crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity`
  -- the exact probability-integral representation;
* `crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity` -- sharp
  phase contractivity from nonnegativity and unit mass;
* `crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support`
  -- the sharp invariant from unit mass and oriented support alone.
-/

@[expose] public section

open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

/-- The real scalar double-layer density based at `xi`.  At the (measure-zero)
parameter values where the boundary trace equals `xi`, Mathlib's inverse at
zero makes this definition zero. -/
noncomputable def crouzeixBoundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ) : ℝ :=
  (deriv Omega.boundaryParam t *
    (Omega.boundaryParam t - xi)⁻¹).im / Real.pi

/-- Unit interval-integral mass forces integrability.  This uses the Bochner
integral convention that a nonintegrable function has integral zero, so the
nonzero mass hypothesis already contains the required integrability datum. -/
theorem
    intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
    (Omega : SmoothJordanDomain) (xi : ℂ)
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1) :
    IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  by_contra hnot
  have hzero : (∫ t in Ioc (0 : ℝ) (2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 0 :=
    integral_undef hnot
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, hzero] at hmass
  norm_num at hmass

/-- An oriented supporting-normal inequality at the boundary trace makes the
scalar double-layer density nonnegative.  This records the exact orientation
data absent from the bare `SmoothJordanDomain` structure. -/
theorem crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ)
    (hsupport :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (xi - Omega.boundaryParam t)).re ≤ 0) :
    0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t := by
  let D := deriv Omega.boundaryParam t
  let d := Omega.boundaryParam t - xi
  have hnormal : ((starRingEnd ℂ) (-I * D) * (-d)).re ≤ 0 := by
    simpa only [D, d, neg_sub] using hsupport
  have him : 0 ≤ (D * d⁻¹).im := by
    by_cases hd : d = 0
    · rw [hd, inv_zero, mul_zero, zero_im]
    have hnum : 0 ≤ D.im * d.re - D.re * d.im := by
      have hid : ((starRingEnd ℂ) (-I * D) * (-d)).re =
          -(D.im * d.re - D.re * d.im) := by
        simp only [map_mul, map_neg, Complex.conj_I, Complex.mul_re,
          Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im, Complex.conj_re, Complex.conj_im]
        ring
      rw [hid] at hnormal
      linarith
    rw [← div_eq_mul_inv, Complex.div_im, ← sub_div]
    exact div_nonneg hnum (Complex.normSq_nonneg d)
  exact div_nonneg him Real.pi_pos.le

/-- The real density is the difference of the two conjugate Cauchy kernels
with the standard `1 / (2 pi i)` normalization. -/
theorem ofReal_crouzeixBoundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ) :
    (crouzeixBoundaryDoubleLayerDensity Omega xi t : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹ -
          star (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹)) := by
  let a := deriv Omega.boundaryParam t *
    (Omega.boundaryParam t - xi)⁻¹
  change (((a.im / Real.pi : ℝ) : ℂ)) =
    (2 * (Real.pi : ℂ) * I)⁻¹ * (a - star a)
  rw [Complex.star_def, RCLike.sub_conj]
  change (((a.im / Real.pi : ℝ) : ℂ)) =
    (2 * (Real.pi : ℂ) * I)⁻¹ * (2 * (a.im : ℂ) * I)
  rw [ofReal_div]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-- The contour integral of a complex polynomial vanishes on every smooth
closed boundary. -/
theorem contourIntegral_polynomial_eval_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral (fun z => Polynomial.eval z p) Omega.boundaryParam = 0 := by
  have hfun :
      (fun z : ℂ => Polynomial.eval z p) =
        fun z => ∑ i ∈ Finset.range (p.natDegree + 1),
          z ^ i * p.coeff i := by
    funext z
    rw [Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  exact contourIntegral_finset_sum_pow_mul_eq_zero
    Omega (Finset.range (p.natDegree + 1)) id p.coeff

/-- The Plemelj boundary value is the conjugate polynomial boundary datum
integrated against the scalar double-layer density, provided that density is
integrable and has unit mass.  The analytic half of the kernel cancels as a
closed polynomial contour. -/
theorem
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier)
    (hrho : IntervalIntegrable
      (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi))
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        (crouzeixBoundaryDoubleLayerDensity Omega xi t : ℂ) *
          star (Polynomial.eval (Omega.boundaryParam t) p) := by
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  let gamma := Omega.boundaryParam
  let rho := crouzeixBoundaryDoubleLayerDensity Omega xi
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have heval : ∀ z : ℂ,
      Polynomial.eval z p - Polynomial.eval xi p =
        (z - xi) * Polynomial.eval z q := by
    intro z
    have hpoly : Polynomial.C (Polynomial.eval xi p) +
        (Polynomial.X - Polynomial.C xi) * q = p := by
      dsimp only [q]
      rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
      exact Polynomial.modByMonic_add_div p
        (Polynomial.X - Polynomial.C xi)
    have h := congrArg (Polynomial.eval z) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  have hrhoC : IntervalIntegrable (fun t => (rho t : ℂ))
      volume 0 (2 * Real.pi) := by
    constructor
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc 0 (2 * Real.pi)) volume
      exact Complex.ofRealCLM.integrable_comp hrho.1
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc (2 * Real.pi) 0) volume
      exact Complex.ofRealCLM.integrable_comp hrho.2
  have hpcont : Continuous (fun t : ℝ =>
      star (Polynomial.eval (gamma t) p)) := by
    exact p.continuous.comp
      Omega.boundaryParam_contDiff.continuous |>.star
  have hweighted : IntervalIntegrable
      (fun t => (rho t : ℂ) * star (Polynomial.eval (gamma t) p))
      volume 0 (2 * Real.pi) :=
    hrhoC.mul_continuousOn hpcont.continuousOn
  have hdiffWeighted : IntervalIntegrable
      (fun t => (rho t : ℂ) *
        (star (Polynomial.eval (gamma t) p) -
          star (Polynomial.eval xi p)))
      volume 0 (2 * Real.pi) := by
    apply hrhoC.mul_continuousOn
    exact (hpcont.sub continuous_const).continuousOn
  let u : ℝ → ℂ := fun t => deriv gamma t *
    ((star (Polynomial.eval (gamma t) p) - star (Polynomial.eval xi p)) *
      (gamma t - xi)⁻¹)
  let v : ℝ → ℂ := fun t =>
    deriv gamma t * Polynomial.eval (gamma t) q
  have hu : IntervalIntegrable u volume 0 (2 * Real.pi) := by
    have h :=
      contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
        Omega p xi
    change IntervalIntegrable
      (fun t => deriv gamma t *
        ((star (Polynomial.eval (gamma t) p) -
            star (Polynomial.eval xi p)) * (gamma t - xi)⁻¹))
      volume 0 (2 * Real.pi) at h
    exact h
  have hv : IntervalIntegrable v volume 0 (2 * Real.pi) := by
    have hcontour : ContourIntegrable
        (fun z => Polynomial.eval z q) gamma := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact
          (Omega.boundaryParam_contDiff.continuous_deriv
            (by norm_num)).continuousOn
      · exact q.continuous.continuousOn
    change IntervalIntegrable
      (fun t => deriv gamma t * Polynomial.eval (gamma t) q)
      volume 0 (2 * Real.pi) at hcontour
    exact hcontour
  have hvstar : IntervalIntegrable (fun t => star (v t))
      volume 0 (2 * Real.pi) := by
    constructor
    · change IntegrableOn (fun t =>
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap (v t))
        (Ioc 0 (2 * Real.pi)) volume
      exact
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.integrable_comp
          hv.1
    · change IntegrableOn (fun t =>
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap (v t))
        (Ioc (2 * Real.pi) 0) volume
      exact
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.integrable_comp
          hv.2
  have hvzero : (∫ t in (0 : ℝ)..(2 * Real.pi), v t) = 0 := by
    simpa only [v, gamma, contourIntegral, smul_eq_mul] using
      contourIntegral_polynomial_eval_eq_zero Omega q
  have hpoint : ∀ t, gamma t ≠ xi →
      (rho t : ℂ) *
          (star (Polynomial.eval (gamma t) p) -
            star (Polynomial.eval xi p)) =
        c * (u t - star (v t)) := by
    intro t hne
    rw [show (rho t : ℂ) =
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          (deriv Omega.boundaryParam t *
              (Omega.boundaryParam t - xi)⁻¹ -
            star (deriv Omega.boundaryParam t *
              (Omega.boundaryParam t - xi)⁻¹)) by
          exact ofReal_crouzeixBoundaryDoubleLayerDensity Omega xi t]
    dsimp only [c, u, v, gamma]
    rw [← star_sub, heval]
    simp only [star_mul]
    have hd : Omega.boundaryParam t - xi ≠ 0 := sub_ne_zero.mpr hne
    have hstarCancel :
        star ((Omega.boundaryParam t - xi)⁻¹) *
          star (Omega.boundaryParam t - xi) = 1 :=
      by
        rw [star_inv₀, inv_mul_cancel₀ (star_ne_zero.mpr hd)]
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ *
            (deriv Omega.boundaryParam t *
                (Omega.boundaryParam t - xi)⁻¹ -
              star ((Omega.boundaryParam t - xi)⁻¹) *
                star (deriv Omega.boundaryParam t)) *
          (star (Polynomial.eval (Omega.boundaryParam t) q) *
            star (Omega.boundaryParam t - xi)) =
          (2 * (Real.pi : ℂ) * I)⁻¹ *
            (deriv Omega.boundaryParam t *
                ((star (Polynomial.eval (Omega.boundaryParam t) q) *
                    star (Omega.boundaryParam t - xi)) *
                  (Omega.boundaryParam t - xi)⁻¹) -
              star (Polynomial.eval (Omega.boundaryParam t) q) *
                star (deriv Omega.boundaryParam t) *
                  (star ((Omega.boundaryParam t - xi)⁻¹) *
                    star (Omega.boundaryParam t - xi))) := by
        ring
      _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
          (deriv Omega.boundaryParam t *
              ((star (Polynomial.eval (Omega.boundaryParam t) q) *
                  star (Omega.boundaryParam t - xi)) *
                (Omega.boundaryParam t - xi)⁻¹) -
            star (Polynomial.eval (Omega.boundaryParam t) q) *
              star (deriv Omega.boundaryParam t)) := by
        rw [hstarCancel, mul_one]
  have hdiffIntegral :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (rho t : ℂ) *
          (star (Polynomial.eval (gamma t) p) -
            star (Polynomial.eval xi p))) =
        c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
    calc
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          (rho t : ℂ) *
            (star (Polynomial.eval (gamma t) p) -
              star (Polynomial.eval xi p))) =
          ∫ t in (0 : ℝ)..(2 * Real.pi), c * (u t - star (v t)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [ae_boundaryParam_ne_of_mem_frontier Omega hxi]
          with t ht
        intro _ht
        exact hpoint t (ht _ht)
      _ = c * ((∫ t in (0 : ℝ)..(2 * Real.pi), u t) -
          ∫ t in (0 : ℝ)..(2 * Real.pi), star (v t)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hu hvstar]
      _ = c * ((∫ t in (0 : ℝ)..(2 * Real.pi), u t) -
          star (∫ t in (0 : ℝ)..(2 * Real.pi), v t)) := by
        rw [show (∫ t in (0 : ℝ)..(2 * Real.pi), star (v t)) =
            star (∫ t in (0 : ℝ)..(2 * Real.pi), v t) by
          change (∫ t in (0 : ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (v t)) =
              (starRingEnd ℂ) (∫ t in (0 : ℝ)..(2 * Real.pi), v t)
          exact intervalIntegral.intervalIntegral_conj]
      _ = c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
        rw [hvzero, star_zero, sub_zero]
  have hsplit :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (rho t : ℂ) * star (Polynomial.eval (gamma t) p)) =
        star (Polynomial.eval xi p) +
          c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
    have hconst : IntervalIntegrable
        (fun t => star (Polynomial.eval xi p) * (rho t : ℂ))
        volume 0 (2 * Real.pi) := hrhoC.const_mul _
    have hfun :
        (fun t => (rho t : ℂ) * star (Polynomial.eval (gamma t) p)) =
          fun t => star (Polynomial.eval xi p) * (rho t : ℂ) +
            (rho t : ℂ) *
              (star (Polynomial.eval (gamma t) p) -
                star (Polynomial.eval xi p)) := by
      funext t
      ring
    rw [hfun, intervalIntegral.integral_add hconst hdiffWeighted,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, hmass, ofReal_one, mul_one,
      hdiffIntegral]
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  unfold crouzeixPolynomialScalarCompanionRegularized
  change star (Polynomial.eval xi p) +
      c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) = _
  simpa only [rho, gamma] using hsplit.symm

/-- Integration of conjugate polynomial boundary data against a nonnegative
unit-mass double-layer density is contractive for the frontier sup norm. -/
theorem
    norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier)
    (hrho : IntervalIntegrable
      (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi))
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  let rho := crouzeixBoundaryDoubleLayerDensity Omega xi
  let M := polynomialSupNorm p (frontier Omega.carrier)
  have hrhoC : IntervalIntegrable (fun t => (rho t : ℂ))
      volume 0 (2 * Real.pi) := by
    constructor
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc 0 (2 * Real.pi)) volume
      exact Complex.ofRealCLM.integrable_comp hrho.1
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc (2 * Real.pi) 0) volume
      exact Complex.ofRealCLM.integrable_comp hrho.2
  have hpcont : Continuous (fun t : ℝ =>
      star (Polynomial.eval (Omega.boundaryParam t) p)) :=
    p.continuous.comp Omega.boundaryParam_contDiff.continuous |>.star
  have hweighted : IntervalIntegrable
      (fun t => (rho t : ℂ) *
        star (Polynomial.eval (Omega.boundaryParam t) p))
      volume 0 (2 * Real.pi) :=
    hrhoC.mul_continuousOn hpcont.continuousOn
  have hweightedOn : Integrable
      (fun t => (rho t : ℂ) *
        star (Polynomial.eval (Omega.boundaryParam t) p))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp hweighted
  have hrhoOn : Integrable rho
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp hrho
  have hrhs : Integrable (fun t => rho t * M)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    hrhoOn.mul_const M
  have hpoint : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))),
      ‖(rho t : ℂ) *
          star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤
        rho t * M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hrho_nonneg : 0 ≤ rho t := hpos t ht
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrho_nonneg]
    exact mul_le_mul_of_nonneg_left
      (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega p t)
      hrho_nonneg
  rw [
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
      Omega p hxi hrho hmass,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    (∫ t in Ioc (0 : ℝ) (2 * Real.pi),
        ‖(rho t : ℂ) *
          star (Polynomial.eval (Omega.boundaryParam t) p)‖) ≤
        ∫ t in Ioc (0 : ℝ) (2 * Real.pi), rho t * M :=
      integral_mono_ae hweightedOn.norm hrhs hpoint
    _ = M := by
      rw [integral_mul_const,
        ← intervalIntegral.integral_of_le Real.two_pi_pos.le, hmass,
        one_mul]

/-- Nonnegativity and unit mass of the explicit boundary double-layer
density imply the sharp boundary-phase invariant. -/
theorem crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hrho : ∀ xi ∈ frontier Omega.carrier,
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi))
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hpos : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  intro xi hxi
  rw [←
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
  exact
    norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
      Omega p hxi (hrho xi hxi) (hmass xi hxi) (hpos xi hxi)

/-- The sharp boundary-phase invariant follows directly from integrability,
unit mass, and the oriented supporting-normal inequality on the frontier.
The pointwise density sign is discharged algebraically. -/
theorem
    crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hrho : ∀ xi ∈ frontier Omega.carrier,
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi))
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hsupport : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (xi - Omega.boundaryParam t)).re ≤ 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  apply crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
    Omega p hrho hmass
  intro xi hxi t ht
  exact crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
    Omega xi t (hsupport xi hxi t ht)

/-- Unit mass and oriented frontier support alone imply the sharp
boundary-phase invariant.  A separate integrability assumption is redundant:
mass one rules out the nonintegrable zero-integral convention. -/
theorem
    crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hsupport : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (xi - Omega.boundaryParam t)).re ≤ 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  apply
    crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
      Omega p
  · intro xi hxi
    exact
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
        Omega xi (hmass xi hxi)
  · exact hmass
  · exact hsupport

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
