/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The scalar Crouzeix--Palencia companion

For a polynomial `p` and a smooth Jordan domain `Omega`, the published
Crouzeix--Palencia proof uses the scalar Cauchy companion

`g(z) = (2πi)⁻¹ ∮∂Ω conj(p(σ)) / (σ - z) dσ`.

This file defines that function using the project's parameterized contour
integral and proves it is holomorphic throughout `Omega.carrier`.  The proof
differentiates under the interval integral.  Around each interior point, an
open ball remains disjoint from the compact parametrized frontier; this gives
the uniform inverse-square bound required by the dominated derivative theorem.

The remaining sharp analytic input is not hidden here: extending the companion
continuously to the boundary and proving its sup-norm contraction require a
Plemelj boundary-value argument.

## Main declarations

* `crouzeixPolynomialScalarCompanion` -- the scalar Cauchy companion.
* `crouzeixPolynomialScalarCompanionDeriv` -- its inverse-square derivative
  integral.
* `crouzeixPolynomialScalarCompanion_smul` -- the companion and its derivative
  are conjugate-homogeneous in the polynomial.
* `crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one` -- the
  companion is the scalarization of the one-dimensional auxiliary operator.
* `norm_crouzeixPolynomialScalarCompanion_eq_norm_auxiliaryOperator` -- this
  scalarization preserves the operator norm exactly.
* `hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier` -- the
  exact derivative formula away from the boundary.
* `analyticOn_crouzeixPolynomialScalarCompanion_frontier_compl` -- the
  interior and exterior holomorphic branches.
* `hasDerivAt_crouzeixPolynomialScalarCompanion` and
  `analyticOn_crouzeixPolynomialScalarCompanion` -- their interior forms.
-/

open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

/-- The scalar Cauchy companion of `p` on a smooth Jordan domain. -/
noncomputable def crouzeixPolynomialScalarCompanion
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    contourIntegral
      (fun σ ↦ star (Polynomial.eval σ p) * (σ - z)⁻¹)
      Omega.boundaryParam

/-- The scalar integral obtained by differentiating the Cauchy companion
kernel with respect to its interior argument. -/
noncomputable def crouzeixPolynomialScalarCompanionDeriv
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p) *
          (Omega.boundaryParam t - z)⁻¹ ^ 2

/-- The scalar companion is conjugate-homogeneous in its polynomial
argument. -/
theorem crouzeixPolynomialScalarCompanion_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    crouzeixPolynomialScalarCompanion Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanion Omega p z := by
  unfold crouzeixPolynomialScalarCompanion
  have hfun :
      (fun sigma ↦ star (Polynomial.eval sigma (a • p)) * (sigma - z)⁻¹) =
        fun sigma ↦ star a •
          (star (Polynomial.eval sigma p) * (sigma - z)⁻¹) := by
    funext sigma
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, contourIntegral_smul]
  simp only [smul_eq_mul]
  ring

/-- The scalar companion of the zero polynomial vanishes identically. -/
@[simp] theorem crouzeixPolynomialScalarCompanion_zero
    (Omega : SmoothJordanDomain) (z : ℂ) :
    crouzeixPolynomialScalarCompanion Omega 0 z = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialScalarCompanion_smul Omega 0 (0 : Polynomial ℂ) z)

/-- The derivative integral of the scalar companion is likewise
conjugate-homogeneous in the polynomial. -/
theorem crouzeixPolynomialScalarCompanionDeriv_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    crouzeixPolynomialScalarCompanionDeriv Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionDeriv Omega p z := by
  unfold crouzeixPolynomialScalarCompanionDeriv
  have hfun :
      (fun t ↦ deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) (a • p)) *
          (Omega.boundaryParam t - z)⁻¹ ^ 2) =
        fun t ↦ star a •
          (deriv Omega.boundaryParam t *
            star (Polynomial.eval (Omega.boundaryParam t) p) *
              (Omega.boundaryParam t - z)⁻¹ ^ 2) := by
    funext t
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, intervalIntegral.integral_smul]
  simp only [smul_eq_mul]
  ring

/-- The derivative integral for the zero polynomial vanishes identically. -/
@[simp] theorem crouzeixPolynomialScalarCompanionDeriv_zero
    (Omega : SmoothJordanDomain) (z : ℂ) :
    crouzeixPolynomialScalarCompanionDeriv Omega 0 z = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialScalarCompanionDeriv_smul
      Omega 0 (0 : Polynomial ℂ) z)

private theorem resolvent_toSpanSingleton_apply_one_eq_inv (z sigma : ℂ)
    (hne : sigma ≠ z) :
    resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma (1 : ℂ) =
      (sigma - z)⁻¹ := by
  have hsub : (sigma • (1 : ℂ →L[ℂ] ℂ) -
      ContinuousLinearMap.toSpanSingleton ℂ z) =
      ContinuousLinearMap.toSpanSingleton ℂ (sigma - z) := by
    apply ContinuousLinearMap.ext
    intro x
    change sigma * x - x * z = x * (sigma - z)
    ring
  have hunit : IsUnit (sigma • (1 : ℂ →L[ℂ] ℂ) -
      ContinuousLinearMap.toSpanSingleton ℂ z) := by
    rw [hsub]
    let u : (ℂ →L[ℂ] ℂ)ˣ :=
      { val := ContinuousLinearMap.toSpanSingleton ℂ (sigma - z)
        inv := ContinuousLinearMap.toSpanSingleton ℂ (sigma - z)⁻¹
        val_inv := by
          apply ContinuousLinearMap.ext
          intro x
          change (x * (sigma - z)⁻¹) * (sigma - z) = x
          field_simp
        inv_val := by
          apply ContinuousLinearMap.ext
          intro x
          change (x * (sigma - z)) * (sigma - z)⁻¹ = x
          field_simp }
    exact ⟨u, rfl⟩
  have hsigma : sigma ∈ resolventSet ℂ
      (ContinuousLinearMap.toSpanSingleton ℂ z) := by
    rw [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
    exact hunit
  have hmul :
      (sigma • (1 : ℂ →L[ℂ] ℂ) -
          ContinuousLinearMap.toSpanSingleton ℂ z) *
        resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma = 1 := by
    have hunitEq : sigma • (1 : ℂ →L[ℂ] ℂ) -
        ContinuousLinearMap.toSpanSingleton ℂ z =
          (hsigma.unit : ℂ →L[ℂ] ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hsigma.unit_spec.symm
    calc
      (sigma • (1 : ℂ →L[ℂ] ℂ) -
            ContinuousLinearMap.toSpanSingleton ℂ z) *
          resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma =
          (hsigma.unit : ℂ →L[ℂ] ℂ) *
            (↑((hsigma.unit)⁻¹) : ℂ →L[ℂ] ℂ) := by
        rw [hunitEq, spectrum.resolvent_eq hsigma]
      _ = 1 := Units.mul_inv _
  have hx := congrArg (fun T : ℂ →L[ℂ] ℂ ↦ T (1 : ℂ)) hmul
  have hx' : 1 = sigma *
      (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) -
        (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) * z := by
    change sigma *
        (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) -
          (resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1) * z =
      1 at hx
    exact hx.symm
  let y := resolvent (ContinuousLinearMap.toSpanSingleton ℂ z) sigma 1
  have hmul : y * (sigma - z) = 1 := by
    calc
      y * (sigma - z) = sigma * y - y * z := by ring
      _ = 1 := hx'.symm
  calc
    y = y * ((sigma - z) * (sigma - z)⁻¹) := by
      rw [mul_inv_cancel₀ (sub_ne_zero.mpr hne), mul_one]
    _ = (y * (sigma - z)) * (sigma - z)⁻¹ := by ring
    _ = (sigma - z)⁻¹ := by rw [hmul, one_mul]

/-- At any interior point, the scalar Crouzeix companion is the value at `1`
of the polynomial auxiliary operator for one-dimensional multiplication by
that point.  Thus the scalar analytic construction is exactly the
one-dimensional scalarization of the operator contour construction, for an
arbitrary smooth Jordan domain. -/
theorem crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega p z =
      crouzeixPolynomialAuxiliaryOperator
        (ContinuousLinearMap.toSpanSingleton ℂ z) Omega p 1 := by
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ z
  have hAeq : A = z • (1 : ℂ →L[ℂ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro x
    change x * z = z * x
    ring
  have hW : closure (numericalRange A) ⊆ Omega.carrier := by
    have hnr : numericalRange A ⊆ ({z} : Set ℂ) := by
      rintro w ⟨x, hx, rfl⟩
      rw [hAeq]
      simp only [smul_apply, one_apply_eq_self, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hx]
      norm_num
    exact (closure_minimal hnr isClosed_singleton).trans (by
      intro w hw
      simpa only [mem_singleton_iff] using hw ▸ hz)
  have hint := crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
    A Omega p hW
  let L : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  have hLcontour :
      contourIntegral
          (fun sigma ↦ L (star (Polynomial.eval sigma p) • resolvent A sigma))
          Omega.boundaryParam =
        L (contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma p) • resolvent A sigma)
          Omega.boundaryParam) :=
    L.contourIntegral_comp_comm hint
  have hscalarContour :
      contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma p) * (sigma - z)⁻¹)
          Omega.boundaryParam =
        contourIntegral
          (fun sigma ↦ L (star (Polynomial.eval sigma p) • resolvent A sigma))
          Omega.boundaryParam := by
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _ht
    have hne : Omega.boundaryParam t ≠ z := by
      intro heq
      have hzfrontier : z ∈ frontier Omega.carrier := by
        rw [← heq, ← Omega.boundaryParam_range]
        exact mem_range_self t
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← Omega.isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hzfrontier⟩
      exact hempty
    change deriv Omega.boundaryParam t *
        (star (Polynomial.eval (Omega.boundaryParam t) p) *
          (Omega.boundaryParam t - z)⁻¹) =
      deriv Omega.boundaryParam t *
        L (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))
    congr 1
    change star (Polynomial.eval (Omega.boundaryParam t) p) *
        (Omega.boundaryParam t - z)⁻¹ =
      star (Polynomial.eval (Omega.boundaryParam t) p) *
        resolvent A (Omega.boundaryParam t) 1
    rw [resolvent_toSpanSingleton_apply_one_eq_inv z
      (Omega.boundaryParam t) hne]
  calc
    crouzeixPolynomialScalarCompanion Omega p z =
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          contourIntegral
            (fun sigma ↦ star (Polynomial.eval sigma p) * (sigma - z)⁻¹)
            Omega.boundaryParam := rfl
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
        L (contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma p) • resolvent A sigma)
          Omega.boundaryParam) := by rw [hscalarContour, hLcontour]
    _ = (crouzeixPolynomialAuxiliaryOperator A Omega p) 1 := by rfl

private theorem norm_apply_one_eq_norm_complex_endomorphism
    (T : ℂ →L[ℂ] ℂ) : ‖T 1‖ = ‖T‖ := by
  have hT : T = ContinuousLinearMap.toSpanSingleton ℂ (T 1) := by
    apply ContinuousLinearMap.ext
    intro x
    change T x = x * T 1
    calc
      T x = T (x • (1 : ℂ)) := by simp only [smul_eq_mul, mul_one]
      _ = x • T 1 := map_smul T x 1
      _ = x * T 1 := by rfl
  rw [hT, ContinuousLinearMap.norm_toSpanSingleton]
  change ‖(1 : ℂ) * T 1‖ = ‖T 1‖
  rw [one_mul]

/-- Scalarization is isometric: the norm of the scalar companion at an
interior point equals the operator norm of the corresponding one-dimensional
polynomial auxiliary operator.  Hence an auxiliary-operator estimate in the
scalar model transfers to the analytic companion with no loss. -/
theorem norm_crouzeixPolynomialScalarCompanion_eq_norm_auxiliaryOperator
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ =
      ‖crouzeixPolynomialAuxiliaryOperator
        (ContinuousLinearMap.toSpanSingleton ℂ z) Omega p‖ := by
  rw [crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
    Omega p hz]
  exact norm_apply_one_eq_norm_complex_endomorphism _

/-- At every point away from the smooth Jordan frontier, the scalar companion
has the expected inverse-square Cauchy-kernel derivative.  This simultaneously
constructs its interior and exterior holomorphic branches. -/
theorem hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    HasDerivAt (crouzeixPolynomialScalarCompanion Omega p)
      (crouzeixPolynomialScalarCompanionDeriv Omega p z) z := by
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp isClosed_frontier.isOpen_compl z hz
  let c : ℝ → ℂ := fun t ↦
    deriv Omega.boundaryParam t *
      star (Polynomial.eval (Omega.boundaryParam t) p)
  let F : ℂ → ℝ → ℂ := fun w t ↦
    c t * (Omega.boundaryParam t - w)⁻¹
  let F' : ℂ → ℝ → ℂ := fun w t ↦
    c t * (Omega.boundaryParam t - w)⁻¹ ^ 2
  have hsep : ∀ t, δ ≤ ‖Omega.boundaryParam t - z‖ := by
    intro t
    rw [← dist_eq_norm]
    apply le_of_not_gt
    intro hlt
    have hcompl := hball (by
      simpa only [Metric.mem_ball, dist_comm] using hlt)
    apply hcompl
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hsep_local : ∀ t, ∀ w ∈ Metric.ball z (δ / 2),
      δ / 2 ≤ ‖Omega.boundaryParam t - w‖ := by
    intro t w hw
    have hwz : ‖w - z‖ < δ / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have htri : ‖Omega.boundaryParam t - z‖ ≤
        ‖Omega.boundaryParam t - w‖ + ‖w - z‖ := by
      calc
        ‖Omega.boundaryParam t - z‖ =
            ‖(Omega.boundaryParam t - w) + (w - z)‖ := by ring_nf
        _ ≤ ‖Omega.boundaryParam t - w‖ + ‖w - z‖ := norm_add_le _ _
    linarith [hsep t]
  have hderiv : ∀ t, ∀ w ∈ Metric.ball z (δ / 2),
      HasDerivAt (fun x ↦ F x t) (F' w t) w := by
    intro t w hw
    have hne : Omega.boundaryParam t - w ≠ 0 := by
      intro heq
      have hzero : ‖Omega.boundaryParam t - w‖ = 0 := by rw [heq, norm_zero]
      linarith [hsep_local t w hw]
    have hsub : HasDerivAt (fun x : ℂ ↦ Omega.boundaryParam t - x) (-1) w := by
      have hfun : (fun x : ℂ ↦ Omega.boundaryParam t - x) =
          (fun _ : ℂ ↦ Omega.boundaryParam t) - id := by
        funext x
        rfl
      rw [hfun]
      simpa only [zero_sub] using
        (hasDerivAt_const w (Omega.boundaryParam t)).sub (hasDerivAt_id w)
    have hinv := hsub.inv hne
    have hmul := (hasDerivAt_const w (c t)).mul hinv
    have hfun : (fun x : ℂ ↦ c t * (Omega.boundaryParam t - x)⁻¹) =
        (fun _ : ℂ ↦ c t) * (fun x ↦ Omega.boundaryParam t - x)⁻¹ := by
      funext x
      rfl
    change HasDerivAt (fun x ↦ c t * (Omega.boundaryParam t - x)⁻¹)
      (c t * (Omega.boundaryParam t - w)⁻¹ ^ 2) w
    rw [hfun]
    simpa only [Pi.mul_apply, zero_mul, zero_add, neg_neg, one_div, inv_pow] using hmul
  have hccont : Continuous c := by
    apply Continuous.mul
    · exact Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)
    · exact (p.continuous.comp
        Omega.boundaryParam_contDiff.continuous).star
  have hFcont : ∀ w ∈ Metric.ball z (δ / 2),
      ContinuousOn (F w) [[(0 : ℝ), 2 * Real.pi]] := by
    intro w hw
    have hden : ContinuousOn (fun t ↦ Omega.boundaryParam t - w)
        [[(0 : ℝ), 2 * Real.pi]] :=
      Omega.boundaryParam_contDiff.continuous.continuousOn.sub
        continuous_const.continuousOn
    have hne : ∀ t ∈ [[(0 : ℝ), 2 * Real.pi]],
        Omega.boundaryParam t - w ≠ 0 := by
      intro t ht heq
      have hzero : ‖Omega.boundaryParam t - w‖ = 0 := by rw [heq, norm_zero]
      linarith [hsep_local t w hw]
    have hfun : F w = c * (fun t ↦ Omega.boundaryParam t - w)⁻¹ := by
      funext t
      rfl
    rw [hfun]
    exact hccont.continuousOn.mul (hden.inv₀ hne)
  have hF'cont : ∀ w ∈ Metric.ball z (δ / 2),
      ContinuousOn (F' w) [[(0 : ℝ), 2 * Real.pi]] := by
    intro w hw
    have hden : ContinuousOn (fun t ↦ Omega.boundaryParam t - w)
        [[(0 : ℝ), 2 * Real.pi]] :=
      Omega.boundaryParam_contDiff.continuous.continuousOn.sub
        continuous_const.continuousOn
    have hne : ∀ t ∈ [[(0 : ℝ), 2 * Real.pi]],
        Omega.boundaryParam t - w ≠ 0 := by
      intro t ht heq
      have hzero : ‖Omega.boundaryParam t - w‖ = 0 := by rw [heq, norm_zero]
      linarith [hsep_local t w hw]
    have hfun : F' w = c * (fun t ↦ Omega.boundaryParam t - w)⁻¹ ^ 2 := by
      funext t
      rfl
    rw [hfun]
    exact hccont.continuousOn.mul ((hden.inv₀ hne).pow 2)
  let bound : ℝ → ℝ := fun t ↦ ‖c t‖ * (δ / 2)⁻¹ ^ 2
  have hboundInt : IntervalIntegrable bound volume (0 : ℝ) (2 * Real.pi) :=
    (hccont.norm.mul continuous_const).intervalIntegrable _ _
  have hFmeas : ∀ᶠ w in nhds z,
      AEStronglyMeasurable (F w)
        (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [Metric.ball_mem_nhds z (half_pos hδ)] with w hw
    exact ((hFcont w hw).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  have hFint : IntervalIntegrable (F z) volume (0 : ℝ) (2 * Real.pi) :=
    (hFcont z (Metric.mem_ball_self (half_pos hδ))).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) :=
    ((hF'cont z (Metric.mem_ball_self (half_pos hδ))).mono
      uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ Metric.ball z (δ / 2), ‖F' w t‖ ≤ bound t := by
    filter_upwards with t
    intro ht w hw
    have hdenpos : 0 < ‖Omega.boundaryParam t - w‖ :=
      (half_pos hδ).trans_le (hsep_local t w hw)
    have hinv : ‖Omega.boundaryParam t - w‖⁻¹ ≤ (δ / 2)⁻¹ :=
      (inv_le_inv₀ hdenpos (half_pos hδ)).2 (hsep_local t w hw)
    dsimp only [F', bound]
    rw [norm_mul, norm_pow, norm_inv]
    gcongr
  have hdiff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ Metric.ball z (δ / 2),
        HasDerivAt (fun x ↦ F x t) (F' w t) w := by
    filter_upwards with t
    intro ht w hw
    exact hderiv t w hw
  have hint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z (half_pos hδ)) hFmeas hFint hF'meas hbound hboundInt hdiff
  have hscaled :=
    (hasDerivAt_const z ((2 * (Real.pi : ℂ) * I)⁻¹)).mul hint.2
  have hcompanion : crouzeixPolynomialScalarCompanion Omega p = fun w ↦
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), F w t := by
    funext w
    unfold crouzeixPolynomialScalarCompanion contourIntegral
    simp only [F, c, smul_eq_mul, mul_assoc]
  rw [hcompanion]
  have hpoint : (fun _ : ℂ ↦ (2 * (Real.pi : ℂ) * I)⁻¹) *
      (fun w ↦ ∫ t in (0 : ℝ)..(2 * Real.pi), F w t) =
      (fun w ↦ (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), F w t) := by
    funext w
    rfl
  rw [← hpoint]
  simpa only [crouzeixPolynomialScalarCompanionDeriv, F', c, zero_mul,
    zero_add, mul_assoc] using hscaled

/-- At every point in the smooth Jordan carrier, the scalar companion has the
expected inverse-square Cauchy-kernel derivative. -/
theorem hasDerivAt_crouzeixPolynomialScalarCompanion
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    HasDerivAt (crouzeixPolynomialScalarCompanion Omega p)
      (crouzeixPolynomialScalarCompanionDeriv Omega p z) z := by
  apply hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
  intro hfrontier
  have hempty : z ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hz, hfrontier⟩
  exact hempty

/-- The scalar companion is holomorphic on the complement of the smooth
Jordan frontier, giving both its interior and exterior branches. -/
theorem analyticOn_crouzeixPolynomialScalarCompanion_frontier_compl
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    AnalyticOn ℂ (crouzeixPolynomialScalarCompanion Omega p)
      (frontier Omega.carrier)ᶜ := by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact
      (hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
        Omega p hz).differentiableAt.differentiableWithinAt
  · exact isClosed_frontier.isOpen_compl

/-- The scalar Crouzeix--Palencia companion is holomorphic throughout the
smooth Jordan carrier. -/
theorem analyticOn_crouzeixPolynomialScalarCompanion
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    AnalyticOn ℂ (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier := by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact (hasDerivAt_crouzeixPolynomialScalarCompanion Omega p
      hz).differentiableAt.differentiableWithinAt
  · exact Omega.isOpen_carrier

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
