/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# General smooth-domain symmetrized auxiliary bound

This file assembles the sharp L4.2d estimate on a smooth boundary once the
three genuinely analytic/geometric inputs are available:

* the polynomial and resolvent Cauchy identities for the parametrized curve;
* the outward tangent-normal direction supports the numerical range; and
* the polynomial boundary values are uniformly bounded by `M`.

The proof derives all remaining facts from the landed infrastructure.  The
resolvent and polynomial kernels are interval integrable, the supporting
half-plane condition makes the double-layer kernel positive, and the
resolvent Cauchy identity gives total mass `4 * pi • 1`.  Positive-kernel
contractivity then gives the factor `2`.

The hypotheses are intentionally explicit: `SmoothJordanDomain` does not
currently record an orientation/support condition, and no general-domain
Cauchy or Plemelj theorem is hidden here.

## Main declaration

* `SmoothJordanDomain.isCompact_frontier` -- the parametrized frontier is
  compact;
* `norm_eval_boundaryParam_le_polynomialSupNorm_frontier` -- boundary values
  are controlled by the polynomial sup norm on the frontier;
* `exists_global_polynomial_calculus_bound_frontier_of_cauchy` -- an
  all-polynomial Cauchy representation supplies a finite global calculus
  constant on the fixed smooth domain;
* `norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support`
  -- the generic smooth-domain L4.2d bound from Cauchy and support data.
* `norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_frontier_of_cauchy_support`
  -- the same estimate with the canonical frontier sup norm.
* `norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support`
  -- control by any compact set containing the frontier.
* `isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support`
  -- the Hermitian product remainder is an integrated positive variance.
* `re_inner_aeval_crouzeixProductRemainderPolynomial_nonneg_of_cauchy_support`
  -- the corresponding accretive quadratic-form statement.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ApproximationSupNorm
import LeanPool.OperatorTheory.Operator.Crouzeix.DoubleLayer
import LeanPool.OperatorTheory.Operator.Crouzeix.DoubleLayerIntegral
import LeanPool.OperatorTheory.Operator.Crouzeix.PositiveIntegral
import LeanPool.OperatorTheory.Operator.Crouzeix.ProductContour
import LeanPool.OperatorTheory.Operator.Crouzeix.SymmetrizedAuxiliary
import LeanPool.OperatorTheory.Operator.Crouzeix.SymmetrizedBound

open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

namespace SmoothJordanDomain

/-- The frontier of a smooth Jordan domain is compact: it is the range of a
continuous function with nonzero period. -/
theorem isCompact_frontier (Omega : SmoothJordanDomain) :
    IsCompact (frontier Omega.carrier) := by
  rw [← Omega.boundaryParam_range]
  exact Omega.boundaryParam_periodic.compact_of_continuous
    (by positivity) Omega.boundaryParam_contDiff.continuous

end SmoothJordanDomain

/-- Every value of a polynomial on the parametrized boundary is bounded by
its polynomial sup norm on the domain frontier. -/
theorem norm_eval_boundaryParam_le_polynomialSupNorm_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (t : ℝ) :
    ‖Polynomial.eval (Omega.boundaryParam t) p‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  apply norm_eval_le_polynomialSupNorm p
  · exact bddAbove_norm_eval_image_of_isCompact p Omega.isCompact_frontier
  · rw [← Omega.boundaryParam_range]
    exact mem_range_self t

/-- An all-polynomial Cauchy representation on a fixed smooth domain gives a
finite global polynomial-calculus constant relative to the frontier sup norm.
The constant is obtained from the compact parameter-interval bound on the
unweighted resolvent kernel, extracted by applying the existing auxiliary
integrand bound to the constant polynomial `1`. -/
theorem exists_global_polynomial_calculus_bound_frontier_of_cauchy
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : ∀ p : Polynomial ℂ, Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z ↦ Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (frontier Omega.carrier) := by
  obtain ⟨C, hC⟩ :=
    exists_bound_crouzeixPolynomialAuxiliaryIntegrand A Omega (Polynomial.C 1) hOmega
  have hkernel : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        resolvent A (Omega.boundaryParam t)‖ ≤ C := by
    intro t ht
    simpa only [Polynomial.eval_C, star_one, one_smul] using hC t ht
  have hC0 : 0 ≤ C :=
    (norm_nonneg (deriv Omega.boundaryParam 0 •
      resolvent A (Omega.boundaryParam 0))).trans
      (hkernel 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let K : ℝ := ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)
  refine ⟨K, mul_nonneg (norm_nonneg _) (mul_nonneg Real.two_pi_pos.le hC0), ?_⟩
  intro p
  have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (Polynomial.eval (Omega.boundaryParam t) p •
          resolvent A (Omega.boundaryParam t))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier) * C := by
    intro t ht
    rw [smul_smul, norm_smul, norm_mul]
    calc
      ‖deriv Omega.boundaryParam t‖ *
          ‖Polynomial.eval (Omega.boundaryParam t) p‖ *
            ‖resolvent A (Omega.boundaryParam t)‖ =
          ‖Polynomial.eval (Omega.boundaryParam t) p‖ *
            ‖deriv Omega.boundaryParam t •
              resolvent A (Omega.boundaryParam t)‖ := by
        rw [norm_smul]
        ring
      _ ≤ polynomialSupNorm p (frontier Omega.carrier) * C :=
        mul_le_mul (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega p t)
          (hkernel t ht) (norm_nonneg _) (polynomialSupNorm_nonneg p _)
  rw [hCauchy p, norm_smul]
  calc
    ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        ‖contourIntegral (fun z ↦ Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi * (polynomialSupNorm p (frontier Omega.carrier) * C)) :=
      mul_le_mul_of_nonneg_left
        (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)
    _ = K * polynomialSupNorm p (frontier Omega.carrier) := by
      simp only [K]
      ring

private theorem intervalIntegrable_deriv_smul_resolvent
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    IntervalIntegrable
      (fun t => deriv Omega.boundaryParam t •
        resolvent A (Omega.boundaryParam t))
      volume 0 (2 * Real.pi) := by
  have hcontour :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
      (fun _ => 1) hOmega continuous_const.continuousOn
  change IntervalIntegrable
    (fun t => deriv Omega.boundaryParam t •
      (1 • resolvent A (Omega.boundaryParam t)))
    volume 0 (2 * Real.pi) at hcontour
  simpa only [one_smul] using hcontour

private theorem intervalIntegrable_boundaryDatum_smul_outwardKernel
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (h : ℂ → ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hh : ContinuousOn h
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi))) :
    IntervalIntegrable
      (fun t => h (Omega.boundaryParam t) •
        ((-I * deriv Omega.boundaryParam t) •
          resolvent A (Omega.boundaryParam t)))
      volume 0 (2 * Real.pi) := by
  have hcontour :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega h hOmega hh
  change IntervalIntegrable
    (fun t => deriv Omega.boundaryParam t •
      (h (Omega.boundaryParam t) •
        resolvent A (Omega.boundaryParam t)))
    volume 0 (2 * Real.pi) at hcontour
  have hfun :
      (fun t => h (Omega.boundaryParam t) •
        ((-I * deriv Omega.boundaryParam t) •
          resolvent A (Omega.boundaryParam t))) =
      fun t => (-I) •
        (deriv Omega.boundaryParam t •
          (h (Omega.boundaryParam t) •
            resolvent A (Omega.boundaryParam t))) := by
    funext t
    simp only [smul_smul]
    congr 1
    ring
  rw [hfun]
  exact ⟨hcontour.1.smul_enorm (-I), hcontour.2.smul_enorm (-I)⟩

private theorem intervalIntegrable_adjoint
    {g : ℝ → E →L[ℂ] E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => ContinuousLinearMap.adjoint (g t))
      volume a b := by
  let adjointCLM : (E →L[ℂ] E) →L⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  change IntervalIntegrable (fun t => adjointCLM (g t)) volume a b
  exact ⟨adjointCLM.integrable_comp hg.1, adjointCLM.integrable_comp hg.2⟩

private theorem intervalIntegrable_smul_add_adjoint
    (B : ℝ → E →L[ℂ] E) (f : ℝ → ℂ) {a b : ℝ}
    (hfB : IntervalIntegrable (fun t => f t • B t) volume a b)
    (hstarfB : IntervalIntegrable (fun t => star (f t) • B t) volume a b) :
    IntervalIntegrable
      (fun t => f t • (B t + ContinuousLinearMap.adjoint (B t)))
      volume a b := by
  have hAdjoint : IntervalIntegrable
      (fun t => ContinuousLinearMap.adjoint (star (f t) • B t))
      volume a b := intervalIntegrable_adjoint hstarfB
  have hfun :
      (fun t => ContinuousLinearMap.adjoint (star (f t) • B t)) =
        fun t => f t • ContinuousLinearMap.adjoint (B t) := by
    funext t
    exact
      (map_smulₛₗ ContinuousLinearMap.adjoint (star (f t)) (B t)).trans (by
        rw [starRingEnd_apply, star_star])
  rw [hfun] at hAdjoint
  simpa only [smul_add] using hfB.add hAdjoint

/-- **Generic smooth-domain L4.2d bound.**  If the parametrized boundary
satisfies the polynomial and resolvent Cauchy identities, its induced outward
normal supports the numerical range pointwise, and `‖p‖ ≤ M` on the boundary,
then the polynomial auxiliary operator satisfies the sharp symmetrized bound
`‖p(A) + G†‖ ≤ 2 * M`. -/
theorem
    norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {M : ℝ}
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (hM : 0 ≤ M)
    (hp : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ‖Polynomial.eval (Omega.boundaryParam t) p‖ ≤ M) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤ 2 * M := by
  let gamma := Omega.boundaryParam
  let f : ℝ → ℂ := fun t => Polynomial.eval (gamma t) p
  let B : ℝ → E →L[ℂ] E := fun t =>
    (-I * deriv gamma t) • resolvent A (gamma t)
  let K : ℝ → E →L[ℂ] E := fun t =>
    B t + ContinuousLinearMap.adjoint (B t)
  have hbase : IntervalIntegrable
      (fun t => deriv gamma t • resolvent A (gamma t))
      volume 0 (2 * Real.pi) := by
    simpa only [gamma] using
      intervalIntegrable_deriv_smul_resolvent A Omega hOmega
  have hB : IntervalIntegrable B volume 0 (2 * Real.pi) := by
    simpa only [B, gamma, one_smul] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun _ => 1) hOmega continuous_const.continuousOn
  have hK : IntervalIntegrable K volume 0 (2 * Real.pi) := by
    change IntervalIntegrable
      (fun t => B t + ContinuousLinearMap.adjoint (B t))
      volume 0 (2 * Real.pi)
    exact hB.add (intervalIntegrable_adjoint hB)
  have hfB : IntervalIntegrable (fun t => f t • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun z => Polynomial.eval z p) hOmega
          p.continuous.continuousOn
  have hstarfB : IntervalIntegrable (fun t => star (f t) • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun z => star (Polynomial.eval z p)) hOmega
          p.continuous.star.continuousOn
  have hfK : IntervalIntegrable (fun t => f t • K t)
      volume 0 (2 * Real.pi) := by
    change IntervalIntegrable
      (fun t => f t • (B t + ContinuousLinearMap.adjoint (B t)))
      volume 0 (2 * Real.pi)
    exact intervalIntegrable_smul_add_adjoint B f hfB hstarfB
  have hrepresentation :
      Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p) =
        (2 * Real.pi)⁻¹ •
          (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) := by
    simpa only [gamma, f, B, K] using
      (aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
        A Omega p hOmega hCauchyP)
  have hpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t := by
    intro t ht
    change 0 ≤ ((-I * deriv gamma t) • resolvent A (gamma t) +
      ContinuousLinearMap.adjoint
        ((-I * deriv gamma t) • resolvent A (gamma t)))
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    apply isPositive_add_adjoint_smul_resolvent A
    simpa only [gamma] using hsupport t ht
  have hCauchyOne' :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv gamma t • resolvent A (gamma t)) =
          (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    simpa only [gamma] using hCauchyOne
  have hnorm : (∫ t in (0 : ℝ)..(2 * Real.pi), K t) =
      (4 * Real.pi) • (1 : E →L[ℂ] E) := by
    simpa only [K, B] using
      (intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
        A gamma hbase hCauchyOne')
  have hp' : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M := by
    simpa only [f, gamma] using hp
  exact norm_add_star_le_two_mul_of_doubleLayer_representation
    (Polynomial.aeval A p) (crouzeixPolynomialAuxiliaryOperator A Omega p)
      hrepresentation hK hfK hpos hnorm hM hp'

/-- The scalar-square auxiliary operator has nonnegative quadratic real
part whenever the outward normal of the contour supports the numerical
range.  This is the signed half of double-layer positivity needed by the
product-remainder identity; it requires no triangle inequality and no
Cauchy mass normalization. -/
theorem re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    0 ≤ RCLike.re ⟪x,
      crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) x⟫_ℂ := by
  let gamma := Omega.boundaryParam
  let f : ℝ → ℂ := fun t =>
    star (Polynomial.eval (gamma t) p) * Polynomial.eval (gamma t) p
  let B : ℝ → E →L[ℂ] E := fun t =>
    (-I * deriv gamma t) • resolvent A (gamma t)
  let K : ℝ → E →L[ℂ] E := fun t =>
    B t + ContinuousLinearMap.adjoint (B t)
  have hfB : IntervalIntegrable (fun t => f t • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) hOmega
        (p.continuous.star.mul p.continuous).continuousOn
  have hstarf : (fun t => star (f t) • B t) = fun t => f t • B t := by
    funext t
    simp only [f, star_mul, star_star]
  have hstarfB : IntervalIntegrable (fun t => star (f t) • B t)
      volume 0 (2 * Real.pi) := by
    rw [hstarf]
    exact hfB
  have hfK : IntervalIntegrable (fun t => f t • K t)
      volume 0 (2 * Real.pi) := by
    change IntervalIntegrable
      (fun t => f t • (B t + ContinuousLinearMap.adjoint (B t)))
      volume 0 (2 * Real.pi)
    exact intervalIntegrable_smul_add_adjoint B f hfB hstarfB
  have hKpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t := by
    intro t ht
    change 0 ≤ ((-I * deriv gamma t) • resolvent A (gamma t) +
      ContinuousLinearMap.adjoint
        ((-I * deriv gamma t) • resolvent A (gamma t)))
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    apply isPositive_add_adjoint_smul_resolvent A
    simpa only [gamma] using hsupport t ht
  have hfKpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      0 ≤ f t • K t := by
    intro t ht
    rw [show f t = ((‖Polynomial.eval (gamma t) p‖ ^ 2 : ℝ) : ℂ) by
      simp only [f]
      change (starRingEnd ℂ) (Polynomial.eval (gamma t) p) *
        Polynomial.eval (gamma t) p = _
      rw [Complex.conj_mul']
      norm_cast]
    change 0 ≤ (‖Polynomial.eval (gamma t) p‖ ^ 2 : ℝ) • K t
    exact smul_nonneg (sq_nonneg _) (hKpos t ht)
  have hIntegralPos : ContinuousLinearMap.IsPositive
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) := by
    apply ContinuousLinearMap.isPositive_intervalIntegral
      (f := fun t => f t • K t) Real.two_pi_pos.le hfK
    exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
      rw [← ContinuousLinearMap.nonneg_iff_isPositive]
      exact hfKpos t ht
  have hsymmIntegral :
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) +
          ContinuousLinearMap.adjoint
            (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) =
        ∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t := by
    have h := ContinuousLinearMap.intervalIntegral_smul_add_adjoint
      B f hfB hstarfB
    rw [hstarf] at h
    simpa only [K] using h
  have hcoeff : ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ := by
    symm
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ = I⁻¹ * (2 * (Real.pi : ℂ))⁻¹ :=
        mul_inv_rev _ _
      _ = (-I) * (2 * (Real.pi : ℂ))⁻¹ := by rw [inv_I]
      _ = (-I) * ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) := by
        rw [Complex.ofReal_inv]
        push_cast
        rfl
      _ = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-I)) := mul_comm _ _
  have haux : crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
        (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) := by
    unfold crouzeixAuxiliaryOperator contourIntegral
    have hfun :
        (fun t => f t • B t) = fun t =>
          (-I) • (deriv gamma t •
            ((star (Polynomial.eval (gamma t) p) *
              Polynomial.eval (gamma t) p) • resolvent A (gamma t))) := by
      funext t
      simp only [f, B, smul_smul]
      congr 1
      ring
    rw [hfun, intervalIntegral.integral_smul, smul_smul, hcoeff]
  have hsymm :
      crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) +
        star (crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)) =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
        (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) := by
    rw [haux]
    change
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t)) +
        ContinuousLinearMap.adjoint
          ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
            (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t)) = _
    rw [map_smulₛₗ, Complex.conj_ofReal, ← smul_add, hsymmIntegral]
  have hIntegralRe : 0 ≤ RCLike.re ⟪x,
      (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) x⟫_ℂ :=
    hIntegralPos.re_inner_nonneg_right x
  have hsymmRe : 0 ≤ RCLike.re ⟪x,
      (crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) +
        star (crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p))) x⟫_ℂ := by
    rw [hsymm, smul_apply, inner_smul_right]
    change 0 ≤
      (((((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ⟪x, (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t) x⟫_ℂ).re)
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le) hIntegralRe
  have hadjointRe : RCLike.re ⟪x,
      star (crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)) x⟫_ℂ =
      RCLike.re ⟪x,
        crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) x⟫_ℂ := by
    change RCLike.re ⟪x,
      ContinuousLinearMap.adjoint (crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)) x⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact inner_re_symm _ _
  rw [add_apply, inner_add_right, map_add, hadjointRe] at hsymmRe
  linarith

/-- In the exact product decomposition, double-layer positivity retains the
sign of the cancellation: the real part of `p(A) G_p` is bounded below by
minus the real part of the evaluated lower-degree remainder. -/
theorem neg_re_inner_aeval_crouzeixProductRemainderPolynomial_le_re_inner_product
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    -RCLike.re ⟪x,
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) x⟫_ℂ ≤
      RCLike.re ⟪x, (Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ := by
  have hsquare := re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
    A Omega p hOmega hsupport x
  have hidentity :=
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
      A Omega p hOmega
  rw [hidentity, sub_apply, inner_sub_right, map_sub]
  linarith

/-- The Hermitian part of the product remainder is positive.  More
precisely, it is the normalized integral of the positive operator-valued
variance `(p(z) - p(A))† K(z) (p(z) - p(A))`, where `K` is the
double-layer kernel.  This identity retains the coupling between the square
auxiliary and the product term; it does not estimate either separately. -/
theorem
    isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0) :
    ContinuousLinearMap.IsPositive
      (Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) +
        star (Polynomial.aeval A
          (crouzeixProductRemainderPolynomial Omega p))) := by
  let gamma := Omega.boundaryParam
  let f : ℝ → ℂ := fun t => Polynomial.eval (gamma t) p
  let B : ℝ → E →L[ℂ] E := fun t =>
    (-I * deriv gamma t) • resolvent A (gamma t)
  let K : ℝ → E →L[ℂ] E := fun t =>
    B t + ContinuousLinearMap.adjoint (B t)
  let F : E →L[ℂ] E := Polynomial.aeval A p
  let D : ℝ → E →L[ℂ] E := fun t => f t • 1 - F
  let Q : ℝ → E →L[ℂ] E := fun t => star (D t) * B t * D t
  have hB : IntervalIntegrable B volume 0 (2 * Real.pi) := by
    simpa only [B, gamma, one_smul] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel
        A Omega (fun _ => 1) hOmega continuous_const.continuousOn
  have hD : Continuous D := by
    have hgamma : Continuous gamma := by
      simpa only [gamma] using Omega.boundaryParam_contDiff.continuous
    change Continuous (fun t => f t • (1 : E →L[ℂ] E) - F)
    have hf : Continuous f := p.continuous.comp hgamma
    fun_prop
  have hQ : IntervalIntegrable Q volume 0 (2 * Real.pi) := by
    have hBD : IntervalIntegrable (fun t => B t * D t)
        volume 0 (2 * Real.pi) := hB.mul_continuousOn hD.continuousOn
    have hstarD : Continuous (fun t => star (D t)) := by
      fun_prop
    simpa only [Q, mul_assoc] using
      hBD.continuousOn_mul hstarD.continuousOn
  have hKpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ContinuousLinearMap.IsPositive (K t) := by
    intro t ht
    change ContinuousLinearMap.IsPositive
      ((-I * deriv gamma t) • resolvent A (gamma t) +
        ContinuousLinearMap.adjoint
          ((-I * deriv gamma t) • resolvent A (gamma t)))
    apply isPositive_add_adjoint_smul_resolvent A
    simpa only [gamma] using hsupport t ht
  have hQadd : (fun t => Q t + star (Q t)) =
      fun t => star (D t) * K t * D t := by
    funext t
    simp only [Q, K, star_mul, star_star, mul_add, add_mul, mul_assoc]
    rw [show star (B t) = ContinuousLinearMap.adjoint (B t) by rfl]
  have hQpos : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ContinuousLinearMap.IsPositive (Q t + star (Q t)) := by
    intro t ht
    rw [congrFun hQadd t]
    exact (hKpos t ht).adjoint_conj (D t)
  have hQsymm : ContinuousLinearMap.IsPositive
      (∫ t in (0 : ℝ)..(2 * Real.pi), Q t + star (Q t)) := by
    apply ContinuousLinearMap.isPositive_intervalIntegral
      (f := fun t => Q t + star (Q t)) Real.two_pi_pos.le
      (hQ.add (intervalIntegrable_adjoint hQ))
    exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => hQpos t ht
  have hQexpand : Q = fun t =>
      (star (f t) * f t) • B t -
        (star (f t) • B t) * F -
        star F * (f t • B t) +
        star F * B t * F := by
    funext t
    simp only [Q, D, star_sub, star_smul, star_one, sub_mul, mul_sub,
      one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc,
      smul_sub, smul_smul]
    rw [mul_comm (f t) (star (f t))]
    module
  let c : ℂ := (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  have hcoeff : c * (-I) = (2 * (Real.pi : ℂ) * I)⁻¹ := by
    dsimp only [c]
    symm
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ = I⁻¹ * (2 * (Real.pi : ℂ))⁻¹ :=
        mul_inv_rev _ _
      _ = (-I) * (2 * (Real.pi : ℂ))⁻¹ := by rw [inv_I]
      _ = (-I) * ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) := by
        rw [Complex.ofReal_inv]
        push_cast
        rfl
      _ = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-I)) := mul_comm _ _
  have hnormalized (h : ℂ → ℂ) :
      crouzeixAuxiliaryOperator A Omega h =
        c • (∫ t in (0 : ℝ)..(2 * Real.pi),
          h (gamma t) • B t) := by
    unfold crouzeixAuxiliaryOperator contourIntegral
    have hfun :
        (fun t => h (gamma t) • B t) = fun t =>
          (-I) • (deriv gamma t •
            (h (gamma t) • resolvent A (gamma t))) := by
      funext t
      simp only [B, smul_smul]
      congr 1
      ring
    rw [hfun, intervalIntegral.integral_smul, smul_smul, hcoeff]
  have habsB : IntervalIntegrable
      (fun t => (star (f t) * f t) • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) hOmega
        (p.continuous.star.mul p.continuous).continuousOn
  have hstarfB : IntervalIntegrable (fun t => star (f t) • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => star (Polynomial.eval z p)) hOmega
        p.continuous.star.continuousOn
  have hfB : IntervalIntegrable (fun t => f t • B t)
      volume 0 (2 * Real.pi) := by
    simpa only [f, B, gamma] using
      intervalIntegrable_boundaryDatum_smul_outwardKernel A Omega
        (fun z => Polynomial.eval z p) hOmega p.continuous.continuousOn
  have hAbs : c • (∫ t in (0 : ℝ)..(2 * Real.pi),
        (star (f t) * f t) • B t) =
      crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) := by
    simpa only [f, gamma] using
      (hnormalized
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)).symm
  have hStar : c • (∫ t in (0 : ℝ)..(2 * Real.pi),
        star (f t) • B t) =
      crouzeixPolynomialAuxiliaryOperator A Omega p := by
    simpa only [crouzeixPolynomialAuxiliaryOperator, f, gamma] using
      (hnormalized (fun z => star (Polynomial.eval z p))).symm
  have hP : c • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) = F := by
    rw [← hnormalized (fun z => Polynomial.eval z p)]
    unfold crouzeixAuxiliaryOperator
    simpa only [F] using hCauchyP.symm
  have hOne : c • (∫ t in (0 : ℝ)..(2 * Real.pi), B t) =
      (1 : E →L[ℂ] E) := by
    have hBfun : B = fun t =>
        (-I) • (deriv gamma t • resolvent A (gamma t)) := by
      funext t
      simp only [B, smul_smul]
    rw [hBfun, intervalIntegral.integral_smul]
    have hCauchyOne' :
        (∫ t in (0 : ℝ)..(2 * Real.pi),
          deriv gamma t • resolvent A (gamma t)) =
            (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
      simpa only [gamma] using hCauchyOne
    rw [hCauchyOne']
    simp only [smul_smul]
    rw [← mul_assoc, hcoeff, inv_mul_cancel₀]
    · exact one_smul ℂ (1 : E →L[ℂ] E)
    · exact mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hstarBF : IntervalIntegrable
      (fun t => (star (f t) • B t) * F) volume 0 (2 * Real.pi) :=
    hstarfB.mul_continuousOn continuous_const.continuousOn
  have hFstarfB : IntervalIntegrable
      (fun t => star F * (f t • B t)) volume 0 (2 * Real.pi) :=
    hfB.continuousOn_mul continuous_const.continuousOn
  have hFBF : IntervalIntegrable
      (fun t => star F * B t * F) volume 0 (2 * Real.pi) := by
    exact (hB.continuousOn_mul continuous_const.continuousOn).mul_continuousOn
      continuous_const.continuousOn
  have hintegral_mul_const (u : ℝ → E →L[ℂ] E) (C : E →L[ℂ] E)
      (hu : IntervalIntegrable u volume 0 (2 * Real.pi)) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), u t * C) =
        (∫ t in (0 : ℝ)..(2 * Real.pi), u t) * C := by
    let L := (ContinuousLinearMap.mul ℝ (E →L[ℂ] E)).flip C
    change (∫ t in (0 : ℝ)..(2 * Real.pi), L (u t)) =
      L (∫ t in (0 : ℝ)..(2 * Real.pi), u t)
    exact L.intervalIntegral_comp_comm hu
  have hintegral_const_mul (C : E →L[ℂ] E) (u : ℝ → E →L[ℂ] E)
      (hu : IntervalIntegrable u volume 0 (2 * Real.pi)) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), C * u t) =
        C * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
    let L := ContinuousLinearMap.mul ℝ (E →L[ℂ] E) C
    change (∫ t in (0 : ℝ)..(2 * Real.pi), L (u t)) =
      L (∫ t in (0 : ℝ)..(2 * Real.pi), u t)
    exact L.intervalIntegral_comp_comm hu
  have hIntegralQ :
      (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
        (∫ t in (0 : ℝ)..(2 * Real.pi),
            (star (f t) * f t) • B t) -
          (∫ t in (0 : ℝ)..(2 * Real.pi), star (f t) • B t) * F -
          star F * (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t) +
          star F * (∫ t in (0 : ℝ)..(2 * Real.pi), B t) * F := by
    rw [hQexpand]
    rw [intervalIntegral.integral_add
      ((habsB.sub hstarBF).sub hFstarfB) hFBF]
    rw [intervalIntegral.integral_sub (habsB.sub hstarBF) hFstarfB]
    rw [intervalIntegral.integral_sub habsB hstarBF]
    rw [hintegral_mul_const (fun t => star (f t) • B t) F hstarfB]
    rw [hintegral_const_mul (star F) (fun t => f t • B t) hfB]
    rw [hintegral_mul_const (fun t => star F * B t) F
      (hB.continuousOn_mul continuous_const.continuousOn)]
    rw [hintegral_const_mul (star F) B hB]
  have hStarF : c •
        ((∫ t in (0 : ℝ)..(2 * Real.pi), star (f t) • B t) * F) =
      crouzeixPolynomialAuxiliaryOperator A Omega p * F := by
    rw [← smul_mul_assoc, hStar]
  have hFP : c •
        (star F * (∫ t in (0 : ℝ)..(2 * Real.pi), f t • B t)) =
      star F * F := by
    rw [← mul_smul_comm, hP]
  have hFOneF : c •
        ((star F * (∫ t in (0 : ℝ)..(2 * Real.pi), B t)) * F) =
      star F * F := by
    rw [← smul_mul_assoc, ← mul_smul_comm, hOne, mul_one]
  have hQnorm : c • (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
      Polynomial.aeval A
        (crouzeixProductRemainderPolynomial Omega p) := by
    rw [hIntegralQ]
    simp only [smul_add, smul_sub]
    rw [hAbs, hStarF, hFP, hFOneF]
    have hcomm :=
      commute_aeval_crouzeixPolynomialAuxiliaryOperator A Omega p p hOmega
    rw [← hcomm.eq]
    have hidentity :=
      aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
        A Omega p hOmega
    change crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) -
        Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p -
        star (Polynomial.aeval A p) * Polynomial.aeval A p +
        star (Polynomial.aeval A p) * Polynomial.aeval A p = _
    rw [hidentity]
    module
  have hcstar : (starRingEnd ℂ) c = c := by
    simp only [c, Complex.conj_ofReal]
  have hadjointQ : c • star (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
      star (Polynomial.aeval A
        (crouzeixProductRemainderPolynomial Omega p)) := by
    rw [← hQnorm]
    change c • ContinuousLinearMap.adjoint
        (∫ t in (0 : ℝ)..(2 * Real.pi), Q t) =
      ContinuousLinearMap.adjoint
        (c • (∫ t in (0 : ℝ)..(2 * Real.pi), Q t))
    rw [map_smulₛₗ, hcstar]
  have hrepresentation :
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) +
          star (Polynomial.aeval A
          (crouzeixProductRemainderPolynomial Omega p)) =
        c • (∫ t in (0 : ℝ)..(2 * Real.pi), Q t + star (Q t)) := by
    change _ = c • (∫ t in (0 : ℝ)..(2 * Real.pi),
      Q t + ContinuousLinearMap.adjoint (Q t))
    rw [ContinuousLinearMap.intervalIntegral_add_adjoint hQ]
    change _ = c • ((∫ t in (0 : ℝ)..(2 * Real.pi), Q t) +
      star (∫ t in (0 : ℝ)..(2 * Real.pi), Q t))
    rw [smul_add, hQnorm, hadjointQ]
  rw [hrepresentation]
  rw [← ContinuousLinearMap.nonneg_iff_isPositive]
  change 0 ≤ (2 * Real.pi)⁻¹ •
    (∫ t in (0 : ℝ)..(2 * Real.pi), Q t + star (Q t))
  apply smul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le)
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact hQsymm

/-- The evaluated product remainder is accretive: its quadratic real part is
nonnegative on every vector.  This is the scalar-form consequence of the
positive integrated-variance identity above. -/
theorem re_inner_aeval_crouzeixProductRemainderPolynomial_nonneg_of_cauchy_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    0 ≤ RCLike.re ⟪x,
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) x⟫_ℂ := by
  let H := Polynomial.aeval A
    (crouzeixProductRemainderPolynomial Omega p)
  have hpos :=
    isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support
      A Omega p hOmega hCauchyP hCauchyOne hsupport
  have hreal := hpos.re_inner_nonneg_right x
  have hadjoint : RCLike.re ⟪x, star H x⟫_ℂ =
      RCLike.re ⟪x, H x⟫_ℂ := by
    change RCLike.re ⟪x, ContinuousLinearMap.adjoint H x⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact inner_re_symm _ _
  change 0 ≤ RCLike.re ⟪x, H x⟫_ℂ
  change 0 ≤ RCLike.re ⟪x, (H + star H) x⟫_ℂ at hreal
  rw [add_apply, inner_add_right, map_add, hadjoint] at hreal
  linarith

/-- The generic smooth-domain symmetrized estimate with the canonical
boundary constant.  The Cauchy and outward-support inputs imply
`‖p(A) + G†‖ ≤ 2 * sup_{z ∈ frontier Ω} ‖p(z)‖`. -/
theorem
    norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_frontier_of_cauchy_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
      2 * polynomialSupNorm p (frontier Omega.carrier) := by
  apply
    norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_of_cauchy_support
      A Omega p hOmega hCauchyP hCauchyOne hsupport
      (polynomialSupNorm_nonneg p _)
  intro t _
  exact norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega p t

/-- If a compact set `L` contains the smooth frontier, the generic
symmetrized estimate is controlled by the polynomial sup norm on `L`.  This
is the stagewise form consumed by compact-exhaustion arguments. -/
theorem
    norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (L : Set ℂ) (hL : IsCompact L) (hfrontier : frontier Omega.carrier ⊆ L)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
      2 * polynomialSupNorm p L := by
  calc
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (frontier Omega.carrier) :=
      norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_frontier_of_cauchy_support
        A Omega p hOmega hCauchyP hCauchyOne hsupport
    _ ≤ 2 * polynomialSupNorm p L :=
      mul_le_mul_of_nonneg_left
        (polynomialSupNorm_mono_of_isCompact p hfrontier hL) (by norm_num)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
