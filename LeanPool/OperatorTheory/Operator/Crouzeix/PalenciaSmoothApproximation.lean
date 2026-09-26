/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.CompactThickeningApprox
public import LeanPool.OperatorTheory.Operator.Crouzeix.GeneralSymmetrized
public import LeanPool.OperatorTheory.Operator.Crouzeix.PalenciaExhaustion
public import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialCauchyMass
public import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialCompanionConvergence
public import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialCompanionNormalization
public import LeanPool.OperatorTheory.Operator.Crouzeix.ProductBase
public import LeanPool.OperatorTheory.Operator.NumericalRange.Convex

/-!
# Crouzeix--Palencia assembly on smooth thickening domains

This file connects the concrete closed-thickening exhaustion to the sharp
smooth-boundary symmetrized estimate.  It shows that the full
Crouzeix--Palencia conclusion follows if the open metric thickenings of the
closed numerical range admit compatible smooth Jordan parametrizations with
the polynomial Cauchy and support identities, and if the remaining product
estimate holds at every stage.  It also packages the published companion
route: a uniformly sup-norm-contractive sequence of polynomials converging at
the operator to the canonical auxiliary operator suffices.  The resolvent
Cauchy mass identity is the constant-polynomial specialization of the
polynomial formula.

The hypotheses deliberately expose the remaining analytic gaps.  No
smoothness of an arbitrary metric-thickening frontier, general-domain Cauchy
theorem, polynomial companion approximation, or product inequality is inferred
from the set-theoretic approximation alone.

## Main declaration

* `crouzeix_palencia_of_convexThickening_cauchy_support_product` -- exact
  Crouzeix--Palencia from compatible smooth thickening data and stagewise
  positive-degree product bounds.
* `crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions`
  -- exact Crouzeix--Palencia from the same smooth data and convergent
  polynomial companions.
* `crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions`
  -- the natural additive-error polynomial-approximation interface.
* `crouzeixPalencia_of_thickening_cauchy_support_contractive_companion_approximation`
  -- the published-route interface in terms of contractive interior scalar
  companions, uniform polynomial approximation, and calculus identification.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem isCompact_closure_numericalRange_smoothApproximation
    (A : E →L[ℂ] E) : IsCompact (closure (numericalRange A)) := by
  have hbounded : Bornology.IsBounded (numericalRange A) :=
    Metric.isBounded_closedBall.subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz)
  exact hbounded.isCompact_closure

variable [CompleteSpace E]

/-- Suppose the open thickenings of the closed numerical range are realized
by smooth Jordan domains whose parametrizations satisfy the polynomial Cauchy
identity and whose outward normals support the numerical range.  If the
canonical Crouzeix auxiliary operator at every stage is the operator-norm
limit of polynomials uniformly contractive for the corresponding closed-stage
sup norm, then the exact Crouzeix--Palencia estimate follows.

The all-polynomial Cauchy formula supplies the finite stagewise calculus bound
needed to run the fourth-power best-constant bootstrap. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ q : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (q j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hCauchy : ∀ n : ℕ,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := fun n ↦
    contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
      A (Omega n) (fun p ↦ hCauchyP p n)
  have hCauchyOne : ∀ n : ℕ,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (Omega n).boundaryParam t •
          resolvent A ((Omega n).boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    intro n
    simpa only [contourIntegral, one_smul] using hCauchy n
  let K : Set ℂ := closure (numericalRange A)
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_closure_numericalRange_smoothApproximation A
  have hKconvex : Convex ℝ K := by
    simpa only [K] using (convex_numericalRange A).closure
  have hstageCompact : ∀ n, IsCompact (compactThickeningApprox K n) :=
    fun _ ↦ hKcompact.cthickening
  have hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        C * polynomialSupNorm p (compactThickeningApprox K n) := by
    intro n
    have hOmega : K ⊆ (Omega n).carrier := by
      rw [hcarrier n]
      exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
    obtain ⟨C, hC, hbound⟩ :=
      exists_global_polynomial_calculus_bound_frontier_of_cauchy
        A (Omega n) hOmega (fun p ↦ hCauchyP p n)
    refine ⟨C, hC, ?_⟩
    intro p
    calc
      ‖Polynomial.aeval A p‖ ≤
          C * polynomialSupNorm p (frontier (Omega n).carrier) := hbound p
      _ ≤ C * polynomialSupNorm p (compactThickeningApprox K n) :=
        mul_le_mul_of_nonneg_left
          (polynomialSupNorm_mono_of_isCompact p (by
            rw [hcarrier n]
            exact frontier_convexThickeningApprox_subset_compactThickeningApprox K n)
            (hstageCompact n)) hC
  apply crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
    A (by simpa only [K] using hfinite)
  intro p n
  obtain ⟨q, hq, hq_lim⟩ := hcompanion p n
  refine ⟨crouzeixPolynomialAuxiliaryOperator A (Omega n) p,
    q, hq, hq_lim, ?_⟩
  apply
    norm_aeval_add_star_auxiliary_le_two_mul_polynomialNorm_of_frontier_subset_of_cauchy_support
      A (Omega n) p
      (compactThickeningApprox (closure (numericalRange A)) n)
      (by simpa only [K] using hstageCompact n)
  · rw [hcarrier n]
    exact frontier_convexThickeningApprox_subset_compactThickeningApprox
      (closure (numericalRange A)) n
  · rw [hcarrier n]
    exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
  · exact hCauchyP p n
  · exact hCauchyOne n
  · intro t ht w hw
    exact hsupport n t ht w hw

/-- The smooth-stage companion assembly only needs the natural additive-error
form of uniform polynomial approximation.  A sequence bounded by
`supNorm p + 1 / (j + 1)` is asymptotically rescaled to an exactly contractive
one before applying
`crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions`.

In the nontrivial Hilbert-space case, every compact thickening is infinite.
Thus a zero stage sup norm forces `p = 0`, and conjugate linearity makes the
canonical auxiliary operator zero, discharging the necessary normalization
edge case. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (r j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
              (compactThickeningApprox (closure (numericalRange A)) n) +
            1 / ((j : ℝ) + 1)) ∧
        Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    constructor
    · exact spectrum_subset_closure_numericalRange A
    · intro p
      have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (polynomialSupNorm_nonneg p (closure (numericalRange A)))
  · let _ := hE
    let K : Set ℂ := closure (numericalRange A)
    have hKcompact : IsCompact K := by
      simpa only [K] using
        isCompact_closure_numericalRange_smoothApproximation A
    have hKnonempty : K.Nonempty := by
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      simpa only [K] using hW.mono subset_closure
    apply
      crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
        A Omega hcarrier hCauchyP hsupport
    intro p n
    obtain ⟨r, hr, hrlim⟩ := hcompanion p n
    apply exists_tendsto_polynomial_companions_of_add_one_div_bounds
      A (compactThickeningApprox K n) (polynomialSupNorm p
        (compactThickeningApprox K n))
      (polynomialSupNorm_nonneg p (compactThickeningApprox K n))
      (crouzeixPolynomialAuxiliaryOperator A (Omega n) p)
    · intro hm
      have hp : p = 0 :=
        polynomial_eq_zero_of_polynomialSupNorm_eq_zero p
          (hKcompact.cthickening : IsCompact (compactThickeningApprox K n))
          (compactThickeningApprox_infinite K n hKnonempty) hm
      subst p
      calc
        crouzeixPolynomialAuxiliaryOperator A (Omega n) 0 =
            crouzeixPolynomialAuxiliaryOperator A (Omega n)
              (0 • (1 : Polynomial ℂ)) := by rw [zero_smul]
        _ = star (0 : ℂ) •
            crouzeixPolynomialAuxiliaryOperator A (Omega n) 1 :=
          crouzeixPolynomialAuxiliaryOperator_smul A (Omega n) 0 1
        _ = 0 := by simp only [star_zero, zero_smul]
    · simpa only [K] using hr
    · simpa only [K] using hrlim

/-- The published companion route in scalar analytic form.  At every smooth
stage, suppose an interior scalar companion `g` is bounded by the stage sup
norm of `p`, is uniformly approximated there by polynomials `r j` with error
`1 / (j + 1)`, and those polynomial evaluations converge at `A` to the
canonical contour auxiliary.  Then the exact Crouzeix--Palencia estimate
follows.

This theorem leaves precisely the analytic companion contraction, polynomial
approximation, and functional-calculus identification as explicit inputs; the
additive-to-exact normalization and fourth-power bootstrap are internal. -/
theorem
    crouzeixPalencia_of_thickening_cauchy_support_contractive_companion_approximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
        (∀ z ∈ compactThickeningApprox (closure (numericalRange A)) n,
          ‖g z‖ ≤ polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        (∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
        Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
      A Omega hcarrier hCauchyP hsupport
  intro p n
  obtain ⟨g, r, hg, happrox, hrlim⟩ := hcompanion p n
  refine ⟨r, ?_, hrlim⟩
  intro j
  exact polynomialSupNorm_le_add_of_uniform_approximation
    (r j) (compactThickeningApprox (closure (numericalRange A)) n) g
    (polynomialSupNorm p
      (compactThickeningApprox (closure (numericalRange A)) n))
    (1 / ((j : ℝ) + 1))
    (polynomialSupNorm_nonneg p
      (compactThickeningApprox (closure (numericalRange A)) n))
    (by positivity) hg (happrox j)

/-- The published scalar-companion route with functional-calculus convergence
derived rather than assumed.  At every stage, a continuous boundary datum is
contractive on the compact control set and uniformly approximated there by
polynomials.  The single remaining calculus input is the Plemelj identity
saying that its normalized resolvent contour integral is the canonical
conjugate-polynomial auxiliary.

The quantitative contour convergence theorem turns these data into the
operator-limit premise of
`crouzeixPalencia_of_thickening_cauchy_support_contractive_companion_approximation`.
-/
theorem
    crouzeixPalencia_of_thickening_cauchy_support_continuous_companion_approximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
        ContinuousOn g
          ((Omega n).boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
        (∀ z ∈ compactThickeningApprox (closure (numericalRange A)) n,
          ‖g z‖ ≤ polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        (∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
        crouzeixAuxiliaryOperator A (Omega n) g =
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : Set ℂ := closure (numericalRange A)
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_closure_numericalRange_smoothApproximation A
  have hKconvex : Convex ℝ K := by
    simpa only [K] using (convex_numericalRange A).closure
  apply
    crouzeixPalencia_of_thickening_cauchy_support_contractive_companion_approximation
      A Omega hcarrier hCauchyP hsupport
  intro p n
  obtain ⟨g, r, hgcont, hgbound, happrox, hPlemelj⟩ := hcompanion p n
  refine ⟨g, r, hgbound, happrox, ?_⟩
  have hOmega : closure (numericalRange A) ⊆ (Omega n).carrier := by
    rw [hcarrier n]
    exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
  have hboundaryApprox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval ((Omega n).boundaryParam t) (r j) -
        g ((Omega n).boundaryParam t)‖ ≤ 1 / ((j : ℝ) + 1) := by
    intro j t ht
    apply happrox j ((Omega n).boundaryParam t)
    have hfrontier : (Omega n).boundaryParam t ∈
        frontier (Omega n).carrier := by
      rw [← (Omega n).boundaryParam_range]
      exact mem_range_self t
    rw [hcarrier n] at hfrontier
    exact frontier_convexThickeningApprox_subset_compactThickeningApprox
      (closure (numericalRange A)) n hfrontier
  have hlim :=
    tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
      A (Omega n) g r hOmega hgcont (fun j ↦ hCauchyP (r j) n)
        hboundaryApprox
  simpa only [hPlemelj] using hlim

/-- Suppose the open thickenings of the closed numerical range are realized
by smooth Jordan domains whose parametrizations satisfy the polynomial Cauchy
identity and whose outward normals support the numerical range.  If the
associated auxiliary operators also satisfy the sharp product bound on the
closed thickenings for positive-degree polynomials, then the exact
Crouzeix--Palencia polynomial spectral-set estimate follows.  Specializing
the polynomial identity to `C 1` supplies the resolvent mass identity and,
through it, the degree-zero product case. -/
theorem crouzeix_palencia_of_convexThickening_cauchy_support_product
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hprod : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p‖ ≤
        polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hCauchy : ∀ n : ℕ,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := fun n ↦
    contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
      A (Omega n) (fun p ↦ hCauchyP p n)
  have hCauchyOne : ∀ n : ℕ,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (Omega n).boundaryParam t •
          resolvent A ((Omega n).boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    intro n
    simpa only [contourIntegral, one_smul] using hCauchy n
  let K : Set ℂ := closure (numericalRange A)
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_closure_numericalRange_smoothApproximation A
  have hKconvex : Convex ℝ K := by
    simpa only [K] using (convex_numericalRange A).closure
  have hstageCompact : ∀ n, IsCompact (compactThickeningApprox K n) :=
    fun _ ↦ hKcompact.cthickening
  apply crouzeix_palencia_of_compactThickening_auxiliary_bounds A
  intro p n
  refine ⟨crouzeixPolynomialAuxiliaryOperator A (Omega n) p, ?_, ?_⟩
  · apply
      norm_aeval_add_star_auxiliary_le_two_mul_polynomialNorm_of_frontier_subset_of_cauchy_support
        A (Omega n) p (compactThickeningApprox K n) (hstageCompact n)
    · rw [hcarrier n]
      exact frontier_convexThickeningApprox_subset_compactThickeningApprox K n
    · rw [hcarrier n]
      exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
    · exact hCauchyP p n
    · exact hCauchyOne n
    · intro t ht w hw
      exact hsupport n t ht w hw
  · by_cases hp : p.natDegree = 0
    · rcases subsingleton_or_nontrivial E with hE | hE
      · let _ := hE
        have hzero : Polynomial.aeval A p *
            crouzeixPolynomialAuxiliaryOperator A (Omega n) p = 0 :=
          Subsingleton.elim _ _
        rw [hzero, norm_zero]
        exact sq_nonneg _
      · let _ := hE
        obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
          NormedSpace.sphere_nonempty.mpr zero_le_one
        have hxnorm : ‖x‖ = 1 := by
          rw [Metric.mem_sphere, dist_zero_right] at hx
          exact hx
        have hW : (numericalRange A).Nonempty :=
          ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
        have hKnonempty : K.Nonempty := by
          simpa only [K] using hW.mono subset_closure
        have hstageNonempty :
            (compactThickeningApprox K n).Nonempty :=
          hKnonempty.mono
            (Metric.self_subset_cthickening
              (E := K) (δ := smoothApproxRadius n))
        exact
          norm_aeval_mul_auxiliary_le_polynomialNorm_sq_of_natDegree_eq_zero
            A (Omega n) p hstageNonempty hp (hCauchy n)
    · simpa only [K] using hprod p n (Nat.pos_of_ne_zero hp)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
