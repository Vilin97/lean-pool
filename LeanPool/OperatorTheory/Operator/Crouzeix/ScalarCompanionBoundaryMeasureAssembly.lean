/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialCauchyFromResolventMass
import LeanPool.OperatorTheory.Operator.Crouzeix.ResolventContourHomotopy
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionBoundaryMeasureMass
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionRadialAssembly

/-!
# L4.2 assembly from the boundary double-layer probability measure

The scalar-companion boundary value is contractive once its explicit
double-layer density is an oriented probability density.  This file feeds
that concrete geometric interface into the strongest radial assembly: phase
contractivity is automatic, approximation is needed only for positive-degree
polynomials vanishing at zero, and auxiliary-contour reproduction only after
frontier-sup normalization.

## Main declaration

* `crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero`
  -- the radial Crouzeix--Palencia capstone with the opaque phase hypothesis
  replaced by integrability, unit mass, and oriented frontier support of the
  explicit scalar double-layer density.
* `crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerMass_radial_vanishingAtZero`
  -- the strongest form, where the existing numerical-range support fixes the
  boundary orientation and unit density mass is the only remaining phase
  geometry.
* `crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayer_radial_vanishingAtZero`
  -- oriented convexity also forces unit mass, leaving no separate boundary
  probability-measure premise.
* `crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_radial_vanishingAtZero`
  -- a single resolvent-mass identity also supplies the all-polynomial Cauchy
  representation used by the strongest capstone.
* `crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_basepointWinding_radial_vanishingAtZero`
  -- winding normalization at one carrier point per stage propagates across
  the whole strictly convex carrier.
* `crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_automaticWinding_radial_vanishingAtZero`
  -- oriented numerical-range support also supplies that basepoint
  normalization, so no separate winding premise remains.
-/

open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The strongest radial scalar-companion capstone with sharp phase
contractivity supplied by the explicit boundary double-layer probability
measure. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero
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
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hrho : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      IntervalIntegrable
        (crouzeixBoundaryDoubleLayerDensity (Omega n) xi)
        volume 0 (2 * Real.pi))
    (hmass : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity (Omega n) xi t) = 1)
    (hboundarySupport : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (xi - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_vanishingAtZero
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro n p _hp _hnorm
    exact
      crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
        (Omega n) p (hrho n) (hmass n) (hboundarySupport n)
  · exact happrox
  · exact hPlemelj

/-- Unit density mass and oriented frontier support already make the boundary
double layer a probability measure: integrability follows because a
nonintegrable Bochner integral is zero.  Thus no separate density
integrability witness is needed in this strongest capstone. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerProbability_radial_vanishingAtZero
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
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hmass : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity (Omega n) xi t) = 1)
    (hboundarySupport : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (xi - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro n xi hxi
    exact
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
        (Omega n) xi (hmass n xi hxi)
  · exact hmass
  · exact hboundarySupport
  · exact happrox
  · exact hPlemelj

omit [CompleteSpace E] in
/-- The numerical-range support inequality supplies a point of the open
carrier whose canonical-normal sign holds for every real parameter.  The
carrier cannot be nonempty unless the underlying numerical range is
nonempty; periodicity then extends the fundamental-interval hypothesis. -/
theorem oriented_carrier_point_of_convexThickening_numericalRange_support
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0) :
    ∀ n, ∃ w ∈ (Omega n).carrier, ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
        (w - (Omega n).boundaryParam t)).re ≤ 0 := by
  intro n
  have hr : 0 < smoothApproxRadius n := by
    unfold smoothApproxRadius
    positivity
  have hstage : (Omega n).carrier.Nonempty :=
    (Omega n).carrier_nonempty
  rw [hcarrier n] at hstage
  have hK : (closure (numericalRange A)).Nonempty := by
    change (Metric.thickening (smoothApproxRadius n)
      (closure (numericalRange A))).Nonempty at hstage
    exact (Metric.thickening_nonempty_iff_of_pos hr).mp hstage
  obtain ⟨w, hw⟩ := hK.of_closure
  have hwOmega : w ∈ (Omega n).carrier := by
    rw [hcarrier n]
    exact Metric.self_subset_thickening hr _ (subset_closure hw)
  refine ⟨w, hwOmega, ?_⟩
  apply canonicalNormal_support_all_of_Ioc
  intro t ht
  exact hsupport n t ht w hw

omit [CompleteSpace E] in
/-- The existing numerical-range support inequality fixes the orientation of
every smooth convex thickening and therefore propagates to all of its
frontier points.  Nonemptiness of the smooth carrier forces the numerical
range to be nonempty through the exact thickening identity, providing the
interior point that selects the normal orientation. -/
theorem boundary_support_of_convexThickening_numericalRange_support
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0) :
    ∀ (n : ℕ) (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (xi - (Omega n).boundaryParam t)).re ≤ 0 := by
  intro n xi hxi t ht
  obtain ⟨w, hwOmega, hwside⟩ :=
    oriented_carrier_point_of_convexThickening_numericalRange_support
      A Omega hcarrier hsupport n
  exact (Omega n).frontier_support_of_support_at_mem_carrier
    w hwOmega t (hwside t) xi hxi

/-- In the strongest radial capstone, the numerical-range support hypothesis
already determines the oriented frontier support needed for density
nonnegativity.  Thus unit mass is the only remaining explicit geometric
premise for the boundary double-layer probability measure. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerMass_radial_vanishingAtZero
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
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hmass : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity (Omega n) xi t) = 1)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerProbability_radial_vanishingAtZero
      A Omega hcarrier hCauchyP hsupport hkernel hmass
  · exact
      boundary_support_of_convexThickening_numericalRange_support
        A Omega hcarrier hsupport
  · exact happrox
  · exact hPlemelj

/-- In the strongest convex-thickening capstone, numerical-range support
fixes the boundary orientation and the resulting oriented convex geometry
forces the double-layer density to have unit mass.  Thus phase contractivity
requires neither an abstract phase witness nor any separate density
integrability, positivity, support, or mass premise. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayer_radial_vanishingAtZero
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
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerMass_radial_vanishingAtZero
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro n xi hxi
    obtain ⟨w, hw, hwside⟩ :=
      oriented_carrier_point_of_convexThickening_numericalRange_support
        A Omega hcarrier hsupport n
    exact
      integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
        (Omega n) w hw hwside xi hxi
  · exact happrox
  · exact hPlemelj

/-- The all-polynomial Cauchy representation in the strongest boundary
double-layer capstone can be reduced to a single resolvent-mass identity at
each smooth stage.  The exact polynomial resolvent splitting and vanishing
of its closed-contour remainder supply every polynomial case internally. -/
theorem
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hmass : ∀ n,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayer_radial_vanishingAtZero
      A Omega hcarrier
  · intro p n
    apply polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
      A (Omega n)
    · rw [hcarrier n]
      exact Metric.self_subset_thickening (by
        unfold smoothApproxRadius
        positivity) (closure (numericalRange A))
    · exact hmass n
  · exact hsupport
  · exact hkernel
  · exact happrox
  · exact hPlemelj

/-- Strict convexity makes the scalar winding kernel constant throughout
each carrier.  Hence the strongest resolvent-mass boundary-double-layer
capstone needs winding normalization only at one carrier basepoint per
stage, rather than at every point. -/
theorem
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_basepointWinding_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hmass : ∀ n,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hwind : ∀ n, ∃ c ∈ (Omega n).carrier,
      crouzeixScalarCauchyKernel (Omega n) c = 1)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_radial_vanishingAtZero
      A Omega hcarrier hmass hsupport
  · intro n z hz
    obtain ⟨c, hc, hkc⟩ := hwind n
    exact crouzeixScalarCauchyKernel_eq_one_of_basepoint
      (Omega n) c hc hkc z hz
  · exact happrox
  · exact hPlemelj

/-- Oriented numerical-range support supplies a consistently oriented point
of every smooth carrier, and oriented convex geometry forces the scalar
Cauchy kernel there to have winding one.  Thus the resolvent-mass
boundary-double-layer capstone needs no separate winding hypothesis. -/
theorem
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_automaticWinding_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hmass : ∀ n,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_basepointWinding_radial_vanishingAtZero
      A Omega hcarrier hmass hsupport
  · intro n
    obtain ⟨c, hc, hcside⟩ :=
      oriented_carrier_point_of_convexThickening_numericalRange_support
        A Omega hcarrier hsupport n
    exact ⟨c, hc,
      crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
        (Omega n) c hc hcside c hc⟩
  · exact happrox
  · exact hPlemelj

/-- The numerical-range support condition now supplies both analytic
normalizations that were formerly hypotheses: oriented convex winding gives
the scalar Cauchy kernel, while affine resolvent homotopy gives the operator
resolvent mass.  Only polynomial approximation and auxiliary reproduction
remain explicit beyond the exact smooth carrier realization. -/
theorem
    crouzeix_palencia_of_convexThickening_support_boundaryDoubleLayer_automaticMass_automaticWinding_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_automaticWinding_radial_vanishingAtZero
      A Omega hcarrier
  · intro n
    obtain ⟨c, hc, hcside⟩ :=
      oriented_carrier_point_of_convexThickening_numericalRange_support
        A Omega hcarrier hsupport n
    apply
      contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
        A (Omega n) c hc hcside
    rw [hcarrier n]
    have hcompact : IsCompact (closure (numericalRange A)) := by
      have hbounded : Bornology.IsBounded (numericalRange A) :=
        Metric.isBounded_closedBall.subset (fun z hz => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact norm_le_of_mem_numericalRange A hz)
      exact hbounded.isCompact_closure
    exact
      (convexThickeningApprox_spec (closure (numericalRange A)) hcompact
        (convex_numericalRange A).closure).1 n |>.1
  · exact hsupport
  · exact happrox
  · exact hPlemelj

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
