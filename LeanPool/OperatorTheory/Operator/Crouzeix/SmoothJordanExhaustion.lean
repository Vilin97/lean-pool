/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ResolventContourHomotopy
import LeanPool.OperatorTheory.Operator.Crouzeix.PalenciaSmoothApproximation
import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialCauchyFromResolventMass
import LeanPool.OperatorTheory.Operator.Crouzeix.ResolventCauchyKernel
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionBoundaryMeasureMass
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionRadialAssembly

/-!
# Crouzeix--Palencia assembly over smooth Jordan exhaustions

The analytic argument only needs an antitone compact exhaustion whose stages
contain smooth Jordan frontiers; it does not need those carriers to equal a
particular metric thickening.  This module isolates that invariant interface,
derives contour mass and winding from oriented numerical-range support, and
packages scalar-companion approximation into the sharp exhaustion limit.
-/

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real

/-- A uniformly convergent polynomial sequence has a subsequence with the
explicit error schedule `1, 1/2, 1/3, ...`.  This converts the standard output
of a polynomial approximation theorem into the quantitative interface used by
the exhaustion assembly. -/
theorem exists_polynomial_rate_approximation_of_tendstoUniformlyOn
    (K : Set ℂ) (f : ℂ → ℂ) (q : ℕ → Polynomial ℂ)
    (hlim : TendstoUniformlyOn
      (fun j z ↦ Polynomial.eval z (q j)) f atTop K) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ K →
        ‖Polynomial.eval z (r j) - f z‖ ≤ 1 / ((j : ℝ) + 1) := by
  have hevent : ∀ j : ℕ, ∀ᶠ k in atTop,
      ∀ z ∈ K,
        dist (f z) (Polynomial.eval z (q k)) < 1 / ((j : ℝ) + 1) := by
    intro j
    apply (Metric.tendstoUniformlyOn_iff.mp hlim)
    positivity
  choose N hN using fun j ↦ (eventually_atTop.1 (hevent j))
  refine ⟨fun j ↦ q (N j), ?_⟩
  intro j z hz
  have hlt := hN j (N j) le_rfl z hz
  rw [dist_eq_norm] at hlt
  simpa only [norm_sub_rev] using hlt.le

/-- A strictly nested smooth Jordan exhaustion of a compact planar target.
The closed stages are the compact control sets used by the Palencia limit;
adjacent closure containment gives their antitonicity automatically.

Constructing this bundle for an arbitrary compact convex planar set is the
remaining geometric smooth-approximation input to the terminal assembly. -/
structure StrictNestedSmoothJordanExhaustion (K : Set ℂ) where
  /-- The nested smooth Jordan domain at each stage of the exhaustion. -/
  domain : ℕ → SmoothJordanDomain
  target_subset : ∀ n, K ⊆ (domain n).carrier
  isCompact_closure : ∀ n, IsCompact (closure (domain n).carrier)
  closure_succ_subset : ∀ n,
    closure (domain (n + 1)).carrier ⊆ (domain n).carrier
  iInter_closure : (⋂ n, closure (domain n).carrier) = K

/-- Smooth realizations of the explicit open metric thickenings automatically
form a strict nested smooth Jordan exhaustion.  All closed-stage data comes
from the corresponding compact thickenings; even target nonemptiness follows
from nonemptiness of the represented smooth carrier. -/
noncomputable def StrictNestedSmoothJordanExhaustion.ofConvexThickening
    (K : Set ℂ) (hcompact : IsCompact K) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier = convexThickeningApprox K n) :
    StrictNestedSmoothJordanExhaustion K := by
  have hnonempty : K.Nonempty := by
    have hstage := (Omega 0).carrier_nonempty
    rw [hcarrier 0] at hstage
    unfold convexThickeningApprox at hstage
    apply (Metric.thickening_nonempty_iff_of_pos ?_).mp hstage
    unfold smoothApproxRadius
    positivity
  let hspec := compactThickeningApprox_spec K hcompact hnonempty
  refine
    { domain := Omega
      target_subset := ?_
      isCompact_closure := ?_
      closure_succ_subset := ?_
      iInter_closure := ?_ }
  · intro n
    rw [hcarrier n]
    apply Metric.self_subset_thickening
    unfold smoothApproxRadius
    positivity
  · intro n
    rw [hcarrier n]
    unfold convexThickeningApprox
    rw [closure_thickening]
    · exact hspec.2.1 n
    · unfold smoothApproxRadius
      positivity
  · intro n
    rw [hcarrier (n + 1), hcarrier n]
    exact closure_convexThickeningApprox_succ_subset K n
  · have heq : ∀ n, closure (Omega n).carrier =
        compactThickeningApprox K n := by
      intro n
      rw [hcarrier n]
      unfold convexThickeningApprox compactThickeningApprox
      rw [closure_thickening]
      unfold smoothApproxRadius
      positivity
    simp_rw [heq]
    exact hspec.2.2.2

/-- Closed disks provide an unconditional model of the strict nested smooth
Jordan exhaustion: enlarge the radius by `1 / (n + 1)` and use the standard
circle parametrization. -/
noncomputable def StrictNestedSmoothJordanExhaustion.closedBall
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    StrictNestedSmoothJordanExhaustion (Metric.closedBall c R) := by
  let Omega := (smoothClosedBallApproximation c R hR).domain
  apply StrictNestedSmoothJordanExhaustion.ofConvexThickening
    (Metric.closedBall c R) (isCompact_closedBall c R) Omega
  intro n
  change Metric.ball c (smoothApproxRadius n + R) =
    Metric.thickening (smoothApproxRadius n) (Metric.closedBall c R)
  exact (thickening_closedBall (by
    unfold smoothApproxRadius
    positivity) hR c).symm

/-- The open carrier of a closed-disk exhaustion stage is its concentric
radius-enlarged disk. -/
@[simp] theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).carrier =
      Metric.ball c (smoothApproxRadius n + R) := by
  rfl

/-- The boundary trace of a closed-disk exhaustion stage is its standard
circle parametrization. -/
@[simp] theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).boundaryParam =
      circleMap c (smoothApproxRadius n + R) := by
  rfl

/-- The derivative of a closed-disk exhaustion contour is the usual tangent
to its standard circle parametrization. -/
theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (t : ℝ) :
    deriv
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).boundaryParam t =
      circleMap 0 (smoothApproxRadius n + R) t * I := by
  rw [StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam,
    deriv_circleMap]

/-- The compact control set of a closed-disk exhaustion stage is its
concentric radius-enlarged closed disk. -/
theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    closure
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).carrier =
      Metric.closedBall c (smoothApproxRadius n + R) := by
  rw [StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier,
    closure_ball]
  unfold smoothApproxRadius
  positivity

/-- The frontier of a closed-disk exhaustion stage is its concentric metric
sphere. -/
theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    frontier
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).carrier =
      Metric.sphere c (smoothApproxRadius n + R) := by
  rw [StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier,
    frontier_ball]
  unfold smoothApproxRadius
  positivity

/-- Multiplication of the disk-contour tangent by `-I` yields the radial
outward normal. -/
theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (t : ℝ) :
    -I * deriv
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).boundaryParam t =
      circleMap 0 (smoothApproxRadius n + R) t := by
  rw [StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv]
  linear_combination
    (-circleMap 0 (smoothApproxRadius n + R) t) * I_sq

/-- Every canonical closed scalar companion on a bundled smooth stage has the
regularity required by complex polynomial approximation: it is continuous on
the compact closure and complex differentiable in the carrier.  Canonical
orientation supplies winding one, while compactness supplies boundedness. -/
theorem StrictNestedSmoothJordanExhaustion.diffContOnCl_canonicalScalarCompanion
    {K : Set ℂ} (Omega : StrictNestedSmoothJordanExhaustion K)
    (p : Polynomial ℂ) (n : ℕ) :
    DiffContOnCl ℂ
      (crouzeixPolynomialScalarCompanionClosedExtension
        (Omega.domain n).canonicalOrientation p)
      (Omega.domain n).canonicalOrientation.carrier := by
  let Psi := (Omega.domain n).canonicalOrientation
  obtain ⟨c, hc, hc0⟩ :=
    (Omega.domain n).exists_oriented_point_canonicalOrientation
  have hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
        (c - Psi.boundaryParam t)).re ≤ 0 :=
    Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
  have hkernel : ∀ z ∈ Psi.carrier,
      crouzeixScalarCauchyKernel Psi z = 1 :=
    crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
      Psi c hc hcside
  have hbounded : Bornology.IsBounded Psi.carrier := by
    rw [show Psi.carrier = (Omega.domain n).carrier by
      exact SmoothJordanDomain.canonicalOrientation_carrier _]
    exact (Omega.isCompact_closure n).isBounded.subset subset_closure
  apply diffContOnCl_crouzeixPolynomialScalarCompanion_extension
    Psi p
      (crouzeixPolynomialScalarCompanionClosedExtension Psi p)
  · exact
      continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
        Psi p hbounded hkernel
  · intro z hz
    exact crouzeixPolynomialScalarCompanionClosedExtension_eq Psi p hz

/-- The complex polynomial approximation property needed at a smooth Jordan
stage: every function continuous on the closure and complex differentiable in
the carrier is a compact-uniform limit of complex polynomials.  This is the
Mergelyan conclusion specialized to the represented domain. -/
def SmoothJordanDomain.HasMergelyanPolynomialApproximation
    (Omega : SmoothJordanDomain) : Prop :=
  ∀ f : ℂ → ℂ, DiffContOnCl ℂ f Omega.carrier →
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun j z ↦ Polynomial.eval z (q j)) f atTop
        (closure Omega.carrier)

@[simp] theorem SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
    (Omega : SmoothJordanDomain) :
    Omega.reverseOrientation.HasMergelyanPolynomialApproximation ↔
      Omega.HasMergelyanPolynomialApproximation := by
  rfl

@[simp] theorem SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
    (Omega : SmoothJordanDomain) :
    Omega.canonicalOrientation.HasMergelyanPolynomialApproximation ↔
      Omega.HasMergelyanPolynomialApproximation := by
  unfold SmoothJordanDomain.HasMergelyanPolynomialApproximation
  rw [SmoothJordanDomain.canonicalOrientation_carrier]

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The sharp Crouzeix--Palencia bound over an arbitrary antitone compact
exhaustion, assuming the polynomial Cauchy formula and approximability of the
stagewise auxiliary operators. -/
theorem crouzeix_palencia_of_smoothJordan_exhaustion_cauchy_support_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfrontier : ∀ n, frontier (Omega n).carrier ⊆ K n)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
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
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hCauchy : ∀ n : ℕ,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := fun n =>
    contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
      A (Omega n) (fun p => hCauchyP p n)
  have hCauchyOne : ∀ n : ℕ,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (Omega n).boundaryParam t •
          resolvent A ((Omega n).boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    intro n
    simpa only [contourIntegral, one_smul] using hCauchy n
  have hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p (K n) := by
    intro n
    obtain ⟨C, hC, hbound⟩ :=
      exists_global_polynomial_calculus_bound_frontier_of_cauchy
        A (Omega n) (hOmega n) (fun p => hCauchyP p n)
    refine ⟨C, hC, ?_⟩
    intro p
    exact (hbound p).trans (mul_le_mul_of_nonneg_left
      (polynomialSupNorm_mono_of_isCompact p (hfrontier n) (hcompact n)) hC)
  apply crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
    A K hanti hcompact hnonempty hinter hfinite
  intro p n
  obtain ⟨q, hq, hqLim⟩ := hcompanion p n
  refine ⟨crouzeixPolynomialAuxiliaryOperator A (Omega n) p,
    q, hq, hqLim, ?_⟩
  exact
    norm_aeval_add_star_auxiliary_le_two_mul_polynomialNorm_of_frontier_subset_of_cauchy_support
      A (Omega n) p (K n) (hcompact n) (hfrontier n) (hOmega n)
        (hCauchyP p n) (hCauchyOne n) (hsupport n)

/-- An oriented point in every smooth Jordan carrier supplies the resolvent
mass, hence the polynomial Cauchy formula needed by the exhaustion theorem. -/
theorem crouzeixPalencia_of_smoothExhaustion_oriented_support_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfrontier : ∀ n, frontier (Omega n).carrier ⊆ K n)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (horiented : ∀ n, ∃ c ∈ (Omega n).carrier, ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
        (c - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ q : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hmass : ∀ n,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    intro n
    obtain ⟨c, hc, hcside⟩ := horiented n
    exact
      contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
        A (Omega n) c hc hcside (hOmega n)
  apply
    crouzeix_palencia_of_smoothJordan_exhaustion_cauchy_support_tendsto_polynomial_companions
      A Omega K hanti hcompact hnonempty hinter hfrontier hOmega
  · intro p n
    exact polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
      A (Omega n) (hOmega n) (hmass n) p
  · exact hsupport
  · exact hcompanion

/-- Numerical-range support automatically supplies the oriented carrier point
at every stage of a smooth Jordan exhaustion. -/
theorem crouzeix_palencia_of_smoothJordan_exhaustion_support_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfrontier : ∀ n, frontier (Omega n).carrier ⊆ K n)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ q : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
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
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    let c : ℂ := ⟪x, A x⟫_ℂ
    have hcW : c ∈ numericalRange A :=
      (mem_numericalRange A c).mpr ⟨x, hxnorm, rfl⟩
    apply
      crouzeixPalencia_of_smoothExhaustion_oriented_support_tendsto_polynomial_companions
        A Omega K hanti hcompact hnonempty hinter hfrontier hOmega hsupport
    · intro n
      refine ⟨c, hOmega n (subset_closure hcW), ?_⟩
      apply canonicalNormal_support_all_of_Ioc
      intro t ht
      exact hsupport n t ht c hcW
    · exact hcompanion

/-- Full scalar-companion assembly over a realistic smooth Jordan exhaustion:
uniform polynomial approximation on each compact stage and the Plemelj
identification imply the sharp `1 + sqrt 2` spectral-set bound. -/
theorem crouzeix_palencia_of_smoothJordan_exhaustion_support_scalarCompanion_approximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
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
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    let c : ℂ := ⟪x, A x⟫_ℂ
    have hcW : c ∈ numericalRange A :=
      (mem_numericalRange A c).mpr ⟨x, hxnorm, rfl⟩
    have horiented : ∀ n, c ∈ (Omega n).carrier ∧ ∀ t : ℝ,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (c - (Omega n).boundaryParam t)).re ≤ 0 := by
      intro n
      refine ⟨hOmega n (subset_closure hcW), ?_⟩
      apply canonicalNormal_support_all_of_Ioc
      intro t ht
      exact hsupport n t ht c hcW
    have hmass : ∀ n,
        contourIntegral (resolvent A) (Omega n).boundaryParam =
          (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
      intro n
      exact
        contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
          A (Omega n) c (horiented n).1 (horiented n).2 (hOmega n)
    have hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
        Polynomial.aeval A p =
          (2 * (Real.pi : ℂ) * I)⁻¹ •
            contourIntegral
              (fun z => Polynomial.eval z p • resolvent A z)
              (Omega n).boundaryParam := by
      intro p n
      exact polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
        A (Omega n) (hOmega n) (hmass n) p
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_cauchy_support_tendsto_polynomial_companions
        A Omega K hanti hcompact hnonempty hinter
    · intro n
      rw [hK n]
      exact frontier_subset_closure
    · exact hOmega
    · exact hCauchyP
    · exact hsupport
    · intro p n
      have hkernel : ∀ z ∈ (Omega n).carrier,
          crouzeixScalarCauchyKernel (Omega n) z = 1 :=
        crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
          (Omega n) c (horiented n).1 (horiented n).2
      have hphase : CrouzeixBoundaryPhaseContractive (Omega n) p :=
        crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
          (Omega n) c (horiented n).1 (horiented n).2 p
      obtain ⟨r, hr⟩ := happrox p n
      have hr' : ∀ (j : ℕ) (z : ℂ), z ∈ closure (Omega n).carrier →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1) := by
        intro j z hz
        apply hr j z
        rwa [hK n]
      obtain ⟨g, q, hgcont, hgbound, hqapprox, hgaux⟩ :=
        exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform_radial
          A (Omega n) p hkernel hphase r hr' (hPlemelj p n)
      have hboundaryApprox : ∀ (j : ℕ) (t : ℝ),
          t ∈ Icc (0 : ℝ) (2 * Real.pi) →
          ‖Polynomial.eval ((Omega n).boundaryParam t) (q j) -
            g ((Omega n).boundaryParam t)‖ ≤ 1 / ((j : ℝ) + 1) := by
        intro j t _ht
        apply hqapprox j
        apply frontier_subset_closure
        rw [← (Omega n).boundaryParam_range]
        exact mem_range_self t
      have hlim :=
        tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
          A (Omega n) g q (hOmega n) hgcont
            (fun j => hCauchyP (q j) n) hboundaryApprox
      have hlim' : Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p)) := by
        simpa only [hgaux] using hlim
      apply exists_tendsto_polynomial_companions_of_uniform_approximation
        A (K n) (polynomialSupNorm p (K n))
          (polynomialSupNorm_nonneg p (K n)) g ?_
          (crouzeixPolynomialAuxiliaryOperator A (Omega n) p) ?_ q ?_ hlim'
      · intro z hz
        have hgb := hgbound z (by rwa [← hK n])
        simpa only [hK n] using hgb
      · intro hm
        have hpzero : p = 0 :=
          polynomial_eq_zero_of_polynomialSupNorm_eq_zero p (hcompact n)
            ((Omega n).frontier_infinite.mono (by
              rw [hK n]
              exact frontier_subset_closure)) hm
        subst p
        calc
          crouzeixPolynomialAuxiliaryOperator A (Omega n) 0 =
              crouzeixPolynomialAuxiliaryOperator A (Omega n)
                (0 • (1 : Polynomial ℂ)) := by rw [zero_smul]
          _ = star (0 : ℂ) •
              crouzeixPolynomialAuxiliaryOperator A (Omega n) 1 :=
            crouzeixPolynomialAuxiliaryOperator_smul A (Omega n) 0 1
          _ = 0 := by simp only [star_zero, zero_smul]
      · intro j z hz
        apply hqapprox j z
        rwa [← hK n]

/-- Constant-shift and scaling invariance reduce the scalar-companion inputs
over a smooth Jordan exhaustion to positive-degree polynomials that vanish at
zero; contour reproduction need only be checked after frontier normalization. -/
theorem
    crouzeixPalencia_of_smoothExhaustion_support_companion_radialZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
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
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    let c : ℂ := ⟪x, A x⟫_ℂ
    have hcW : c ∈ numericalRange A :=
      (mem_numericalRange A c).mpr ⟨x, hxnorm, rfl⟩
    have horiented : ∀ n, c ∈ (Omega n).carrier ∧ ∀ t : ℝ,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (c - (Omega n).boundaryParam t)).re ≤ 0 := by
      intro n
      refine ⟨hOmega n (subset_closure hcW), ?_⟩
      apply canonicalNormal_support_all_of_Ioc
      intro t ht
      exact hsupport n t ht c hcW
    have hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
        crouzeixScalarCauchyKernel (Omega n) z = 1 := by
      intro n
      exact crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
        (Omega n) c (horiented n).1 (horiented n).2
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_support_scalarCompanion_approximation
        A Omega K hanti hcompact hnonempty hinter hK hOmega hsupport
    · intro p n
      by_cases hp : 0 < p.natDegree
      · let q := p - Polynomial.C (Polynomial.eval 0 p)
        have hqdegree : 0 < q.natDegree := by
          simpa only [q, Polynomial.natDegree_sub_C] using hp
        have hqzero : Polynomial.eval 0 q = 0 := by
          simp only [q, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
        have hqapprox := happrox q n hqdegree hqzero
        have hS : K n ⊆ closure (Omega n).carrier := by
          intro z hz
          simpa only [hK n] using hz
        have htransfer :=
          exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
            (Omega n) q (Polynomial.eval 0 p) (hkernel n)
            (K n) hS (fun j => 1 / ((j : ℝ) + 1)) hqapprox
        have hqadd : q + Polynomial.C (Polynomial.eval 0 p) = p := by
          dsimp only [q]
          abel
        rw [hqadd] at htransfer
        exact htransfer
      · have hpzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
        let a := p.coeff 0
        have hpC : p = Polynomial.C a :=
          Polynomial.eq_C_of_natDegree_eq_zero hpzero
        rw [hpC]
        refine ⟨fun _ => Polynomial.C (star a), ?_⟩
        intro j z hz
        have hzclosure : z ∈ closure (Omega n).carrier := by
          simpa only [hK n] using hz
        rw [Polynomial.eval_C,
          crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
            (Omega n) a (hkernel n) hzclosure,
          sub_self, norm_zero]
        positivity
    · intro p n
      exact
        crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
          A (Omega n) (hOmega n) (hkernel n)
            (fun q hq hqzero hqnorm => hPlemelj q n hq hqzero hqnorm) p

/-- On a strictly nested smooth exhaustion, polynomial approximation of the
closed scalar companions is enough: integration on the next inner contour
automatically reproduces the polynomial auxiliary on the current contour. -/
theorem
    crouzeix_palencia_of_smoothJordan_exhaustion_support_nested_scalarCompanion_approximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hnest : ∀ n,
      closure (Omega (n + 1)).carrier ⊆ (Omega n).carrier)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1)) :
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
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    let c : ℂ := ⟪x, A x⟫_ℂ
    have hcW : c ∈ numericalRange A :=
      (mem_numericalRange A c).mpr ⟨x, hxnorm, rfl⟩
    have horiented : ∀ n, c ∈ (Omega n).carrier ∧ ∀ t : ℝ,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (c - (Omega n).boundaryParam t)).re ≤ 0 := by
      intro n
      refine ⟨hOmega n (subset_closure hcW), ?_⟩
      apply canonicalNormal_support_all_of_Ioc
      intro t ht
      exact hsupport n t ht c hcW
    have hmass : ∀ n,
        contourIntegral (resolvent A) (Omega n).boundaryParam =
          (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
      intro n
      exact
        contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
          A (Omega n) c (horiented n).1 (horiented n).2 (hOmega n)
    have hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
        Polynomial.aeval A p =
          (2 * (Real.pi : ℂ) * I)⁻¹ •
            contourIntegral
              (fun z => Polynomial.eval z p • resolvent A z)
              (Omega n).boundaryParam := by
      intro p n
      exact polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
        A (Omega n) (hOmega n) (hmass n) p
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_cauchy_support_tendsto_polynomial_companions
        A Omega K hanti hcompact hnonempty hinter
    · intro n
      rw [hK n]
      exact frontier_subset_closure
    · exact hOmega
    · exact hCauchyP
    · exact hsupport
    · intro p n
      have hkernel : ∀ z ∈ (Omega n).carrier,
          crouzeixScalarCauchyKernel (Omega n) z = 1 :=
        crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
          (Omega n) c (horiented n).1 (horiented n).2
      have hphase : CrouzeixBoundaryPhaseContractive (Omega n) p :=
        crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
          (Omega n) c (horiented n).1 (horiented n).2 p
      obtain ⟨r, hr⟩ := happrox p n
      let g : ℂ → ℂ :=
        crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p
      have hbounded : Bornology.IsBounded (Omega n).carrier :=
        (Omega n).isBounded_carrier_of_cauchyKernel_eq_one hkernel
      have hgcontOuter : ContinuousOn g (closure (Omega n).carrier) := by
        dsimp only [g]
        exact
          continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
            (Omega n) p hbounded hkernel
      have hgcontInner : ContinuousOn g
          ((Omega (n + 1)).boundaryParam ''
            Icc (0 : ℝ) (2 * Real.pi)) := by
        apply hgcontOuter.mono
        rintro z ⟨t, _ht, rfl⟩
        apply subset_closure
        apply hnest n
        apply frontier_subset_closure
        rw [← (Omega (n + 1)).boundaryParam_range]
        exact mem_range_self t
      have hgbound : ∀ z ∈ K n,
          ‖g z‖ ≤ polynomialSupNorm p (K n) := by
        intro z hz
        have hzclosure : z ∈ closure (Omega n).carrier := by
          rwa [← hK n]
        calc
          ‖g z‖ ≤ polynomialSupNorm p (frontier (Omega n).carrier) := by
            dsimp only [g]
            exact
              norm_companionClosedExtension_le_of_boundaryPhaseTransform_radial
                (Omega n) p hkernel hphase hzclosure
          _ = polynomialSupNorm p (closure (Omega n).carrier) :=
            (polynomialSupNorm_closure_carrier_eq_frontier
              (Omega n) p hbounded).symm
          _ = polynomialSupNorm p (K n) := by rw [hK n]
      have hboundaryApprox : ∀ (j : ℕ) (t : ℝ),
          t ∈ Icc (0 : ℝ) (2 * Real.pi) →
          ‖Polynomial.eval ((Omega (n + 1)).boundaryParam t) (r j) -
            g ((Omega (n + 1)).boundaryParam t)‖ ≤
              1 / ((j : ℝ) + 1) := by
        intro j t _ht
        apply hr j
        rw [hK n]
        apply subset_closure
        apply hnest n
        apply frontier_subset_closure
        rw [← (Omega (n + 1)).boundaryParam_range]
        exact mem_range_self t
      have hlim :=
        tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
          A (Omega (n + 1)) g r (hOmega (n + 1)) hgcontInner
            (fun j => hCauchyP (r j) (n + 1)) hboundaryApprox
      have haux : crouzeixAuxiliaryOperator A (Omega (n + 1)) g =
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p := by
        dsimp only [g]
        exact
          crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
            A (Omega (n + 1)) (Omega n) p (hOmega (n + 1))
              (hmass (n + 1)) (hnest n)
      have hlim' : Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p)) := by
        simpa only [haux] using hlim
      apply exists_tendsto_polynomial_companions_of_uniform_approximation
        A (K n) (polynomialSupNorm p (K n))
          (polynomialSupNorm_nonneg p (K n)) g hgbound
          (crouzeixPolynomialAuxiliaryOperator A (Omega n) p) ?_ r ?_ hlim'
      · intro hm
        have hpzero : p = 0 :=
          polynomial_eq_zero_of_polynomialSupNorm_eq_zero p (hcompact n)
            ((Omega n).frontier_infinite.mono (by
              rw [hK n]
              exact frontier_subset_closure)) hm
        subst p
        calc
          crouzeixPolynomialAuxiliaryOperator A (Omega n) 0 =
              crouzeixPolynomialAuxiliaryOperator A (Omega n)
                (0 • (1 : Polynomial ℂ)) := by rw [zero_smul]
          _ = star (0 : ℂ) •
              crouzeixPolynomialAuxiliaryOperator A (Omega n) 1 :=
            crouzeixPolynomialAuxiliaryOperator_smul A (Omega n) 0 1
          _ = 0 := by simp only [star_zero, zero_smul]
      · intro j z hz
        exact hr j z hz

/-- Constant shifts reduce the approximation input in the strictly nested
assembly to positive-degree polynomials vanishing at zero. -/
theorem
    crouzeixPalencia_of_smoothExhaustion_support_nested_companion_radialZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hnest : ∀ n,
      closure (Omega (n + 1)).carrier ⊆ (Omega n).carrier)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1)) :
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
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    let c : ℂ := ⟪x, A x⟫_ℂ
    have hcW : c ∈ numericalRange A :=
      (mem_numericalRange A c).mpr ⟨x, hxnorm, rfl⟩
    have horiented : ∀ n, c ∈ (Omega n).carrier ∧ ∀ t : ℝ,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (c - (Omega n).boundaryParam t)).re ≤ 0 := by
      intro n
      refine ⟨hOmega n (subset_closure hcW), ?_⟩
      apply canonicalNormal_support_all_of_Ioc
      intro t ht
      exact hsupport n t ht c hcW
    have hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
        crouzeixScalarCauchyKernel (Omega n) z = 1 := by
      intro n
      exact crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
        (Omega n) c (horiented n).1 (horiented n).2
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_support_nested_scalarCompanion_approximation
        A Omega K hanti hcompact hnonempty hinter hK hOmega hsupport hnest
    intro p n
    by_cases hp : 0 < p.natDegree
    · let q := p - Polynomial.C (Polynomial.eval 0 p)
      have hqdegree : 0 < q.natDegree := by
        simpa only [q, Polynomial.natDegree_sub_C] using hp
      have hqzero : Polynomial.eval 0 q = 0 := by
        simp only [q, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
      have hqapprox := happrox q n hqdegree hqzero
      have hS : K n ⊆ closure (Omega n).carrier := by
        intro z hz
        simpa only [hK n] using hz
      have htransfer :=
        exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
          (Omega n) q (Polynomial.eval 0 p) (hkernel n)
          (K n) hS (fun j => 1 / ((j : ℝ) + 1)) hqapprox
      have hqadd : q + Polynomial.C (Polynomial.eval 0 p) = p := by
        dsimp only [q]
        abel
      rw [hqadd] at htransfer
      exact htransfer
    · have hpzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
      let a := p.coeff 0
      have hpC : p = Polynomial.C a :=
        Polynomial.eq_C_of_natDegree_eq_zero hpzero
      rw [hpC]
      refine ⟨fun _ => Polynomial.C (star a), ?_⟩
      intro j z hz
      have hzclosure : z ∈ closure (Omega n).carrier := by
        simpa only [hK n] using hz
      rw [Polynomial.eval_C,
        crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
          (Omega n) a (hkernel n) hzclosure,
        sub_self, norm_zero]
      positivity

/-- The canonical metric-thickening specialization of the strictly nested
scalar-companion assembly.  Identifying the smooth carriers with the explicit
open thickenings automatically supplies their adjacent closure nesting, while
the corresponding closed thickenings supply the compact antitone exhaustion.

Consequently no separate Plemelj identity, contour-mass identity, winding
normalization, or exhaustion data is required.  The remaining analytic input
is uniform polynomial approximation of positive-degree closed companions that
vanish at zero. -/
theorem
    crouzeixPalencia_of_thickening_support_nested_companion_radialZero
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
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1)) :
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
    have hcompact : IsCompact (closure (numericalRange A)) := by
      have hbounded : Bornology.IsBounded (numericalRange A) :=
        Metric.isBounded_closedBall.subset (fun z hz ↦ by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact norm_le_of_mem_numericalRange A hz)
      exact hbounded.isCompact_closure
    have hnonempty : (closure (numericalRange A)).Nonempty := by
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      exact ⟨⟪x, A x⟫_ℂ,
        subset_closure ((mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩)⟩
    obtain ⟨hanti, hstageCompact, hstageNonempty, hinter⟩ :=
      compactThickeningApprox_spec (closure (numericalRange A)) hcompact hnonempty
    apply
      crouzeixPalencia_of_smoothExhaustion_support_nested_companion_radialZero
        A Omega (compactThickeningApprox (closure (numericalRange A)))
          hanti hstageCompact hstageNonempty hinter
    · intro n
      rw [hcarrier n]
      unfold compactThickeningApprox convexThickeningApprox
      rw [closure_thickening]
      unfold smoothApproxRadius
      positivity
    · intro n
      rw [hcarrier n]
      apply Metric.self_subset_thickening
      unfold smoothApproxRadius
      positivity
    · exact hsupport
    · intro n
      rw [hcarrier (n + 1), hcarrier n]
      exact closure_convexThickeningApprox_succ_subset
        (closure (numericalRange A)) n
    · exact happrox

/-- A one-point orientation specialization of the canonical thickening
capstone.  At each stage it is enough to exhibit one point of the smooth
carrier whose canonical normal has the supporting sign at parameter zero.
Strict convexity and continuity propagate that single sign to the whole trace
and then to every point of the numerical range. -/
theorem
    crouzeixPalencia_of_thickening_pointOriented_nested_companion_radialZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (horientation : ∀ n, ∃ c ∈ (Omega n).carrier,
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam 0) *
        (c - (Omega n).boundaryParam 0)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeixPalencia_of_thickening_support_nested_companion_radialZero
      A Omega hcarrier
  · intro n t _ht w hw
    obtain ⟨c, hc, hc0⟩ := horientation n
    have hcside :=
      (Omega n).canonicalNormal_support_all_of_support_at c hc 0 hc0 t
    have hwcarrier : w ∈ (Omega n).carrier := by
      rw [hcarrier n]
      apply Metric.self_subset_thickening
      · unfold smoothApproxRadius
        positivity
      · exact subset_closure hw
    exact
      ((Omega n).closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t hcside).2 w hwcarrier |>.le
  · exact happrox

/-- The canonical-orientation specialization removes the final geometric
support premise from the metric-thickening capstone.  Any supplied smooth
realization is reoriented automatically; uniform approximation is required
only for the resulting canonically oriented closed scalar companions. -/
theorem
    crouzeixPalencia_of_thickening_canonical_nested_companion_radialZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n).canonicalOrientation p z‖ ≤
            1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeixPalencia_of_thickening_pointOriented_nested_companion_radialZero
      A (fun n ↦ (Omega n).canonicalOrientation)
  · intro n
    rw [SmoothJordanDomain.canonicalOrientation_carrier, hcarrier n]
  · exact fun n ↦ (Omega n).exists_oriented_point_canonicalOrientation
  · exact happrox

/-- Canonical orientation removes the numerical-range support premise from
the general strictly nested smooth-exhaustion assembly as well.  This version
does not require the carriers to be particular metric thickenings: compact
exhaustion, numerical-range containment, strict adjacent nesting, and uniform
approximation of the canonically oriented closed companions suffice. -/
theorem
    crouzeixPalencia_of_smoothExhaustion_canonical_nested_companion_radialZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hnest : ∀ n,
      closure (Omega (n + 1)).carrier ⊆ (Omega n).carrier)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n).canonicalOrientation p z‖ ≤
            1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeixPalencia_of_smoothExhaustion_support_nested_companion_radialZero
      A (fun n ↦ (Omega n).canonicalOrientation) K hanti hcompact hnonempty hinter
  · intro n
    rw [SmoothJordanDomain.canonicalOrientation_carrier]
    exact hK n
  · intro n
    simpa only [SmoothJordanDomain.canonicalOrientation_carrier] using hOmega n
  · intro n t _ht w hw
    obtain ⟨c, hc, hc0⟩ :=
      (Omega n).exists_oriented_point_canonicalOrientation
    have hcside :=
      (Omega n).canonicalOrientation.canonicalNormal_support_all_of_support_at
        c hc 0 hc0 t
    have hwcarrier : w ∈ (Omega n).canonicalOrientation.carrier := by
      rw [SmoothJordanDomain.canonicalOrientation_carrier]
      exact hOmega n (subset_closure hw)
    exact
      ((Omega n).canonicalOrientation.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t hcside).2 w hwcarrier |>.le
  · intro n
    simpa only [SmoothJordanDomain.canonicalOrientation_carrier] using hnest n
  · exact happrox

/-- Standard compact-uniform polynomial convergence is sufficient for the
canonically oriented nested-exhaustion capstone.  A subsequence realizes the
quantitative error schedule required by the preceding theorem. -/
theorem
    crouzeixPalencia_of_smoothExhaustion_canonical_nested_companion_uniformLimit_radialZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hnest : ∀ n,
      closure (Omega (n + 1)).carrier ⊆ (Omega n).carrier)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ q : ℕ → Polynomial ℂ,
        TendstoUniformlyOn
          (fun j z ↦ Polynomial.eval z (q j))
          (crouzeixPolynomialScalarCompanionClosedExtension
            (Omega n).canonicalOrientation p)
          atTop (K n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeixPalencia_of_smoothExhaustion_canonical_nested_companion_radialZero
      A Omega K hanti hcompact hnonempty hinter hK hOmega hnest
  intro p n hp hp0
  obtain ⟨q, hq⟩ := happrox p n hp hp0
  exact exists_polynomial_rate_approximation_of_tendstoUniformlyOn
    (K n)
    (crouzeixPolynomialScalarCompanionClosedExtension
      (Omega n).canonicalOrientation p) q hq

/-- Terminal bundled form of the verified Crouzeix--Palencia assembly.  A
strictly nested smooth Jordan exhaustion of the closed numerical range and
compact-uniform polynomial approximation of its canonically oriented closed
scalar companions imply the exact `1 + sqrt 2` spectral-set bound. -/
theorem
    crouzeixPalencia_of_nestedExhaustion_canonical_companion_uniformLimit_radialZero
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A)))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ q : ℕ → Polynomial ℂ,
        TendstoUniformlyOn
          (fun j z ↦ Polynomial.eval z (q j))
          (crouzeixPolynomialScalarCompanionClosedExtension
            (Omega.domain n).canonicalOrientation p)
          atTop (closure (Omega.domain n).carrier)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : ℕ → Set ℂ := fun n ↦ closure (Omega.domain n).carrier
  have hanti : Antitone K := by
    apply antitone_nat_of_succ_le
    intro n
    exact (Omega.closure_succ_subset n).trans subset_closure
  have hnonempty : ∀ n, (K n).Nonempty := fun n ↦
    (Omega.domain n).carrier_nonempty.mono subset_closure
  apply
    crouzeixPalencia_of_smoothExhaustion_canonical_nested_companion_uniformLimit_radialZero
      A Omega.domain K hanti Omega.isCompact_closure hnonempty
        Omega.iInter_closure (fun _ ↦ rfl) Omega.target_subset
          Omega.closure_succ_subset
  exact happrox

/-- Textbook terminal criterion: a strictly nested smooth exhaustion whose
canonically oriented stages satisfy the Mergelyan polynomial approximation
property yields the exact Crouzeix--Palencia bound.  The regularity theorem
above applies that property automatically to every closed scalar companion. -/
theorem
    crouzeixPalencia_of_nestedExhaustion_canonical_mergelyanApproximation
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A)))
    (hmergelyan : ∀ n,
      (Omega.domain n).HasMergelyanPolynomialApproximation) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeixPalencia_of_nestedExhaustion_canonical_companion_uniformLimit_radialZero
      A Omega
  intro p n _hp _hp0
  have hcanonical :
      (Omega.domain n).canonicalOrientation.HasMergelyanPolynomialApproximation :=
    (SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
      (Omega.domain n)).mpr (hmergelyan n)
  simpa only [SmoothJordanDomain.canonicalOrientation_carrier] using
    hcanonical _ (Omega.diffContOnCl_canonicalScalarCompanion p n)

/-- Textbook explicit-thickening criterion: if the explicit metric
thickenings of the closed numerical range admit smooth Jordan realizations
with the Mergelyan polynomial approximation property, then the exact
Crouzeix--Palencia bound follows. -/
theorem crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hmergelyan : ∀ n,
      (Omega n).HasMergelyanPolynomialApproximation) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hcompact : IsCompact (closure (numericalRange A)) := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    exact hbounded.isCompact_closure
  let exhaustion :=
    StrictNestedSmoothJordanExhaustion.ofConvexThickening
      (closure (numericalRange A)) hcompact Omega hcarrier
  apply
    crouzeixPalencia_of_nestedExhaustion_canonical_mergelyanApproximation
      A exhaustion
  intro n
  change (Omega n).HasMergelyanPolynomialApproximation
  exact hmergelyan n

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
