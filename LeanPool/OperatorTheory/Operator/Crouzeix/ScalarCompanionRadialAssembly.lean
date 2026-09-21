/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionAssembly
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPhaseInduction
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionRadial

/-!
# L4.2 assembly with automatic scalar Plemelj convergence

Radial regularization on bounded smooth Jordan carriers supplies the full
frontier convergence previously threaded through the scalar-companion
assembly as an analytic hypothesis.  This file removes that hypothesis from
the one-domain companion package and from the smooth-thickening L4.2
capstone.

The remaining inputs are the genuinely sharp phase contraction, polynomial
approximation, and reproduction of the polynomial auxiliary contour.
-/

open Complex Filter Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- On a winding-normalized smooth domain, exterior decay and radial geometry
automatically supply boundedness and the convergence needed by the canonical
phase-controlled scalar companion. -/
theorem
    exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform_radial
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
      ‖Polynomial.eval z (r j) -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
        1 / ((j : ℝ) + 1))
    (hPlemelj :
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) :
    ∃ (g : ℂ → ℂ) (q : ℕ → Polynomial ℂ),
      ContinuousOn g
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ closure Omega.carrier,
        ‖g z‖ ≤ polynomialSupNorm p (closure Omega.carrier)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
        ‖Polynomial.eval z (q j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A Omega g =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  have hbounded : Bornology.IsBounded Omega.carrier :=
    Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel
  refine ⟨
    crouzeixPolynomialScalarCompanionClosedExtension Omega p,
    r, ?_, ?_, happrox, hPlemelj⟩
  · apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
        Omega p hbounded hkernel).mono
    rintro z ⟨t, _ht, rfl⟩
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  · intro z hz
    calc
      ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          polynomialSupNorm p (frontier Omega.carrier) :=
        norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
          Omega p hkernel hphase hz
      _ = polynomialSupNorm p (closure Omega.carrier) :=
        (polynomialSupNorm_closure_carrier_eq_frontier
          Omega p hbounded).symm

omit [CompleteSpace E] in
/-- Auxiliary contours depend only on the scalar datum along the chosen
boundary parametrization. -/
theorem crouzeixAuxiliaryOperator_congr_boundaryParam
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      f (Omega.boundaryParam t) = g (Omega.boundaryParam t)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by
  unfold crouzeixAuxiliaryOperator
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le Real.two_pi_pos.le] at ht
  change deriv Omega.boundaryParam t •
      (f (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t)) =
    deriv Omega.boundaryParam t •
      (g (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t))
  rw [hfg t ht]

omit [CompleteSpace E] in
/-- In particular, equality on the geometric frontier determines the
auxiliary contour. -/
theorem crouzeixAuxiliaryOperator_congr_frontier
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : Set.EqOn f g (frontier Omega.carrier)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by
  apply crouzeixAuxiliaryOperator_congr_boundaryParam
  intro t _ht
  apply hfg
  rw [← Omega.boundaryParam_range]
  exact mem_range_self t

omit [CompleteSpace E] in
/-- Equality on the carrier closure is therefore also sufficient. -/
theorem crouzeixAuxiliaryOperator_congr_closure
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : Set.EqOn f g (closure Omega.carrier)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by
  apply crouzeixAuxiliaryOperator_congr_frontier
  exact hfg.mono frontier_subset_closure

omit [CompleteSpace E] in
/-- Scaling a polynomial conjugate-scales the auxiliary contour of its
canonical closed companion. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p)) =
      star a • crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Omega p) := by
  calc
    crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p)) =
        crouzeixAuxiliaryOperator A Omega
          (fun z => star a •
            crouzeixPolynomialScalarCompanionClosedExtension Omega p z) := by
      apply crouzeixAuxiliaryOperator_congr_frontier
      intro z hz
      change crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
        star a • crouzeixPolynomialScalarCompanionClosedExtension Omega p z
      rw [smul_eq_mul,
        crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
          Omega a p hkernel (frontier_subset_closure hz)]
    _ = star a • crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) :=
      crouzeixAuxiliaryOperator_smul A Omega (star a)
        (crouzeixPolynomialScalarCompanionClosedExtension Omega p)

omit [CompleteSpace E] in
/-- For a nonzero scalar, companion-contour reproduction is preserved and
reflected by polynomial scaling. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    {a : ℂ} (ha : a ≠ 0) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p)) =
        crouzeixPolynomialAuxiliaryOperator A Omega (a • p)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  rw [
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
      A Omega a p hkernel,
    crouzeixPolynomialAuxiliaryOperator_smul]
  constructor
  · intro h
    have h' := congrArg
      (fun T : E →L[ℂ] E => (star a)⁻¹ • T) h
    simpa only [smul_smul, inv_mul_cancel₀ (star_ne_zero.mpr ha), one_smul]
      using h'
  · intro h
    exact congrArg (fun T : E →L[ℂ] E => star a • T) h

/-- Adding a constant polynomial shifts the canonical companion contour by
exactly the constant-polynomial auxiliary operator. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a)) =
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) +
        crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by
  let g := crouzeixPolynomialScalarCompanionClosedExtension Omega p
  have hgcont : ContinuousOn g
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
    apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
        Omega p hkernel).mono
    rintro z ⟨t, _ht, rfl⟩
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hgint :=
    crouzeixAuxiliaryIntegrand_contourIntegrable A Omega g hOmega hgcont
  have haint :=
    crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
      A Omega (Polynomial.C a) hOmega
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  rw [← smul_add, ← contourIntegral_add hgint haint]
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  change deriv Omega.boundaryParam t •
      (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a) (Omega.boundaryParam t) •
        resolvent A (Omega.boundaryParam t)) =
    deriv Omega.boundaryParam t •
      ((g (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t)) +
        (star (Polynomial.eval (Omega.boundaryParam t) (Polynomial.C a)) •
          resolvent A (Omega.boundaryParam t)))
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
      Omega p a
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel (frontier_subset_closure hfrontier)]
  simp only [g, Polynomial.eval_C, add_smul, smul_add]

/-- The companion-contour reproduction identity is invariant under adding a
constant polynomial.  It may therefore be checked after any convenient
constant normalization of `p`. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension
            Omega (p + Polynomial.C a)) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (p + Polynomial.C a)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  rw [
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
      A Omega p a hOmega hkernel,
    crouzeixPolynomialAuxiliaryOperator_add
      A Omega p (Polynomial.C a) hOmega]
  constructor
  · intro h
    exact add_right_cancel h
  · intro h
    exact congrArg
      (fun T : E →L[ℂ] E =>
        T + crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a)) h

/-- The auxiliary contour of the canonical companion satisfies the full
conjugate-affine law. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (a b : ℂ) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (a • p + Polynomial.C b)) =
      star a • crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) +
        crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C b) := by
  rw [
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_of_cauchyKernel_eq_one
      A Omega (a • p) b hOmega hkernel,
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
      A Omega a p hkernel]

/-- Reproduction is invariant under the full nondegenerate affine action on
the source polynomial. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_affine_eq_iff
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension
            Omega (a • p + Polynomial.C b)) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (a • p + Polynomial.C b)) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  exact
    (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
      A Omega (a • p) b hOmega hkernel).trans
        (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
          A Omega ha p hkernel)

/-- In particular, contour reproduction for `p` is equivalent to contour
reproduction after normalizing its value at zero to vanish. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_eq_iff_sub_C_eval_zero
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega
            (p - Polynomial.C (Polynomial.eval 0 p))) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (p - Polynomial.C (Polynomial.eval 0 p)) := by
  let q := p - Polynomial.C (Polynomial.eval 0 p)
  have h :=
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_add_C_eq_iff
      A Omega q (Polynomial.eval 0 p) hOmega hkernel
  have hq : q + Polynomial.C (Polynomial.eval 0 p) = p := by
    dsimp only [q]
    abel
  rw [hq] at h
  exact h

/-- Constant shifts, nonzero scaling, and the automatic constant case reduce
companion-contour reproduction to positive-degree polynomials that vanish at
zero and have frontier sup norm one. -/
theorem
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hnormalized : ∀ p : Polynomial ℂ,
      0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier Omega.carrier) = 1 →
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) :
    ∀ p : Polynomial ℂ,
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  intro p
  by_cases hpzero : p.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hpzero]
    exact
      crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
        A Omega (p.coeff 0) hkernel
  have hp : 0 < p.natDegree := Nat.pos_of_ne_zero hpzero
  let q := p - Polynomial.C (Polynomial.eval 0 p)
  have hqdegree : 0 < q.natDegree := by
    simpa only [q, Polynomial.natDegree_sub_C] using hp
  have hqeval : Polynomial.eval 0 q = 0 := by
    simp only [q, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
  let m := polynomialSupNorm q (frontier Omega.carrier)
  have hm0 : m ≠ 0 := by
    intro hm
    have hqzero : q = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero q
        Omega.isCompact_frontier Omega.frontier_infinite hm
    have hpC : p = Polynomial.C (Polynomial.eval 0 p) := by
      apply sub_eq_zero.mp
      simpa only [q] using hqzero
    apply hpzero
    rw [hpC, Polynomial.natDegree_C]
  have hm : 0 < m :=
    lt_of_le_of_ne (polynomialSupNorm_nonneg q _) (Ne.symm hm0)
  let r : Polynomial ℂ := ((m : ℂ)⁻¹) • q
  have hrdegree : 0 < r.natDegree := by
    dsimp only [r]
    rw [Polynomial.natDegree_smul q
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr hm0))]
    exact hqdegree
  have hreval : Polynomial.eval 0 r = 0 := by
    simp only [r, Polynomial.eval_smul, hqeval, smul_zero]
  have hrnorm : polynomialSupNorm r (frontier Omega.carrier) = 1 := by
    dsimp only [r]
    rw [polynomialSupNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    exact inv_mul_cancel₀ hm0
  have hr := hnormalized r hrdegree hreval hrnorm
  have hmcomplex : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm0
  have hmq : (m : ℂ) • r = q := by
    dsimp only [r]
    rw [smul_smul, mul_inv_cancel₀ hmcomplex, one_smul]
  have hq :
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega q) =
        crouzeixPolynomialAuxiliaryOperator A Omega q := by
    have hscaled :=
      (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
        A Omega hmcomplex r hkernel).2 hr
    rwa [hmq] at hscaled
  exact
    (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_eq_iff_sub_C_eval_zero
      A Omega p hOmega hkernel).2 hq

/-- The smooth-thickening scalar-companion capstone no longer assumes
regularized frontier convergence: boundedness of each compact stage and the
radial Plemelj theorem prove it internally. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_approximation
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
    (hphase : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform (Omega n) xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier (Omega n).carrier))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro p n xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
        (Omega n) p (hkernel n) hxi
  · exact hphase
  · exact happrox
  · exact hPlemelj

/-- Constant companions and their auxiliary contours are automatic, so the
approximation and contour-reproduction inputs need only be supplied for
positive-degree polynomials. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_positiveDegree
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
    (hphase : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform (Omega n) xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier (Omega n).carrier))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : Set ℂ := closure (numericalRange A)
  have hclosure : ∀ n,
      closure (Omega n).carrier = compactThickeningApprox K n := by
    intro n
    rw [hcarrier n]
    unfold convexThickeningApprox compactThickeningApprox
    exact closure_thickening (by
      unfold smoothApproxRadius
      positivity) K
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_approximation
      A Omega hcarrier hCauchyP hsupport hkernel hphase
  · intro p n
    by_cases hp : 0 < p.natDegree
    · exact happrox p n hp
    · have hpzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
      let a := p.coeff 0
      have hpC : p = Polynomial.C a :=
        Polynomial.eq_C_of_natDegree_eq_zero hpzero
      rw [hpC]
      refine ⟨fun _ => Polynomial.C (star a), ?_⟩
      intro j z hz
      have hzclosure : z ∈ closure (Omega n).carrier := by
        rw [hclosure n]
        simpa only [K] using hz
      rw [Polynomial.eval_C,
        crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
          (Omega n) a (hkernel n) hzclosure,
        sub_self, norm_zero]
      positivity
  · intro p n
    by_cases hp : 0 < p.natDegree
    · exact hPlemelj p n hp
    · have hpzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
      let a := p.coeff 0
      have hpC : p = Polynomial.C a :=
        Polynomial.eq_C_of_natDegree_eq_zero hpzero
      rw [hpC]
      exact
        crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
          A (Omega n) a (hkernel n)

/-- Automatic radial Plemelj convergence leaves only the strict-degree
divided-difference induction step for the sharp boundary-phase invariant. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction_radial
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
    (hphaseStep : ∀ (n : ℕ) (p : Polynomial ℂ), 0 < p.natDegree →
      (∀ xi ∈ frontier (Omega n).carrier,
        CrouzeixBoundaryPhaseContractive (Omega n)
          (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_approximation
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro p n xi hxi
    exact
      (crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
        (Omega n) (hphaseStep n) p) xi hxi
  · exact happrox
  · exact hPlemelj

/-- Combining radial Plemelj convergence, the automatic constant case, and
strict degree descent reduces every remaining companion input to positive
degree. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction_radial_positiveDegree
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
    (hphaseStep : ∀ (n : ℕ) (p : Polynomial ℂ), 0 < p.natDegree →
      (∀ xi ∈ frontier (Omega n).carrier,
        CrouzeixBoundaryPhaseContractive (Omega n)
          (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_positiveDegree
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro p n xi hxi
    exact
      (crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
        (Omega n) (hphaseStep n) p) xi hxi
  · exact happrox
  · exact hPlemelj

/-- After automatic radial convergence and the constant case, every remaining
phase, approximation, and contour-reproduction input is restricted to
positive-degree polynomials; the phase input may moreover be normalized to
frontier sup norm one. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_positiveDegree
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
    (hphaseNormalized : ∀ (n : ℕ) (p : Polynomial ℂ),
      0 < p.natDegree →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_positiveDegree
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro p n xi hxi
    exact
      (crouzeixBoundaryPhaseContractive_of_normalized
        (Omega n) (hphaseNormalized n) p) xi hxi
  · exact happrox
  · exact hPlemelj

/-- Constant-shift invariance reduces approximation to positive-degree
polynomials vanishing at zero.  Scaling invariance further restricts contour
reproduction to that subclass at frontier sup norm one; the sharp phase input
is likewise normalized to frontier sup norm one. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_vanishingAtZero
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
    (hphaseNormalized : ∀ (n : ℕ) (p : Polynomial ℂ),
      0 < p.natDegree →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
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
  let K : Set ℂ := closure (numericalRange A)
  have hclosure : ∀ n,
      closure (Omega n).carrier = compactThickeningApprox K n := by
    intro n
    rw [hcarrier n]
    unfold convexThickeningApprox compactThickeningApprox
    exact closure_thickening (by
      unfold smoothApproxRadius
      positivity) K
  have hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier := by
    intro n
    rw [hcarrier n]
    unfold convexThickeningApprox
    exact Metric.self_subset_thickening (by
      unfold smoothApproxRadius
      positivity) _
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_positiveDegree
      A Omega hcarrier hCauchyP hsupport hkernel hphaseNormalized
  · intro p n hp
    let q := p - Polynomial.C (Polynomial.eval 0 p)
    have hqdegree : 0 < q.natDegree := by
      simpa only [q, Polynomial.natDegree_sub_C] using hp
    have hqzero : Polynomial.eval 0 q = 0 := by
      simp only [q, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
    have hqapprox := happrox q n hqdegree hqzero
    have hS : compactThickeningApprox (closure (numericalRange A)) n ⊆
        closure (Omega n).carrier := by
      rw [hclosure n]
    have htransfer :=
      exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
        (Omega n) q (Polynomial.eval 0 p) (hkernel n)
        (compactThickeningApprox (closure (numericalRange A)) n) hS
        (fun j => 1 / ((j : ℝ) + 1)) hqapprox
    have hqadd : q + Polynomial.C (Polynomial.eval 0 p) = p := by
      dsimp only [q]
      abel
    rw [hqadd] at htransfer
    exact htransfer
  · intro p n _hp
    exact
      crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
        A (Omega n) (hOmega n) (hkernel n)
          (fun q hq hqzero hqnorm => hPlemelj q n hq hqzero hqnorm) p

/-- After automatic radial Plemelj convergence and scalar normalization, the
L4.2 route needs the sharp phase theorem only for positive-degree
frontier-sup-norm-one polynomials. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial
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
    (hphaseNormalized : ∀ (n : ℕ) (p : Polynomial ℂ),
      0 < p.natDegree →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_positiveDegree
      A Omega hcarrier hCauchyP hsupport hkernel
  · exact hphaseNormalized
  · intro p n _hp
    exact happrox p n
  · intro p n _hp
    exact hPlemelj p n

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
