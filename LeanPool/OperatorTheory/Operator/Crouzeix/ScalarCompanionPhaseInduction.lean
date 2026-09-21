/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionAssembly

/-!
# Induction through boundary-phase divided differences

At a frontier point `xi`, the sharp scalar-companion boundary estimate for a
polynomial `p` contains the phase transform of
`p /ₘ (X - C xi)`.  This quotient has strictly smaller degree whenever `p`
has positive degree, but it depends on `xi`.  Consequently the appropriate
recursive invariant branches over every frontier point rather than following
one fixed remainder polynomial.

This file packages that branching strong induction.  The degree-zero base is
already sharp because the divided difference vanishes.  The resulting L4.2
connector leaves only a cancellation-preserving divided-difference-to-parent
phase step as its phase hypothesis.

## Main declarations

* `CrouzeixBoundaryPhaseContractive` -- the exact sharp frontier invariant;
* `polynomial_induction_on_boundaryPhaseDividedDifferences` -- branching
  strong induction through all frontier-dependent quotients;
* `crouzeixBoundaryPhaseContractive_of_dividedDifference_induction` -- the
  invariant with its degree-zero base discharged;
* `crouzeixBoundaryPhaseContractive_of_normalized` -- reduction to
  positive-degree polynomials of unit frontier sup norm;
* `crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction`
  -- the L4.2 assembly from the remaining positive-degree phase step.
-/

open Complex Filter Set
open scoped InnerProductSpace Interval Real

universe u

/-- The sharp boundary invariant for the scalar Crouzeix companion: at every
frontier point, the conjugate point value plus the lower-degree phase contour
is bounded by the polynomial frontier sup norm. -/
def CrouzeixBoundaryPhaseContractive
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : Prop :=
  ∀ xi ∈ frontier Omega.carrier,
    ‖star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
      polynomialSupNorm p (frontier Omega.carrier)

/-- Every smooth Jordan frontier is infinite.  The boundary parametrization
is injective on the infinite half-open fundamental interval, whose image lies
in its full range. -/
theorem SmoothJordanDomain.frontier_infinite (Omega : SmoothJordanDomain) :
    (frontier Omega.carrier).Infinite := by
  rw [← Omega.boundaryParam_range]
  have himage :
      (Omega.boundaryParam '' Ico (0 : ℝ) (2 * Real.pi)).Infinite :=
    (Ico_infinite Real.two_pi_pos).image Omega.boundaryParam_injOn
  exact himage.mono (image_subset_range _ _)

/-- Phase contractivity is preserved by polynomial scaling.  Both the
boundary value and the frontier sup norm scale by the norm of the scalar. -/
theorem crouzeixBoundaryPhaseContractive_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hp : CrouzeixBoundaryPhaseContractive Omega p) :
    CrouzeixBoundaryPhaseContractive Omega (a • p) := by
  intro xi hxi
  have hpbound :
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
        polynomialSupNorm p (frontier Omega.carrier) := by
    rw [
      crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
    exact hp xi hxi
  rw [←
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform,
    crouzeixPolynomialScalarCompanionBoundaryValue_smul,
    norm_mul, norm_star, polynomialSupNorm_smul]
  exact mul_le_mul_of_nonneg_left hpbound (norm_nonneg a)

/-- Scaling by a nonzero scalar preserves and reflects phase contractivity. -/
theorem crouzeixBoundaryPhaseContractive_smul_iff
    (Omega : SmoothJordanDomain) {a : ℂ} (ha : a ≠ 0)
    (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive Omega (a • p) ↔
      CrouzeixBoundaryPhaseContractive Omega p := by
  constructor
  · intro h
    have hscaled := crouzeixBoundaryPhaseContractive_smul
      Omega a⁻¹ (a • p) h
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hscaled
  · exact crouzeixBoundaryPhaseContractive_smul Omega a p

/-- A branching strong-induction principle for the family of divided
differences indexed by the frontier.  Every quotient used in the positive
degree step is strictly lower-degree. -/
theorem polynomial_induction_on_boundaryPhaseDividedDifferences
    (Omega : SmoothJordanDomain) (P : Polynomial ℂ → Prop)
    (hzero : ∀ p, p.natDegree = 0 → P p)
    (hstep : ∀ p, 0 < p.natDegree →
      (∀ xi ∈ frontier Omega.carrier,
        P (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      P p) :
    ∀ p, P p := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp : p.natDegree = 0
      · exact hzero p hp
      · apply hstep p (Nat.pos_of_ne_zero hp)
        intro xi _hxi
        apply ih
          (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree
        · simpa only [← hn] using
            natDegree_divByMonic_X_sub_C_lt p xi
              (Nat.pos_of_ne_zero hp)
        · rfl

/-- Constant polynomials satisfy the sharp boundary-phase invariant. -/
theorem crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hp : p.natDegree = 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  intro xi _hxi
  exact
    norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero
      Omega p hp xi

/-- To establish sharp boundary-phase contractivity for every polynomial, it
suffices to propagate it from all frontier-indexed divided differences to a
positive-degree parent polynomial.  The degree-zero base is automatic. -/
theorem
    crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
    (Omega : SmoothJordanDomain)
    (hstep : ∀ p, 0 < p.natDegree →
      (∀ xi ∈ frontier Omega.carrier,
        CrouzeixBoundaryPhaseContractive Omega
          (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      CrouzeixBoundaryPhaseContractive Omega p) :
    ∀ p, CrouzeixBoundaryPhaseContractive Omega p := by
  apply polynomial_induction_on_boundaryPhaseDividedDifferences Omega
  · exact crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero Omega
  · exact hstep

/-- On the infinite compact frontier of a smooth Jordan domain, it suffices
to prove phase contractivity for positive-degree polynomials normalized to
frontier sup norm one.  Exact conjugate homogeneity restores every nonzero
scale, while the degree-zero case is automatic. -/
theorem crouzeixBoundaryPhaseContractive_of_normalized
    (Omega : SmoothJordanDomain)
    (hnormalized : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      polynomialSupNorm p (frontier Omega.carrier) = 1 →
      CrouzeixBoundaryPhaseContractive Omega p) :
    ∀ p, CrouzeixBoundaryPhaseContractive Omega p := by
  intro p
  by_cases hpzero : p.natDegree = 0
  · exact crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
      Omega p hpzero
  have hp : 0 < p.natDegree := Nat.pos_of_ne_zero hpzero
  let m := polynomialSupNorm p (frontier Omega.carrier)
  have hm0 : m ≠ 0 := by
    intro hm
    have hpzero' : p = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero p
        Omega.isCompact_frontier Omega.frontier_infinite hm
    subst p
    simp only [Polynomial.natDegree_zero, lt_self_iff_false] at hp
  have hm : 0 < m :=
    lt_of_le_of_ne (polynomialSupNorm_nonneg p _) (Ne.symm hm0)
  let q : Polynomial ℂ := ((m : ℂ)⁻¹) • p
  have hscalar : ((m : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hm0)
  have hqdegree : 0 < q.natDegree := by
    dsimp only [q]
    rw [Polynomial.natDegree_smul p hscalar]
    exact hp
  have hqnorm : polynomialSupNorm q (frontier Omega.carrier) = 1 := by
    dsimp only [q]
    rw [polynomialSupNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    exact inv_mul_cancel₀ hm0
  have hq := hnormalized q hqdegree hqnorm
  have hscaled := crouzeixBoundaryPhaseContractive_smul
    Omega (m : ℂ) q hq
  have hpq : (m : ℂ) • q = p := by
    dsimp only [q]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm0),
      one_smul]
  rw [hpq] at hscaled
  exact hscaled

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The smooth-thickening scalar-companion route needs only a
cancellation-preserving positive-degree induction step for the sharp phase
invariant.  Branching divided-difference induction supplies all-polynomial
phase contractivity, after which the Plemelj assembly and fourth-power
bootstrap give the exact Crouzeix--Palencia conclusion. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction
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
    (hreg : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized (Omega n) p xi)
        (nhdsWithin xi (Omega n).carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized
            (Omega n) p xi xi)))
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
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
      A Omega hcarrier hCauchyP hsupport hkernel hreg
  · intro p n xi hxi
    exact
      (crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
        (Omega n) (hphaseStep n) p) xi hxi
  · exact happrox
  · exact hPlemelj

/-- Equivalently, the smooth-thickening scalar-companion route only needs the
sharp phase theorem for positive-degree polynomials normalized to frontier
sup norm one at each stage.  Infinite-frontier normalization supplies all
other scales and the constant case. -/
theorem
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase
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
    (hreg : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized (Omega n) p xi)
        (nhdsWithin xi (Omega n).carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized
            (Omega n) p xi xi)))
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
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
      A Omega hcarrier hCauchyP hsupport hkernel hreg
  · intro p n xi hxi
    exact
      (crouzeixBoundaryPhaseContractive_of_normalized
        (Omega n) (hphaseNormalized n) p) xi hxi
  · exact happrox
  · exact hPlemelj

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
