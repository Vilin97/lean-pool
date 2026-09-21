/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ChartArcAnnihilation
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localized transition between projective affine charts

The coordinate ring of the overlap between the zeroth affine chart and a
chosen chart is obtained by inverting the chosen-chart coordinate representing
`X₀ / X_chart`.  This file constructs the resulting transition homomorphism.
-/

namespace Stafford38.Geometry.LocalizedProjectiveChartTransition

open Stafford38.Geometry.AsymptoticChartArcAdapter
open Stafford38.Geometry.ChartArcAnnihilation
open Stafford38.Geometry.ProjectiveEquationFormalChart

noncomputable section

universe u

variable {K : Type u} [Field K]

/-! ## Zeroth-chart homogenization -/

/-- Homogenize an affine polynomial in the zeroth projective coordinate by
padding each homogeneous component to the total degree of the polynomial. -/
def homogenizeAtZero {m : ℕ} (f : MvPolynomial (Fin m) K) :
    MvPolynomial (Fin (m + 1)) K :=
  ∑ i ∈ Finset.range (f.totalDegree + 1),
    MvPolynomial.X 0 ^ (f.totalDegree - i) *
      MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i f)

/-- The explicit homogenization is homogeneous of the expected degree. -/
theorem homogenizeAtZero_isHomogeneous {m : ℕ}
    (f : MvPolynomial (Fin m) K) :
    (homogenizeAtZero f).IsHomogeneous f.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hi_le : i ≤ f.totalDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpow := MvPolynomial.isHomogeneous_X_pow
    (R := K) (0 : Fin (m + 1)) (f.totalDegree - i)
  have hcomponent :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i f).rename_isHomogeneous
      (f := Fin.succ)
  convert hpow.mul hcomponent using 1
  omega

/-- Dehomogenizing the constructed projective polynomial in chart zero
recovers the original affine polynomial exactly. -/
theorem projectiveDehomogenize_homogenizeAtZero {m : ℕ}
    (f : MvPolynomial (Fin m) K) :
    Stafford38.Geometry.ProjectiveEquationFormalChart.projectiveDehomogenize
        (homogenizeAtZero f) = f := by
  rw [homogenizeAtZero]
  simp only [map_sum, map_mul, map_pow]
  have hcomponent : ∀ i,
      projectiveDehomogenize
          (MvPolynomial.rename Fin.succ
            (MvPolynomial.homogeneousComponent i f)) =
        MvPolynomial.homogeneousComponent i f := by
    intro i
    rw [show projectiveDehomogenize
        (MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i f)) =
      MvPolynomial.bind₁ (Fin.cases 1 fun j ↦ MvPolynomial.X j)
        (MvPolynomial.rename Fin.succ
          (MvPolynomial.homogeneousComponent i f)) by rfl]
    rw [MvPolynomial.bind₁_rename]
    have hfun :
        ((fun a : Fin (m + 1) ↦
            Fin.cases 1 (fun j ↦ MvPolynomial.X (R := K) j) a) ∘
            Fin.succ) = MvPolynomial.X (R := K) := by
      funext j
      simp
    rw [hfun, MvPolynomial.bind₁_X_left]
    rfl
  simp_rw [hcomponent]
  simp [projectiveDehomogenize]
  exact MvPolynomial.sum_homogeneousComponent f

/-- Every affine ideal over a field has a finite homogeneous projective
equation family whose zeroth-chart dehomogenized ideal is exactly the given
ideal.  This is the algebraic homogenization step; it does not assert that the
resulting homogeneous ideal is saturated. -/
theorem exists_finite_homogeneous_equations_dehomogenizing_to
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) K)) :
    ∃ (n : ℕ) (equations : Fin n → MvPolynomial (Fin (m + 1)) K)
        (degree : Fin n → ℕ),
      (∀ j, (equations j).IsHomogeneous (degree j)) ∧
      dehomogenizedEquationIdeal equations = I := by
  obtain ⟨n, generators, hgenerators⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (I : Submodule _ _))
  refine ⟨n, fun j ↦ homogenizeAtZero (generators j),
    fun j ↦ (generators j).totalDegree, ?_, ?_⟩
  · intro j
    exact homogenizeAtZero_isHomogeneous (generators j)
  · rw [dehomogenizedEquationIdeal]
    simp_rw [projectiveDehomogenize_homogenizeAtZero]
    change Submodule.span _ (Set.range generators) = (I : Submodule _ _)
    exact hgenerators

/-- The projective coordinate `X_a/X_chart`, represented in the polynomial
coordinate ring of the chosen affine chart. -/
def chartProjectiveCoordinate {m : ℕ} (chart a : Fin (m + 1)) :
    MvPolynomial (Fin m) K :=
  if h : a = chart then 1
  else MvPolynomial.X ((chartAffineCoordinateEquiv chart).symm ⟨a, h⟩)

/-- The chosen-chart polynomial representing `X₀/X_chart`. -/
def chartOverlapDenominator {m : ℕ} (chart : Fin (m + 1)) :
    MvPolynomial (Fin m) K :=
  chartProjectiveCoordinate chart 0

/-- Coordinate ring of the overlap of the zeroth and chosen projective
affine charts. -/
abbrev ChartOverlapRing {m : ℕ} (chart : Fin (m + 1)) :=
  Localization.Away (chartOverlapDenominator (K := K) chart)

/-- The regular chart transition on the overlap.  The old zeroth-chart
coordinate `X_(i+1)/X₀` becomes
`(X_(i+1)/X_chart) / (X₀/X_chart)`. -/
def chartZeroToChosenOverlap {m : ℕ} (chart : Fin (m + 1)) :
    MvPolynomial (Fin m) K →+* ChartOverlapRing (K := K) chart :=
  MvPolynomial.eval₂Hom
    (algebraMap K (ChartOverlapRing (K := K) chart))
    (fun i ↦
      algebraMap (MvPolynomial (Fin m) K)
          (ChartOverlapRing (K := K) chart)
          (chartProjectiveCoordinate chart i.succ) *
        IsLocalization.Away.invSelf
          (chartOverlapDenominator (K := K) chart))

theorem chartZeroToChosenOverlap_X {m : ℕ} (chart : Fin (m + 1))
    (i : Fin m) :
    chartZeroToChosenOverlap (K := K) chart (MvPolynomial.X i) =
      algebraMap (MvPolynomial (Fin m) K)
          (ChartOverlapRing (K := K) chart)
          (chartProjectiveCoordinate chart i.succ) *
        IsLocalization.Away.invSelf
          (chartOverlapDenominator (K := K) chart) := by
  simp [chartZeroToChosenOverlap]

theorem chartOverlapDenominator_mul_invSelf {m : ℕ}
    (chart : Fin (m + 1)) :
    algebraMap (MvPolynomial (Fin m) K)
        (ChartOverlapRing (K := K) chart)
        (chartOverlapDenominator (K := K) chart) *
      IsLocalization.Away.invSelf
        (chartOverlapDenominator (K := K) chart) = 1 := by
  exact IsLocalization.Away.mul_invSelf _

/-! ## Homogeneous scaling without division -/

/-- If `s * r = 1`, scaling every coordinate by `r` scales a homogeneous
polynomial of degree `d` by `s⁻ᵈ` in the cancellation-free form displayed
below.  This version works in the overlap localization, which need not be a
field. -/
theorem eval_eq_pow_mul_eval_mul_of_homogeneous
    {R : Type*} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ)
    (hp : p.IsHomogeneous d) (q : Fin n → R) (s r : R)
    (hsr : s * r = 1) :
    MvPolynomial.eval q p =
      s ^ d * MvPolynomial.eval (fun i ↦ r * q i) p := by
  change p.eval₂ (RingHom.id R) q =
    s ^ d * p.eval₂ (RingHom.id R) (fun i ↦ r * q i)
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  have hdegree : ∑ i, exponent i = d := by
    have hweight := hp (MvPolynomial.mem_support_iff.mp hexponent)
    rw [Finsupp.weight_apply,
      Finsupp.sum_fintype exponent
        (fun i c ↦ c • (1 : Fin n → ℕ) i) (by simp)] at hweight
    simpa only [Pi.one_apply, smul_eq_mul, mul_one] using hweight
  have hcoordinate : ∀ i : Fin n, s * (r * q i) = q i := by
    intro i
    rw [← mul_assoc, hsr, one_mul]
  have hproduct : (∏ i : Fin n, q i ^ exponent i) =
      s ^ d * ∏ i : Fin n, (r * q i) ^ exponent i := by
    calc
      (∏ i : Fin n, q i ^ exponent i) =
          ∏ i : Fin n, (s * (r * q i)) ^ exponent i := by
            simp_rw [hcoordinate]
      _ = (∏ i : Fin n, s ^ exponent i) *
          ∏ i : Fin n, (r * q i) ^ exponent i := by
            simp_rw [mul_pow]
            rw [Finset.prod_mul_distrib]
      _ = s ^ d * ∏ i : Fin n, (r * q i) ^ exponent i := by
            rw [Finset.prod_pow_eq_pow_sum, hdegree]
  rw [hproduct]
  ring

/-! ## The localized chart-overlap identity -/

/-- Mapping chosen-chart dehomogenization into the overlap ring is the same
as evaluating the projective polynomial at its chosen-chart coordinates. -/
theorem algebraMap_projectiveDehomogenizeAt {m : ℕ}
    (chart : Fin (m + 1)) (p : MvPolynomial (Fin (m + 1)) K) :
    algebraMap (MvPolynomial (Fin m) K)
        (ChartOverlapRing (K := K) chart)
        (projectiveDehomogenizeAt chart p) =
      MvPolynomial.eval₂
        (algebraMap K (ChartOverlapRing (K := K) chart))
        (fun a ↦ algebraMap (MvPolynomial (Fin m) K)
          (ChartOverlapRing (K := K) chart)
          (chartProjectiveCoordinate chart a)) p := by
  rw [show projectiveDehomogenizeAt chart p =
      MvPolynomial.bind₁ (chartProjectiveCoordinate (K := K) chart) p by rfl]
  rw [MvPolynomial.hom_bind₁]
  change MvPolynomial.eval₂ _ _ p = MvPolynomial.eval₂ _ _ p
  apply MvPolynomial.eval₂_congr
  intro _ _ _ _
  rfl

/-- Zeroth-chart dehomogenization followed by the overlap transition is
projective evaluation after dividing every chosen-chart coordinate by
`X₀/X_chart`. -/
theorem chartZeroToChosenOverlap_projectiveDehomogenize {m : ℕ}
    (chart : Fin (m + 1)) (p : MvPolynomial (Fin (m + 1)) K) :
    chartZeroToChosenOverlap (K := K) chart (projectiveDehomogenize p) =
      MvPolynomial.eval₂
        (algebraMap K (ChartOverlapRing (K := K) chart))
        (fun a ↦
          IsLocalization.Away.invSelf
              (chartOverlapDenominator (K := K) chart) *
            algebraMap (MvPolynomial (Fin m) K)
              (ChartOverlapRing (K := K) chart)
              (chartProjectiveCoordinate chart a)) p := by
  rw [show projectiveDehomogenize p = MvPolynomial.bind₁
      (Fin.cases 1 fun i ↦ MvPolynomial.X i) p by rfl]
  rw [MvPolynomial.hom_bind₁]
  have hcoeff :
      (chartZeroToChosenOverlap (K := K) chart).comp MvPolynomial.C =
        algebraMap K (ChartOverlapRing (K := K) chart) := by
    ext k
    simp [chartZeroToChosenOverlap]
  rw [hcoeff]
  apply MvPolynomial.eval₂_congr
  intro a _ _ _
  refine Fin.cases ?_ (fun i ↦ ?_) a
  · rw [Fin.cases_zero, map_one]
    calc
      1 = algebraMap (MvPolynomial (Fin m) K)
          (ChartOverlapRing (K := K) chart)
          (chartOverlapDenominator (K := K) chart) *
          IsLocalization.Away.invSelf
            (chartOverlapDenominator (K := K) chart) :=
        (chartOverlapDenominator_mul_invSelf (K := K) chart).symm
      _ = IsLocalization.Away.invSelf
            (chartOverlapDenominator (K := K) chart) *
          algebraMap (MvPolynomial (Fin m) K)
            (ChartOverlapRing (K := K) chart)
            (chartProjectiveCoordinate chart 0) := mul_comm _ _
  · rw [Fin.cases_succ, chartZeroToChosenOverlap_X]
    exact mul_comm _ _

/-- Exact overlap transition for a homogeneous projective equation.  The two
dehomogenizations differ by the invertible degree-`d` power of
`X₀/X_chart`; hence they define the same localized equation ideal. -/
theorem localized_projectiveDehomogenizeAt_eq_pow_mul_transition
    {m : ℕ} (chart : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) K) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    algebraMap (MvPolynomial (Fin m) K)
        (ChartOverlapRing (K := K) chart)
        (projectiveDehomogenizeAt chart p) =
      algebraMap (MvPolynomial (Fin m) K)
          (ChartOverlapRing (K := K) chart)
          (chartOverlapDenominator (K := K) chart) ^ d *
        chartZeroToChosenOverlap (K := K) chart
          (projectiveDehomogenize p) := by
  let L := ChartOverlapRing (K := K) chart
  let q : Fin (m + 1) → L := fun a ↦
    algebraMap (MvPolynomial (Fin m) K) L
      (chartProjectiveCoordinate chart a)
  let s : L := algebraMap (MvPolynomial (Fin m) K) L
    (chartOverlapDenominator (K := K) chart)
  let r : L := IsLocalization.Away.invSelf
    (chartOverlapDenominator (K := K) chart)
  have hsr : s * r = 1 :=
    chartOverlapDenominator_mul_invSelf (K := K) chart
  have hscale := eval_eq_pow_mul_eval_mul_of_homogeneous
    (MvPolynomial.map (algebraMap K L) p) d
    (hp.map (algebraMap K L)) q s r hsr
  rw [algebraMap_projectiveDehomogenizeAt]
  rw [chartZeroToChosenOverlap_projectiveDehomogenize]
  simpa [MvPolynomial.eval_map, q, s, r] using hscale

/-- Homogenization followed by arbitrary-chart dehomogenization is the
localized transition of the original affine polynomial, up to the expected
invertible power of `X₀/X_chart`. -/
theorem localized_dehomogenizeAt_homogenizeAtZero
    {m : ℕ} (chart : Fin (m + 1))
    (f : MvPolynomial (Fin m) K) :
    algebraMap (MvPolynomial (Fin m) K)
        (ChartOverlapRing (K := K) chart)
        (projectiveDehomogenizeAt chart (homogenizeAtZero f)) =
      algebraMap (MvPolynomial (Fin m) K)
          (ChartOverlapRing (K := K) chart)
          (chartOverlapDenominator (K := K) chart) ^ f.totalDegree *
        chartZeroToChosenOverlap (K := K) chart f := by
  rw [localized_projectiveDehomogenizeAt_eq_pow_mul_transition
    chart (homogenizeAtZero f) f.totalDegree
      (homogenizeAtZero_isHomogeneous f)]
  rw [projectiveDehomogenize_homogenizeAtZero]

/-- The zeroth-chart equations transported to the overlap ring. -/
def localizedZeroChartEquationIdeal {m : ℕ} {ι : Type*}
    (chart : Fin (m + 1))
    (equations : ι → MvPolynomial (Fin (m + 1)) K) :
    Ideal (ChartOverlapRing (K := K) chart) :=
  Ideal.span (Set.range fun j ↦
    chartZeroToChosenOverlap (K := K) chart
      (projectiveDehomogenize (equations j)))

/-- The chosen-chart equations mapped to the same overlap ring. -/
def localizedChosenChartEquationIdeal {m : ℕ} {ι : Type*}
    (chart : Fin (m + 1))
    (equations : ι → MvPolynomial (Fin (m + 1)) K) :
    Ideal (ChartOverlapRing (K := K) chart) :=
  Ideal.span (Set.range fun j ↦
    algebraMap (MvPolynomial (Fin m) K)
      (ChartOverlapRing (K := K) chart)
      (projectiveDehomogenizeAt chart (equations j)))

/-- Homogeneous projective equations generate the same ideal after both
affine charts are restricted to their overlap.  This is the corrected ideal
statement: equality holds after the chart-transition map and localization,
not between the two untransformed affine polynomial ideals. -/
theorem localized_chartEquationIdeals_eq
    {m : ℕ} {ι : Type*} (chart : Fin (m + 1))
    (equations : ι → MvPolynomial (Fin (m + 1)) K)
    (degree : ι → ℕ)
    (homogeneous : ∀ j, (equations j).IsHomogeneous (degree j)) :
    localizedZeroChartEquationIdeal chart equations =
      localizedChosenChartEquationIdeal chart equations := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    let s : ChartOverlapRing (K := K) chart :=
      algebraMap (MvPolynomial (Fin m) K)
        (ChartOverlapRing (K := K) chart)
        (chartOverlapDenominator (K := K) chart)
    have hchosen :
        algebraMap (MvPolynomial (Fin m) K)
            (ChartOverlapRing (K := K) chart)
            (projectiveDehomogenizeAt chart (equations j)) ∈
          localizedChosenChartEquationIdeal chart equations :=
      Ideal.subset_span ⟨j, rfl⟩
    have hrelation :=
      localized_projectiveDehomogenizeAt_eq_pow_mul_transition
        chart (equations j) (degree j) (homogeneous j)
    have hmultiple :
        chartZeroToChosenOverlap (K := K) chart
              (projectiveDehomogenize (equations j)) * s ^ degree j ∈
          localizedChosenChartEquationIdeal chart equations := by
      rw [mul_comm, ← hrelation]
      exact hchosen
    have hs : IsUnit (s ^ degree j) :=
      (IsLocalization.Away.algebraMap_isUnit
        (chartOverlapDenominator (K := K) chart)).pow _
    exact (Ideal.mul_unit_mem_iff_mem _ hs).mp hmultiple
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change algebraMap (MvPolynomial (Fin m) K)
        (ChartOverlapRing (K := K) chart)
        (projectiveDehomogenizeAt chart (equations j)) ∈
      localizedZeroChartEquationIdeal chart equations
    rw [localized_projectiveDehomogenizeAt_eq_pow_mul_transition
      chart (equations j) (degree j) (homogeneous j)]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨j, rfl⟩)

/-- Finite homogenized equations for an affine ideal satisfy the corrected
global-to-local statement on every projective chart overlap. -/
theorem exists_finite_homogeneous_chartOverlapPresentation
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) K)) :
    ∃ (n : ℕ) (equations : Fin n → MvPolynomial (Fin (m + 1)) K)
        (degree : Fin n → ℕ),
      (∀ j, (equations j).IsHomogeneous (degree j)) ∧
      dehomogenizedEquationIdeal equations = I ∧
      ∀ chart : Fin (m + 1),
        localizedZeroChartEquationIdeal chart equations =
          localizedChosenChartEquationIdeal chart equations := by
  obtain ⟨n, equations, degree, homogeneous, hdehom⟩ :=
    exists_finite_homogeneous_equations_dehomogenizing_to I
  refine ⟨n, equations, degree, homogeneous, hdehom, ?_⟩
  intro chart
  exact localized_chartEquationIdeals_eq chart equations degree homogeneous


end


end Stafford38.Geometry.LocalizedProjectiveChartTransition
