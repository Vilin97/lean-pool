/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LeanPool.OSforGFF.General.PositiveDefinite
import LeanPool.OSforGFF.General.GaussianRBF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import LeanPool.OSforGFF.Measure.NuclearSpace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
-- Bochner library imports for proven Minlos theorem
import LeanPool.OSforGFF.Minlos.Main
import LeanPool.OSforGFF.Bochner.PositiveDefinite

/-!
# Minlos Theorem and Gaussian Measure Construction

Uses the proven Minlos theorem from the bochner library to construct Gaussian measures.
The bochner library provides:
- `minlos_theorem`: proven via Bochner + Kolmogorov extension
- `minlos_uniqueness`: derived from minlos_theorem
- `IsPositiveDefinite`: hermitian + nonneg PD structure (in `Bochner.PositiveDefinite`)

This file bridges between the GFF4D project's `GFF4D.IsPositiveDefinite` (nonneg only)
and the bochner library's `IsPositiveDefinite` (hermitian + nonneg), then applies
the proven Minlos theorem.

## Main declarations

- `minlos_gaussian_construction`: Minlos + Gaussian CF → probability measure
- `gaussian_measure_symmetry`: covariance-preserving maps induce measure symmetries
-/

open Complex MeasureTheory Matrix TopologicalSpace
open BigOperators

noncomputable section

/-! ## GFF4D Positive Definiteness Lemmas

These use the GFF4D (nonneg-only) notion of positive definiteness.
-/

/-- **Gaussian RBF kernel is positive definite on inner product spaces** (GFF4D version). -/
theorem gaussian_rbf_pd_innerProduct
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
  GFF4D.IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) :=
  gaussian_rbf_pd_innerProduct_proof

/-- If covariance is realized as a squared norm via a linear embedding T into
    a real inner product space H, then the Gaussian characteristic functional
    is positive definite (GFF4D sense).
-/
lemma gaussian_positive_definite_via_embedding
  {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖ ^ 2 : ℝ)) :
  GFF4D.IsPositiveDefinite (fun f => Complex.exp (-(1/2 : ℂ) * (covariance_form f f))) := by
  have hPD_H := gaussian_rbf_pd_innerProduct (H := H)
  intro m x c
  have repl : ∀ i j,
      covariance_form (x i - x j) (x i - x j) = (‖T (x i - x j)‖ ^ 2 : ℝ) :=
    fun i j => by simpa using h_eq (x i - x j)
  have hPD_comp :
    0 ≤ (∑ i, ∑ j,
      (starRingEnd ℂ) (c i) * c j *
        Complex.exp (-(1/2 : ℂ) * ((‖T (x i) - T (x j)‖ ^ 2 : ℝ)))).re := by
    simpa using (GFF4D.isPositiveDefinite_precomp_linear
      (ψ := fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) hPD_H T) m x c
  simpa [repl, LinearMap.map_sub] using hPD_comp

/-! ## Bridge lemmas: GFF4D PD → Bochner PD

The bochner library's `IsPositiveDefinite` requires both:
1. `hermitian`: φ(-x) = conj(φ(x))
2. `nonneg`: Re(∑ᵢⱼ cbarᵢ cⱼ φ(xᵢ - xⱼ)) ≥ 0

The GFF4D version only requires (2). For the Gaussian CF exp(-½Q(f,f)),
hermiticity follows from Q(-f,-f) = Q(f,f) (which must be supplied).
-/

/-- Promote GFF4D's nonneg-only PD to bochner's hermitian+nonneg PD,
    given an explicit symmetry proof φ(-x) = conj(φ(x)).
-/
theorem gff4d_to_bochner_pd {α : Type*} [AddGroup α] {φ : α → ℂ}
    (h_nonneg : GFF4D.IsPositiveDefinite φ)
    (h_symm : ∀ x, φ (-x) = starRingEnd ℂ (φ x)) :
    IsPositiveDefinite φ where
  hermitian := h_symm
  nonneg := h_nonneg

/-- Helper: exp of a purely-real complex argument is self-conjugate. -/
private lemma conj_cexp_real (z : ℂ) (h : z.im = 0) :
    starRingEnd ℂ (Complex.exp z) = Complex.exp z := by
  have hz : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
  rw [hz, ← Complex.ofReal_exp]; exact Complex.conj_ofReal _

/-- The Gaussian CF argument -(1/2)*r is real for real r. -/
private lemma gaussian_cf_im_zero (r : ℝ) :
    (-(1/2 : ℂ) * (r : ℂ)).im = 0 := by
  simp [Complex.mul_im, Complex.neg_im, Complex.ofReal_im]

/-- The Gaussian RBF kernel is positive definite in the bochner sense.
    The hermitian condition follows from ‖-h‖ = ‖h‖.
-/
theorem gaussian_rbf_pd_bochner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) :=
  gff4d_to_bochner_pd gaussian_rbf_pd_innerProduct_proof (fun h => by
    simp only [norm_neg]; exact (conj_cexp_real _ (gaussian_cf_im_zero _)).symm)

/-- Gaussian CF via embedding is PD in the bochner sense, given Q(-f,-f) = Q(f,f). -/
lemma gaussian_positive_definite_bochner
    {E H : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : E →ₗ[ℝ] H)
    (covariance_form : E → E → ℝ)
    (h_eq : ∀ f, covariance_form f f = (‖T f‖ ^ 2 : ℝ))
    (h_symm : ∀ f, covariance_form (-f) (-f) = covariance_form f f) :
    IsPositiveDefinite
      (fun f => Complex.exp (-(1/2 : ℂ) * (covariance_form f f))) :=
  gff4d_to_bochner_pd
    (gaussian_positive_definite_via_embedding T covariance_form h_eq)
    (fun f => by
      rw [h_symm]
      simp only [one_div, neg_mul]
      apply (conj_cexp_real _ _).symm
      simp [Complex.mul_im, Complex.neg_im, Complex.ofReal_im])

/-! ## Gaussian Characteristic Functional -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- For Gaussian measures, the characteristic functional has the special form
    Φ(f) = exp(-½⟨f, Cf⟩) where C is a nuclear covariance operator.
-/
def gaussianCharacteristicFunctional
  (covariance_form : E → E → ℝ) (f : E) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * (covariance_form f f))

/-! ## Minlos Theorem Applications -/

/-- Application of Minlos theorem to Gaussian measures. -/
theorem minlos_gaussian_construction
  [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖ ^ 2 : ℝ))
  (h_symm : ∀ f, covariance_form (-f) (-f) = covariance_form f f)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, gaussianCharacteristicFunctional covariance_form f =
              ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure) := by
  have h_cf_cont : Continuous (gaussianCharacteristicFunctional covariance_form) :=
    continuous_exp.comp (continuous_const.mul (continuous_ofReal.comp h_continuous))
  have h_cf_pd := gaussian_positive_definite_bochner T covariance_form h_eq h_symm
  have h_cf_norm : gaussianCharacteristicFunctional covariance_form 0 = 1 := by
    simp [gaussianCharacteristicFunctional, h_zero]
  obtain ⟨μ, hchar, _⟩ := minlos_theorem
    (gaussianCharacteristicFunctional covariance_form)
    h_cf_cont h_cf_pd h_cf_norm
  exact ⟨μ, hchar⟩

/-- The measure constructed by Minlos theorem for a Gaussian characteristic functional
    indeed has that functional as its characteristic function.
-/
theorem gaussian_measure_characteristic_functional
  [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖ ^ 2 : ℝ))
  (h_symm : ∀ f, covariance_form (-f) (-f) = covariance_form f f)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
              gaussianCharacteristicFunctional covariance_form f) := by
  obtain ⟨μ,
    hchar⟩ := minlos_gaussian_construction T covariance_form h_eq h_symm h_zero h_continuous
  exact ⟨μ, fun f => (hchar f).symm⟩

/-! ## Minlos Uniqueness (re-exported from bochner) -/

/-- Uniqueness for the Gaussian CF: if two probability measures have the same
    Gaussian characteristic functional, they are equal.
-/
theorem minlos_gaussian_uniqueness
  [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
  {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
  (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
  {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
  (h₁ : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
  (h₂ : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
  μ₁ = μ₂ :=
  minlos_uniqueness hΦ_cont hΦ_pd hΦ_norm h₁ h₂

/-! ## Symmetry Transfer from Characteristic Functional to Measure -/

/-- Corollary for Gaussian measures: if the covariance form is invariant under g,
    then the Gaussian measure is invariant under the dual action of g.
-/
theorem gaussian_measure_symmetry
  [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
  (covariance_form : E → E → ℝ)
  (h_cf_cont : Continuous (gaussianCharacteristicFunctional covariance_form))
  (h_cf_pd : IsPositiveDefinite (gaussianCharacteristicFunctional covariance_form))
  (h_cf_norm : gaussianCharacteristicFunctional covariance_form 0 = 1)
  (μ : ProbabilityMeasure (WeakDual ℝ E))
  (h_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
                     gaussianCharacteristicFunctional covariance_form f)
  (g : E →L[ℝ] E)
  (h_covar_symm : ∀ f : E, covariance_form (g f) (g f) = covariance_form f f)
  (μ_push : ProbabilityMeasure (WeakDual ℝ E))
  (h_push_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ_push.toMeasure =
                          ∫ ω, Complex.exp (I * (ω (g f))) ∂μ.toMeasure)
  : μ_push = μ := by
  have h_Φ_symm : ∀ f, gaussianCharacteristicFunctional covariance_form (g f) =
                       gaussianCharacteristicFunctional covariance_form f := by
    intro f
    simp only [gaussianCharacteristicFunctional, h_covar_symm]
  exact minlos_uniqueness h_cf_cont h_cf_pd h_cf_norm
    (fun f => by rw [h_push_char, h_char (g f), h_Φ_symm]) h_char

end
