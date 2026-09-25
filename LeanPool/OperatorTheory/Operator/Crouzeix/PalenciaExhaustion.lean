/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ApproximationSupNorm
public import LeanPool.OperatorTheory.Operator.Crouzeix.CompactThickeningApprox
public import LeanPool.OperatorTheory.Operator.Crouzeix.PalenciaApproximation

/-!
# Crouzeix--Palencia assembly along compact exhaustions

This file joins compact-set sup-norm convergence to the sequence-limit
auxiliary assembly.  It reduces the exact Crouzeix--Palencia conclusion to
constructing the sharp auxiliary bounds at every stage of a decreasing
compact exhaustion of the closed numerical range.

## Main declaration

* `crouzeix_palencia_of_antitone_compact_auxiliary_bounds` -- exact L4.2
  from stagewise auxiliary bounds along a decreasing compact exhaustion.
* `crouzeix_palencia_of_compactThickening_auxiliary_bounds` -- the canonical
  specialization to closed thickenings of the closed numerical range.
-/

@[expose] public section

open Filter Set
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- If a decreasing sequence of nonempty compact sets intersects to the
closed numerical range and the sharp auxiliary bounds hold on every stage,
then the exact Crouzeix--Palencia polynomial spectral-set conclusion holds. -/
theorem crouzeix_palencia_of_antitone_compact_auxiliary_bounds
    (A : E →L[ℂ] E) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (haux : ∀ (p : Polynomial ℂ) (n : ℕ), ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (K n) ∧
      ‖Polynomial.aeval A p * G‖ ≤ polynomialSupNorm p (K n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_tendsto_auxiliary_bounds A
  intro p
  refine ⟨fun n ↦ polynomialSupNorm p (K n), ?_, haux p⟩
  have hlim := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
    p K hanti hcompact hnonempty
  rw [hinter] at hlim
  exact hlim

/-- If every stage of a decreasing compact exhaustion has a finite global
polynomial-calculus bound and uniformly contractive polynomial companions
converging in operator norm, then the stagewise fourth-power bootstraps and
sup-norm convergence give the exact Crouzeix--Palencia conclusion on the
intersection. -/
theorem crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p (K n))
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p (K n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hstage : ∀ n,
      IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (K n) := by
    intro n
    apply
      isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
        A (K n) (hcompact n)
    · exact (spectrum_subset_closure_numericalRange A).trans (by
        rw [← hinter]
        exact iInter_subset K n)
    · exact hfinite n
    · intro p
      exact hcompanion p n
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    have hlim := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
      p K hanti hcompact hnonempty
    rw [hinter] at hlim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds
      (tendsto_const_nhds.mul hlim) (fun n ↦ (hstage n).2 p)

/-- Finite polynomial-calculus bounds and convergent contractive polynomial
companions on every canonical closed thickening imply the exact
Crouzeix--Palencia conclusion. -/
theorem crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
    (A : E →L[ℂ] E)
    (hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p
        (compactThickeningApprox (closure (numericalRange A)) n))
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ j, polynomialSupNorm (q j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤ 2 * polynomialSupNorm p
          (compactThickeningApprox (closure (numericalRange A)) n)) :
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
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      exact hW.mono subset_closure
    obtain ⟨hanti, hstageCompact, hstageNonempty, hinter⟩ :=
      compactThickeningApprox_spec (closure (numericalRange A)) hcompact hnonempty
    exact
      crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
        A _ hanti hstageCompact hstageNonempty hinter hfinite hcompanion

/-- Sharp auxiliary bounds on the canonical compact thickenings of the closed
numerical range imply the exact Crouzeix--Palencia conclusion.  The zero
Hilbert space is discharged directly; otherwise the closed numerical range
is a nonempty compact set, so `compactThickeningApprox_spec` applies. -/
theorem crouzeix_palencia_of_compactThickening_auxiliary_bounds
    (A : E →L[ℂ] E)
    (haux : ∀ (p : Polynomial ℂ) (n : ℕ), ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n) ∧
      ‖Polynomial.aeval A p * G‖ ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n) ^ 2) :
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
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      exact hW.mono subset_closure
    obtain ⟨hanti, hstageCompact, hstageNonempty, hinter⟩ :=
      compactThickeningApprox_spec (closure (numericalRange A)) hcompact hnonempty
    exact crouzeix_palencia_of_antitone_compact_auxiliary_bounds A _
      hanti hstageCompact hstageNonempty hinter haux

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
