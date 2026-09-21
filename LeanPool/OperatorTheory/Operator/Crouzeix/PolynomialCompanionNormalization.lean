/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Normalize approximate polynomial companions

Uniform polynomial approximation naturally gives a scalar sup-norm bound with
an arbitrarily small additive error.  The fourth-power Crouzeix--Palencia
bootstrap instead consumes an exactly contractive sequence.  This file bridges
those interfaces by shrinking the `j`-th approximant by
`m / (m + 1 / (j + 1))`.  The shrinkage factors tend to one, so the operator
limit is unchanged.

The zero case necessarily needs separate information: exact contractivity at
`m = 0` forces every normalized polynomial to vanish, and hence can converge
only to zero.  This condition is explicit in the generic statement; for the
canonical Crouzeix auxiliary operator it follows from vanishing of the source
polynomial on an infinite compact control set.

## Main declaration

* `exists_tendsto_polynomial_companions_of_add_one_div_bounds` -- convert
  additive `1 / (j + 1)` sup-norm errors into an exactly contractive sequence
  without changing the operator-norm limit.
* `polynomialSupNorm_le_add_of_uniform_approximation` -- a contractive scalar
  target and a uniform polynomial approximation give the required additive
  sup-norm bound.
* `exists_tendsto_polynomial_companions_of_uniform_approximation` -- combine
  uniform approximation of a contractive scalar companion with exact
  normalization.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialSupNormZero

open Filter

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem
    exists_tendsto_polynomial_companions_of_add_one_div_bounds_of_pos
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 < m)
    (G : E →L[ℂ] E) (r : ℕ → Polynomial ℂ)
    (hr : ∀ j, polynomialSupNorm (r j) S ≤
      m + 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  let a : ℕ → ℝ := fun j ↦ m / (m + ε j)
  let q : ℕ → Polynomial ℂ := fun j ↦ ((a j : ℝ) : ℂ) • r j
  refine ⟨q, ?_, ?_⟩
  · intro j
    have hε : 0 < ε j := by
      dsimp only [ε]
      positivity
    have hdenom : 0 < m + ε j := add_pos hm hε
    dsimp only [q]
    rw [polynomialSupNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hm hdenom)]
    calc
      m / (m + ε j) * polynomialSupNorm (r j) S ≤
          m / (m + ε j) * (m + ε j) :=
        mul_le_mul_of_nonneg_left (by simpa only [ε] using hr j)
          (div_nonneg hm.le hdenom.le)
      _ = m := by field_simp
  · have hεlim : Tendsto ε atTop (nhds 0) := by
      simpa only [ε] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0))
    have halim : Tendsto a atTop (nhds 1) := by
      have hnum : Tendsto (fun _ : ℕ ↦ m) atTop (nhds m) :=
        tendsto_const_nhds
      have hden : Tendsto (fun j ↦ m + ε j) atTop (nhds (m + 0)) :=
        tendsto_const_nhds.add hεlim
      have hdiv := hnum.div hden (by simpa only [add_zero] using hm.ne')
      change Tendsto (fun j ↦ m / (m + ε j)) atTop (nhds 1)
      convert hdiv using 1
      · ext j
        rfl
      · rw [add_zero, div_self hm.ne']
    have haclim : Tendsto (fun j ↦ ((a j : ℝ) : ℂ)) atTop (nhds 1) := by
      change Tendsto (Complex.ofReal ∘ a) atTop (nhds 1)
      simpa only [Complex.ofReal_one] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp halim
    have hscaled := haclim.smul hrlim
    simpa only [q, map_smul, one_smul] using hscaled

/-- Additive `1 / (j + 1)` errors in polynomial sup norm can be removed by
rescaling without changing the operator-norm limit.  The explicit zero-case
hypothesis is necessary: a sequence with exact bound zero consists of zero
polynomials, so its operator limit must be zero. -/
theorem exists_tendsto_polynomial_companions_of_add_one_div_bounds
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 ≤ m)
    (G : E →L[ℂ] E) (hGzero : m = 0 → G = 0)
    (r : ℕ → Polynomial ℂ)
    (hr : ∀ j, polynomialSupNorm (r j) S ≤
      m + 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by
  by_cases hm0 : m = 0
  · have hG : G = 0 := hGzero hm0
    refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · intro j
      rw [hm0]
      unfold polynomialSupNorm
      refine Real.iSup_le (fun z ↦ ?_) le_rfl
      exact Real.iSup_le (fun _ ↦ by
        simp only [Polynomial.eval_zero, norm_zero]
        exact le_rfl) le_rfl
    · rw [hG]
      simpa only [map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E →L[ℂ] E))
          atTop (nhds 0))
  · exact exists_tendsto_polynomial_companions_of_add_one_div_bounds_of_pos
      A S m (lt_of_le_of_ne hm (Ne.symm hm0)) G r hr hrlim

/-- If a scalar function is bounded by `m` on `S` and a polynomial uniformly
approximates it within `ε`, the polynomial sup norm on `S` is at most
`m + ε`.  No compactness assumption is needed because the pointwise upper
bound directly controls the conditionally complete supremum. -/
theorem polynomialSupNorm_le_add_of_uniform_approximation
    (r : Polynomial ℂ) (S : Set ℂ) (g : ℂ → ℂ) (m ε : ℝ)
    (hm : 0 ≤ m) (hε : 0 ≤ ε)
    (hg : ∀ z ∈ S, ‖g z‖ ≤ m)
    (happrox : ∀ z ∈ S, ‖Polynomial.eval z r - g z‖ ≤ ε) :
    polynomialSupNorm r S ≤ m + ε := by
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_) (add_nonneg hm hε)
  refine Real.iSup_le (fun hz ↦ ?_) (add_nonneg hm hε)
  calc
    ‖Polynomial.eval z r‖ =
        ‖(Polynomial.eval z r - g z) + g z‖ := by rw [sub_add_cancel]
    _ ≤ ‖Polynomial.eval z r - g z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ ε + m := add_le_add (happrox z hz) (hg z hz)
    _ = m + ε := add_comm _ _

/-- Uniform polynomial approximation of a scalar companion bounded by `m`
produces an exactly sup-norm-contractive polynomial sequence, provided the
polynomial evaluations already converge to the identified operator companion.
The latter identification is deliberately separate: analytically it comes
from the holomorphic functional calculus for the scalar Cauchy companion. -/
theorem exists_tendsto_polynomial_companions_of_uniform_approximation
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 ≤ m)
    (g : ℂ → ℂ) (hg : ∀ z ∈ S, ‖g z‖ ≤ m)
    (G : E →L[ℂ] E) (hGzero : m = 0 → G = 0)
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ S →
      ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by
  apply exists_tendsto_polynomial_companions_of_add_one_div_bounds
    A S m hm G hGzero r
  · intro j
    exact polynomialSupNorm_le_add_of_uniform_approximation (r j) S g m
      (1 / ((j : ℝ) + 1)) hm (by positivity) hg (happrox j)
  · exact hrlim

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
