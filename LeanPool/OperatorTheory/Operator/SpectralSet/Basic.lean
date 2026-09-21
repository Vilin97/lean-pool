/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Polynomial spectral sets — definitions (L2.1)

Defines `polynomialSupNorm`, `IsKPolynomialSpectralSet`, and `IsPolynomialSpectralSet`.
These are *polynomial* spectral sets (norm bound on `Polynomial.aeval`).
-/

open scoped Polynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The supremum of the norm of a polynomial over a complex set. -/
noncomputable def polynomialSupNorm (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  ⨆ z ∈ X, ‖Polynomial.eval z p‖

/-- Spectrum containment and a polynomial-calculus bound with constant `K`. -/
def IsKPolynomialSpectralSet (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ) : Prop :=
  spectrum ℂ (A : E →L[ℂ] E) ⊆ X ∧
  ∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤ K * polynomialSupNorm p X

/-- A polynomial spectral set with multiplicative constant one. -/
def IsPolynomialSpectralSet (A : E →L[ℂ] E) (X : Set ℂ) : Prop :=
  IsKPolynomialSpectralSet A 1 X

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
