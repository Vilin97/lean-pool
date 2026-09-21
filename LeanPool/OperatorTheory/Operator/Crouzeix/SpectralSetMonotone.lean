/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Monotonicity of polynomial spectral sets

Polynomial spectral-set estimates persist when the constant is increased or
when a compact control set is enlarged.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ApproximationSupNorm
import LeanPool.OperatorTheory.Operator.Crouzeix.BoundaryMaximum

open Set
open scoped InnerProductSpace Polynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A polynomial spectral-set estimate remains true with a larger constant. -/
theorem IsKPolynomialSpectralSet.mono_const
    {A : E →L[ℂ] E} {K L : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hKL : K ≤ L) :
    IsKPolynomialSpectralSet A L X := by
  refine ⟨h.1, fun p => (h.2 p).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hKL (polynomialSupNorm_nonneg p X)

/-- With a nonnegative constant, enlarging a compact control set preserves a
polynomial spectral-set estimate. -/
theorem IsKPolynomialSpectralSet.mono_set
    {A : E →L[ℂ] E} {K : ℝ} {X Y : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hK : 0 ≤ K)
    (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsKPolynomialSpectralSet A K Y := by
  constructor
  · exact h.1.trans hXY
  · intro p
    exact (h.2 p).trans (mul_le_mul_of_nonneg_left
      (polynomialSupNorm_mono_of_isCompact p hXY hY) hK)

/-- Simultaneously enlarge the constant and a compact control set. -/
theorem IsKPolynomialSpectralSet.mono
    {A : E →L[ℂ] E} {K L : ℝ} {X Y : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hK : 0 ≤ K)
    (hKL : K ≤ L) (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsKPolynomialSpectralSet A L Y :=
  (h.mono_set hK hXY hY).mono_const hKL

/-- A constant-one polynomial spectral set remains one after compact
enlargement. -/
theorem IsPolynomialSpectralSet.mono_set
    {A : E →L[ℂ] E} {X Y : Set ℂ}
    (h : IsPolynomialSpectralSet A X)
    (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsPolynomialSpectralSet A Y :=
  IsKPolynomialSpectralSet.mono_set h zero_le_one hXY hY

/-- Passing from a bounded control set to its closure preserves the spectral
set constant exactly. -/
theorem IsKPolynomialSpectralSet.closure_of_isBounded
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X)
    (hX : Bornology.IsBounded X) :
    IsKPolynomialSpectralSet A K (closure X) := by
  constructor
  · exact h.1.trans subset_closure
  · intro p
    rw [polynomialSupNorm_closure_of_isBounded p hX]
    exact h.2 p

/-- Compact control sets can be closed without changing a polynomial
spectral-set estimate. -/
theorem IsKPolynomialSpectralSet.closure_of_isCompact
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hX : IsCompact X) :
    IsKPolynomialSpectralSet A K (closure X) :=
  h.closure_of_isBounded hX.isBounded

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
