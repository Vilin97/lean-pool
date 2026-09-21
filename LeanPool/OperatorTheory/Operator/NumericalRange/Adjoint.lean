/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import LeanPool.OperatorTheory.Operator.NumericalRange.Basic

/-!
# Numerical range of the adjoint (L2.3)

For a continuous linear operator on a complex Hilbert space, the numerical
range of its adjoint is the pointwise complex conjugate of its numerical
range.

## Main declaration

* `numericalRange_adjoint` — `W(A†) = conj '' W(A)`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The numerical range of the adjoint is the pointwise complex conjugate of
the numerical range. -/
theorem numericalRange_adjoint (A : E →L[ℂ] E) :
    numericalRange (ContinuousLinearMap.adjoint A) =
      (starRingEnd ℂ) '' (numericalRange A) := by
  ext z
  constructor
  · rintro ⟨x, hx, hz⟩
    refine ⟨⟪x, A x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hz, adjoint_inner_right, inner_conj_symm]
  · rintro ⟨w, ⟨x, hx, hxw⟩, hwz⟩
    refine ⟨x, hx, ?_⟩
    rw [adjoint_inner_right, ← inner_conj_symm, hxw, hwz]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
