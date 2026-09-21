/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportDomain

/-!
# Smooth Jordan exhaustions from rounded support envelopes

The finite-polytope construction gives more than the terminal operator
inequality: combined with the polytope reduction, it supplies arbitrarily
tight smooth Jordan outer approximations of every nonempty compact convex
planar set.  This file exposes that geometric consequence and packages the
resulting strict nested exhaustion, including the canonical specialization to
the closed numerical range of an operator.
-/

open Complex Metric Set
open scoped InnerProductSpace

/-- Every nonempty compact convex planar set admits arbitrarily tight smooth
Jordan outer approximations. -/
theorem hasSmoothJordanOuterApproximation_of_isCompact_nonempty_convex
    {K : Set ℂ} (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K) :
    HasSmoothJordanOuterApproximation K :=
  hasSmoothJordanOuterApproximation_of_polytope_case
    hKcompact hKnonempty hKconvex
      hasSmoothJordanOuterApproximationForPolytopes

/-- The rounded-support construction canonically produces a strict nested
smooth Jordan exhaustion of every nonempty compact convex planar set. -/
noncomputable def StrictNestedSmoothJordanExhaustion.ofCompactConvex
    (K : Set ℂ) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K) :
    StrictNestedSmoothJordanExhaustion K :=
  StrictNestedSmoothJordanExhaustion.ofOuterApproximation
    K hKcompact hKconvex
      (hasSmoothJordanOuterApproximation_of_isCompact_nonempty_convex
        hKcompact hKnonempty hKconvex)

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The closure of the numerical range of a bounded operator is compact. -/
theorem isCompact_closure_numericalRange (A : E →L[ℂ] E) :
    IsCompact (closure (numericalRange A)) := by
  exact (isBounded_numericalRange A).isCompact_closure

/-- On a nontrivial Hilbert space the numerical range, and hence its closure,
is nonempty. -/
theorem nonempty_closure_numericalRange [Nontrivial E]
    (A : E →L[ℂ] E) : (closure (numericalRange A)).Nonempty := by
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hxnorm : ‖x‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hx
    exact hx
  exact ⟨⟪x, A x⟫_ℂ,
    subset_closure ((mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩)⟩

variable [Nontrivial E]

/-- The closed numerical range has arbitrarily tight smooth Jordan outer
approximations. -/
theorem hasSmoothJordanOuterApproximation_closure_numericalRange
    (A : E →L[ℂ] E) :
    HasSmoothJordanOuterApproximation (closure (numericalRange A)) :=
  hasSmoothJordanOuterApproximation_of_isCompact_nonempty_convex
    (isCompact_closure_numericalRange A)
    (nonempty_closure_numericalRange A)
    (convex_numericalRange A).closure

/-- The canonical strict nested smooth Jordan exhaustion of the closed
numerical range. -/
noncomputable def StrictNestedSmoothJordanExhaustion.numericalRange
    (A : E →L[ℂ] E) :
    StrictNestedSmoothJordanExhaustion
      (closure (_root_.numericalRange A)) :=
  StrictNestedSmoothJordanExhaustion.ofCompactConvex
    (closure (_root_.numericalRange A))
    (isCompact_closure_numericalRange A)
    (nonempty_closure_numericalRange A)
    (convex_numericalRange A).closure

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
