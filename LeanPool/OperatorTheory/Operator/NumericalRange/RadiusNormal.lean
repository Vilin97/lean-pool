/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import LeanPool.OperatorTheory.Operator.NumericalRange.RadiusSpectrum

/-!
# Numerical radius of normal operators

For a star-normal operator, the spectral radius equals the operator norm.
Since the spectrum lies in the closed numerical-range disk, the numerical
radius therefore equals the operator norm.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The numerical radius of a normal operator equals its operator norm. -/
theorem numericalRadius_eq_norm_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] :
    numericalRadius A = ‖A‖ := by
  by_cases hE : Nontrivial E
  · let _ : Nontrivial E := hE
    apply le_antisymm (numericalRadius_le_norm A)
    have h := spectralRadius_toReal_le_numericalRadius A
    rw [IsStarNormal.spectralRadius_eq_nnnorm A] at h
    simpa using h
  · let _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    have hA : A = 0 := Subsingleton.elim _ _
    subst A
    simp only [numericalRadius_zero, norm_zero]

/-- A selfadjoint operator has numerical radius equal to its norm. -/
theorem numericalRadius_eq_norm_of_isSelfAdjoint
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    numericalRadius A = ‖A‖ := by
  let _ : IsStarNormal A := hA.isStarNormal
  exact numericalRadius_eq_norm_of_isStarNormal A

/-- A unitary operator on a nontrivial Hilbert space has numerical radius
one. -/
theorem numericalRadius_eq_one_of_mem_unitary
    [Nontrivial E] (U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius U = 1 := by
  let _ : IsStarNormal U := isStarNormal_of_mem_unitary hU
  exact (numericalRadius_eq_norm_of_isStarNormal U).trans
    (CStarRing.norm_of_mem_unitary hU)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
