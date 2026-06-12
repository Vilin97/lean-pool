/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
Positive Definite Functions

This file contains the definition of positive definite functions and basic lemmas.
Extracted from Minlos.lean to avoid circular imports with GaussianRBF.lean.

Key definitions:
- `IsPositiveDefinite`: A function φ : α → ℂ is positive definite if for any finite
  collection of points and complex coefficients, ∑ᵢⱼ cbarᵢ cⱼ φ(xᵢ - xⱼ) ≥ 0

Key lemmas:
- `isPositiveDefinite_precomp_linear`: Composition with linear map preserves PD
-/

open Complex
open BigOperators

/-! ## Positive Definiteness

Namespaced under `GFF4D` to avoid clash with `IsPositiveDefinite` from the
bochner library (which requires both hermitian + nonneg).
-/

namespace GFF4D

/-- A function φ : α → ℂ is positive definite if for any finite collection
    of points x₁, ..., xₘ and complex coefficients c₁, ..., cₘ, we have
    ∑ᵢⱼ cbarᵢ cⱼ φ(xᵢ - xⱼ) ≥ 0

    This is the standard definition in harmonic analysis and probability theory.
-/
def IsPositiveDefinite {α : Type*} [AddGroup α] (φ : α → ℂ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → α) (c : Fin m → ℂ),
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (x i - x j)).re

/-- Composition preserves positive definiteness: if ψ is positive definite on H and
    T : E →ₗ[ℝ] H is linear, then ψ ∘ T is positive definite on E.
-/
lemma isPositiveDefinite_precomp_linear
  {E H : Type*} [AddCommGroup E] [AddCommGroup H]
  [Module ℝ E] [Module ℝ H]
  (ψ : H → ℂ) (hPD : IsPositiveDefinite ψ) (T : E →ₗ[ℝ] H) :
  IsPositiveDefinite (fun f : E => ψ (T f)) := fun m x c => by
  simpa using hPD m (fun i => T (x i)) c

end GFF4D
