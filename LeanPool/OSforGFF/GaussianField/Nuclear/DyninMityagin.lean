/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Dynin-Mityagin Space Typeclass

Defines the `DyninMityaginSpace` typeclass for locally convex spaces admitting
a rapidly decaying Schauder basis. This formalizes the Dynin-Mityagin
theorem: a nuclear Fréchet space with a Schauder basis is isomorphic to
a Köthe sequence space with rapidly decaying weights.

The construction of Gaussian measures works for any `DyninMityaginSpace E`,
not just Schwartz spaces.

## Main definitions

- `DyninMityaginSpace E` — typeclass for nuclear Fréchet spaces with Schauder basis
- `DyninMityaginSpace.expansion_H` — recovery of the Hilbert-space expansion

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
-/

noncomputable section

namespace GaussianField

/-- A nuclear Fréchet space with a countable Schauder basis.

Seminorms and index type are bundled inside the class so that typeclass
synthesis can infer everything from `E` alone. The expansion axiom is
stated for scalar functionals `φ : E →L[ℝ] ℝ`, not arbitrary Hilbert
spaces — the Hilbert-space form is recovered as `expansion_H`.

The class includes `h_countable` (countable seminorm index) and
`h_completeSpace` (completeness w.r.t. the canonical uniform structure).
Together these give `BaireSpace E` (see `DyninMityaginSpace.instBaireSpace`)
via: countable seminorms → pseudometrizable + complete → Baire.
-/
class DyninMityaginSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] extends T1Space E where
  /-- Index type for the defining seminorm family. -/
  ι : Type
  /-- Defining seminorm family. -/
  p : ι → Seminorm ℝ E
  h_with : WithSeminorms p
  h_countable : Countable ι
  h_completeSpace :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)
  /-- Schauder basis vectors. -/
  basis : ℕ → E
  /-- Coefficient functionals for the basis expansion. -/
  coeff : ℕ → (E →L[ℝ] ℝ)
  expansion :
    ∀ (φ : E →L[ℝ] ℝ) (f : E), φ f = ∑' m, (coeff m f) * φ (basis m)
  basis_growth :
    ∀ (i : ι), ∃ C > 0, ∃ (s : ℕ),
    ∀ m, p i (basis m) ≤ C * (1 + (m : ℝ)) ^ s
  coeff_decay :
    ∀ (k : ℕ), ∃ C > 0, ∃ (s : Finset ι),
    ∀ f m, |coeff m f| * (1 + (m : ℝ)) ^ k ≤ C * (s.sup p) f

/-- A `DyninMityaginSpace` with biorthogonal basis and coefficients:
`coeff n (basis m) = δ_{nm}`. This holds for all DM spaces constructed
via `ofRapidDecayEquiv` (including Schwartz spaces and smooth circle functions).

Finite-dimensional spaces with eventually-zero bases do NOT satisfy this.
-/
class _root_.GaussianField.DyninMityaginSpace.HasBiorthogonalBasis (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [DyninMityaginSpace E] : Prop where
  coeff_basis : ∀ n m, DyninMityaginSpace.coeff (E := E) n (DyninMityaginSpace.basis m) =
    if n = m then 1 else 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]

/-- The Hilbert-space expansion recovered from the scalar axiom.

For any CLM `T : E →L[ℝ] H` and `w : H`, the map `f ↦ ⟪w, T f⟫` is a scalar
CLF, so the intrinsic `DyninMityaginSpace.expansion` applies.
-/
theorem _root_.GaussianField.DyninMityaginSpace.expansion_H
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : E →L[ℝ] H) (w : H) (f : E) :
    @inner ℝ H _ w (T f) =
    ∑' m, (DyninMityaginSpace.coeff m f) * @inner ℝ H _ w (T (DyninMityaginSpace.basis m)) := by
  have hφ := DyninMityaginSpace.expansion ((innerSL ℝ w).comp T) f
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hφ

end GaussianField
