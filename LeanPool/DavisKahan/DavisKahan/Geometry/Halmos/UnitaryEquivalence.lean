/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections

/-!
# Unitary equivalence of subspace pairs and bounded operators

Grounded relational predicates promoted out of the experimental Davis--Kahan
frontier.  They express unitary equivalence of ordered pairs of subspaces and of
bounded operators acting on possibly different Hilbert spaces, stated as bare
existential propositions so they carry no computational datum.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


universe u v

section CrossSpaceClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]

/-- Unitary equivalence of two ordered pairs of subspaces.

Stated as existential quantification over the unitary rather than as a
`Prop`-valued structure carrying it: the intended notion is a proposition, and
a `Prop` structure cannot hold the datum `H₁ ≃ₗᵢ[𝕜] H₂`. -/
def PairOfSubspacesUnitaryEquivalent
    (U₁ V₁ : Submodule 𝕜 H₁) (U₂ V₂ : Submodule 𝕜 H₂) : Prop :=
  ∃ e : H₁ ≃ₗᵢ[𝕜] H₂,
    U₁.map e.toLinearMap = U₂ ∧ V₁.map e.toLinearMap = V₂

/-- Unitary equivalence of bounded operators acting on possibly different
Hilbert spaces.

The intertwining is stated pointwise.  Writing it as a composition of
continuous linear maps forces `e` through `LinearMap.toContinuousLinearMap`,
which carries a `FiniteDimensional` hypothesis that the source statement does
not have. -/
def BoundedOperatorsUnitaryEquivalent
    (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂) : Prop :=
  ∃ e : H₁ ≃ₗᵢ[𝕜] H₂, ∀ x : H₁, e (A x) = B (e x)

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Complementing the second subspace of each pair preserves unitary
equivalence of ordered pairs. -/
theorem pairOfSubspacesUnitaryEquivalent_orthogonal_right
    {U₁ V₁ : Submodule 𝕜 H₁} {U₂ V₂ : Submodule 𝕜 H₂}
    [V₁.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ᗮ U₂ V₂ᗮ := by
  obtain ⟨e, hU, hV⟩ := h
  refine ⟨e, hU, ?_⟩
  have hmap : V₁ᗮ.map (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂) =
      (V₁.map (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂))ᗮ :=
    Submodule.map_orthogonal_equiv V₁ e
  have hcoe : (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂) = e.toLinearMap := rfl
  rw [hcoe] at hmap
  rw [hmap, hV]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Complementing the second subspace of each pair is an equivalence on the
pair-equivalence relation, because complementation is involutive. -/
theorem pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff
    (U₁ V₁ : Submodule 𝕜 H₁) (U₂ V₂ : Submodule 𝕜 H₂)
    [V₁.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ᗮ U₂ V₂ᗮ ↔
      PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ := by
  refine ⟨fun h => ?_, pairOfSubspacesUnitaryEquivalent_orthogonal_right⟩
  have h' := pairOfSubspacesUnitaryEquivalent_orthogonal_right h
  rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at h'

end CrossSpaceClassification

end DavisKahan
end TauCeti
