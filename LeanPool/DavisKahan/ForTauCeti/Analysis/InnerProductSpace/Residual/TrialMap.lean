/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz

/-!
# Residuals of arbitrary trial maps

General trial-map residuals, complementary blocks, and the projected Sylvester
identity before orthonormalization.

## Sources

The residual of a trial map generalises the Ritz residual of
`ForTauCeti/Analysis/InnerProductSpace/Residual/Ritz.lean`, whose source is
Davis--Kahan's residual form
(`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`).  Dropping
isometry to a lower frame bound is this library's generalisation.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Residual/TrialMap.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Residual of a general, not necessarily isometric, trial map. -/
@[expose]
noncomputable def generalResidual (A : E →ₗ[𝕜] E) (X : F →ₗ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X - X ∘ₗ M

/-- The raw complementary block of an arbitrary trial map.  For an isometric
embedding this specializes to `sinThetaEmbedding`; without normalization it is
the algebraic block bounded first in the generalized sine and tangent proofs. -/
@[expose]
noncomputable def complementaryTrialBlock (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗ[𝕜] E) : F →ₗ[𝕜] E :=
  complementaryProjection U ∘ₗ X

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- On an isometric trial map the general residual is the ordinary one,
definitionally.  Same pattern as `complementaryTrialBlock_toLinearMap`: the
general form takes an arbitrary linear map, the specific one an isometry. -/
@[simp] theorem generalResidual_toLinearMap (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    generalResidual A X.toLinearMap M = residual A X M :=
  rfl
omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **The arbitrary-trial-map projected-residual Sylvester identity.**

For a symmetric operator `A`, an `A`-reducing subspace `U`, an arbitrary trial
map `X`, and an arbitrary coordinate map `M`, the raw complementary block
`Y = P_{Uᗮ} X` satisfies

`A Y - Y M = P_{Uᗮ} (A X - X M)`.

This statement deliberately assumes no isometry, injectivity, frame bound,
or symmetry of `M`, and it does not require finite-dimensional trial
coordinates.  It is the shared algebraic root of the ordinary and generalized
residual sine bounds and of the graph-operator tangent development. -/
theorem sylvester_complementaryTrialBlock_eq_projectedGeneralResidual
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗ[𝕜] E) (M : F →ₗ[𝕜] F) :
    A ∘ₗ complementaryTrialBlock U X - complementaryTrialBlock U X ∘ₗ M =
      complementaryProjection U ∘ₗ generalResidual A X M := by
  ext x
  simp only [complementaryTrialBlock, generalResidual, LinearMap.comp_apply,
    LinearMap.sub_apply, map_sub]
  rw [complementaryProjection_apply_comm_of_isInvariant hA hU (X x)]

end TauCeti
