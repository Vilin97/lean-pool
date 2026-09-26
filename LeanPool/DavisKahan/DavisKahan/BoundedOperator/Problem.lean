/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Bounded invariant-pair problems

The residual and sine block belong to an approximate invariant pair. Projection,
reducing-subspace, symmetry, and norm estimates are used directly from their
canonical `Submodule` and `ContinuousLinearMap` APIs.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Uniform acuteness bounds the projection gap strictly below one. In infinite
 dimension it is stronger than vanishing crossed intersections, which permits
 angles tending to a right angle. -/
def IsUniformlyAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  U.projectionGap V < 1

/-- The projection gap lies below the quarter-angle threshold. -/
def IsQuarterAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  U.projectionGap V < Real.sqrt 2 / 2

/-- An isometric bounded embedding. -/
def IsometricEmbedding (X : F →L[𝕜] E) : Prop := ∀ x, ‖X x‖ = ‖x‖

/-- Residual of an approximate invariant pair. -/
def residual (A : E →L[𝕜] E) (X : F →L[𝕜] E)
    (M : F →L[𝕜] F) : F →L[𝕜] E := A ∘L X - X ∘L M

/-- Directed sine block for an approximate subspace embedding. -/
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E :=
  Uᗮ.starProjection ∘L X

end DavisKahan
end TauCeti
