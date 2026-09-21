/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SubspaceTransport

/-!
# Singular-value transport across canonical subspace coordinates

The paper writes projection blocks as ambient operators, whereas the natural
Lean theorem often uses a subtype as source or target.  Canonical inclusion and
orthogonal projection add only zero singular values, so the complete
approximation-number sequence is unchanged.  These lemmas make that
identification explicit.

Because the ambient and subtype coordinates are genuinely different Hilbert
spaces, the statements use the heterogeneous relation
`SameApproximationSingularSequence` rather than its same-type specialisation
`SameApproximationSingularValues`.

**The mathematics is not here.**  Nothing in these three statements mentions
Davis--Kahan, so all of it lives in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/SubspaceTransport.lean`
under `ContinuousLinearMap`; this module only keeps the paper's names for the
source layer, in the source layer's spelling of the relation.  The move was
forced by `DavisKahan/Geometry/Polar/RestrictedDisplacementExtremal.lean`, a
generic geometry module that used to reach backwards into this file.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Extending a map from a closed subspace by zero on its orthogonal complement
preserves every approximation singular value. -/
theorem sameApproximationSingularValues_extendDomainByZero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : U →L[𝕜] F) :
    SameApproximationSingularSequence
      (T ∘L U.subtypeL.adjoint) T :=
  ContinuousLinearMap.hasSameApproximationNumbers_extendDomainByZero U T

/-- Including the range of a map into the ambient Hilbert space preserves every
approximation singular value. -/
theorem sameApproximationSingularValues_includeCodomain
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] V) :
    SameApproximationSingularSequence (V.subtypeL ∘L T) T :=
  ContinuousLinearMap.hasSameApproximationNumbers_includeCodomain V T

/-- Ambient extension of a rectangular subspace block preserves the complete
singular-value sequence. -/
theorem sameApproximationSingularValues_ambientSubspaceBlock
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : U →L[𝕜] V) :
    SameApproximationSingularSequence
      (V.subtypeL ∘L T ∘L U.subtypeL.adjoint) T :=
  ContinuousLinearMap.hasSameApproximationNumbers_ambientSubspaceBlock U V T

end

end ExactSinTheta
end DavisKahan
end TauCeti
