/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-!
# Infinite-dimensional double-angle residual embedding

The one-sided Davis--Kahan `sin (2 Theta)` operator attached to a trial range
`V = range X` is

`2 P_{U^perp} P_V P_U`.

This definition is valid in arbitrary Hilbert dimension and agrees literally
with the finite-dimensional source normalization.  No singular-value or compactness
hypothesis is needed to define it.

**Promoted 2026-07-30 under lane `EXP-PROMOTE-MISC`**, from
`DavisKahan/Experimental/InfiniteDimensional/Core/`.  Nothing is restated.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- One-sided double-angle sine operator for a trial embedding. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection] : E →L[𝕜] E :=
  (2 : 𝕜) •
    ((Uᗮ).starProjection ∘L
      Submodule.starProjection (LinearMap.range X.toLinearMap) ∘L U.starProjection)

/-- Unfolding identifies the trial-range construction with the ambient
one-sided double-angle operator `2 P_{U^perp} P_V P_U`. -/
theorem sinTwoThetaEmbedding_eq_rangeAngle (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E)
    (_hX : DavisKahan.IsometricEmbedding X)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection] :
    sinTwoThetaEmbedding U X =
      (2 : 𝕜) •
        ((Uᗮ).starProjection ∘L
          Submodule.starProjection (LinearMap.range X.toLinearMap) ∘L U.starProjection) :=
  rfl

end DavisKahanExt
end TauCeti
