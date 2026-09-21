/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-!
# Symmetric subspace gap from two directed sine estimates

The natural spectral-subspace theorem is directed. Applying it in both
orientations gives two directed projection-gap estimates. The sharp
projector-difference identity combines them without a factor of two.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Two directed bounds with the same right-hand side imply the sharp symmetric
projection-gap bound. -/
theorem mul_subspaceGap_le_of_two_directedGap_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {δ r : ℝ} (hδ : 0 ≤ δ)
    (hUV : δ * U.directedProjectionGap V ≤ r)
    (hVU : δ * V.directedProjectionGap U ≤ r) :
    δ * U.projectionGap V ≤ r := by
  have hmax : U.projectionGap V =
      max (U.directedProjectionGap V) (V.directedProjectionGap U) :=
    U.projectionGap_eq_max_directedProjectionGap V
  rw [hmax, mul_max_of_nonneg _ _ hδ]
  exact max_le hUV hVU

/-- A pair of directed bounds with possibly different right-hand sides gives
the maximum of those bounds. -/
theorem mul_subspaceGap_le_max_of_two_directedGap_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {δ r s : ℝ} (hδ : 0 ≤ δ)
    (hUV : δ * U.directedProjectionGap V ≤ r)
    (hVU : δ * V.directedProjectionGap U ≤ s) :
    δ * U.projectionGap V ≤ max r s := by
  apply mul_subspaceGap_le_of_two_directedGap_le U V hδ
  · exact hUV.trans (le_max_left _ _)
  · exact hVU.trans (le_max_right _ _)

end ExactSinTheta
end DavisKahan
end TauCeti
