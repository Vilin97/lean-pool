/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.RitzResidual
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Residual.AngleEmbeddings

/-!
# Compatibility surface for the unfinished canonical tangent-map corollary
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Canonical directed-tangent specialization of the paper theorem. -/
theorem tanThetaEmbedding_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (ritzResidual A X) := by
  have htrans := isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap
  have htan : (tanThetaEmbedding U X).singularValues =
      principalTangents (approximateSubspace X) U := by
    rw [← graphOperator_eq_tanThetaEmbedding U X htrans]
    exact singularValues_graphOperator U X htrans
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap
    (tanThetaEmbedding U X) htan


end DavisKahan.FiniteDimensional
end TauCeti
