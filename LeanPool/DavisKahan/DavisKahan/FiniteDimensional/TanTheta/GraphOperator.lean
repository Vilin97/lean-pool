/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Residual.AngleEmbeddings
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# Finite coordinate tangent perturbation bounds

The historical ambient graph proof mixed maps on `E`, subtype graph maps, and
trial-coordinate maps.  The canonical finite theorem is rectangular: the graph
operator is `S |C|⁺ : F → E`, its singular values are the directed principal
tangents, and the ordered Ritz gap controls it through the trial residual.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Ordered-gap perturbation theorem for the canonical coordinate tangent. -/
theorem tanTheta_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (residual A X M) :=
  tanThetaEmbedding_residual_le_of_orderedGap
    N hA hU X hM hGalerkin hδ hgap

/-- The same result under the graph-operator compatibility name. -/
theorem tanThetaMap_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (graphOperator U X) ≤ N (residual A X M) := by
  simpa [graphOperator] using
    tanTheta_perturbation_le N hA hU X hM hGalerkin hδ hgap

/-- Operator-norm coordinate tangent bound. -/
theorem opNorm_tanTheta_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * ‖(tanThetaEmbedding U X).toContinuousLinearMap‖ ≤
      ‖(residual A X M).toContinuousLinearMap‖ := by
  simpa using tanTheta_perturbation_le
    (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := F) (F := E))
    hA hU X hM hGalerkin hδ hgap

/-- Frobenius coordinate tangent bound. -/
theorem frobenius_tanTheta_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * UnitarilyInvariantSeminorm.frobenius (tanThetaEmbedding U X) ≤
      UnitarilyInvariantSeminorm.frobenius (residual A X M) :=
  tanTheta_perturbation_le
    (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := E))
    hA hU X hM hGalerkin hδ hgap

/-- Ky Fan coordinate tangent bound. -/
theorem kyFan_tanTheta_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) (k : ℕ) :
    δ * TauCeti.kyFanSum k
        (tanThetaEmbedding U X) ≤
      TauCeti.kyFanSum k
        (residual A X M) := by
  simpa [UnitarilyInvariantSeminorm.kyFan_apply] using
    tanTheta_perturbation_le
      (UnitarilyInvariantSeminorm.kyFan
        (𝕜 := 𝕜) (E := F) (F := E) k)
      hA hU X hM hGalerkin hδ hgap

end DavisKahan.FiniteDimensional
end TauCeti
