/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Residual.AngleEmbeddings

/-!
# Experimental residual `sin (2 Theta)` interface

The coordinate double-angle sine satisfies

`N (sinTwoThetaEmbedding U X) <= 2 * N (sinThetaEmbedding U X)`

for every rectangular unitarily invariant norm.  Consequently every proven
single-angle residual estimate immediately gives a double-angle residual
estimate with twice the constant.

The residual gap belongs between the coordinate operator `M` and the unwanted
spectrum of `A` on `Uᗮ`.  A bare internal gap between the two reducing blocks
of `A` does not control an arbitrary trial pair `(X,M)`, and the former direct
Sylvester body was not type-correct: its displayed right-hand side consisted
of ambient endomorphisms while the norm had rectangular type `F → E`.
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

/-- The interval/exterior residual `sin 2 Theta` theorem for an isometric trial
map.  This is the complete rectangular UI-norm family obtained from the sharp
single-angle residual theorem and `sin (2 t) <= 2 sin t`. -/
theorem sinTwoTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hMspec : PointSpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : PointSpectrumIn A Uᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  have hdouble := sinTwoThetaEmbedding_uiNorm_le_two_mul N U X
  have hsingle := sinTheta_residual_le N hA hU X hM hδ hMspec hAspec
  calc
    δ * N (sinTwoThetaEmbedding U X)
        ≤ δ * (2 * N (sinThetaEmbedding U X)) :=
      mul_le_mul_of_nonneg_left hdouble hδ.le
    _ = 2 * (δ * N (sinThetaEmbedding U X)) := by ring
    _ ≤ 2 * N (residual A X M) :=
      mul_le_mul_of_nonneg_left hsingle (by positivity)

/-- Ordered half-line residual `sin 2 Theta` theorem. -/
theorem sinTwoTheta_residual_le_of_orderedGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  have hdouble := sinTwoThetaEmbedding_uiNorm_le_two_mul N U X
  have hsingle := sinTheta_residual_le_of_orderedGap N hA hU X hM hδ hgap
  calc
    δ * N (sinTwoThetaEmbedding U X)
        ≤ δ * (2 * N (sinThetaEmbedding U X)) :=
      mul_le_mul_of_nonneg_left hdouble hδ.le
    _ = 2 * (δ * N (sinThetaEmbedding U X)) := by ring
    _ ≤ 2 * N (residual A X M) :=
      mul_le_mul_of_nonneg_left hsingle (by positivity)

/-- General separated-spectrum residual form.  The single-angle `pi / 2`
Sylvester loss becomes the expected factor `pi` after the elementary
`sin (2 t) <= 2 sin t` comparison. -/
theorem sinTwoTheta_residual_le_of_spectralDistance
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : PointSpectraSeparated M ⊤ A Uᗮ δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤
      Real.pi * N (residual A X M) := by
  have hdouble := sinTwoThetaEmbedding_uiNorm_le_two_mul N U X
  have hsingle := sinTheta_residual_le_of_spectralDistance
    N hA hU X hM hδ hgap
  calc
    δ * N (sinTwoThetaEmbedding U X)
        ≤ δ * (2 * N (sinThetaEmbedding U X)) :=
      mul_le_mul_of_nonneg_left hdouble hδ.le
    _ = 2 * (δ * N (sinThetaEmbedding U X)) := by ring
    _ ≤ 2 * ((Real.pi / 2) * N (residual A X M)) :=
      mul_le_mul_of_nonneg_left hsingle (by positivity)
    _ = Real.pi * N (residual A X M) := by ring

end DavisKahan.FiniteDimensional
end TauCeti
