/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.Core
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.IntervalExterior
public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.AllGap
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # All Gap -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Spectral all-gap unbounded sine-theta theorem

This leaf exposes the complete generalized and isometric unbounded sine-theta
statements with all three gap configurations phrased through the Spectra
Spectra spectrum.  It reuses the domain-aware residual identity, lower-frame
normalization, and exact-angle identification already present in the canonical
unbounded development.

No continuation, graph-selection, Riccati, Section 8, aggregate, or public
facade file is imported or modified here.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Generalized complementary-block theorem with a spectral all-gap
hypothesis. -/
theorem generalizedSinTheta_unbounded_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : SpectralSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gauge
          (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toSymmetricOperatorIdealFamily D hF₁ hR
  have hRaw := davisKahan1970_sylvester_of_spectrumGap
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N.toSymmetricOperatorIdealFamily D.X D.F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * N.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hRaw.2
    _ ≤ N.gauge D.residual := hC.2

/-- Exact directed-angle form of the spectral all-gap generalized theorem. -/
theorem generalizedSinTheta_unbounded_exact_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : SpectralSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.gauge
          (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.gauge D.residual := by
  have hBlock := generalizedSinTheta_unbounded_of_spectrumGap
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N.toSymmetricOperatorIdealFamily D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [FanDominantIdealFamily.toSymmetric_gaugeReal] at hAngle
  rw [hAngle.2]
  exact hBlock.2

/-- Exact isometric specialization of the spectral all-gap theorem. -/
theorem sinTheta_unbounded_exact_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectralSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
          ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toSymmetricOperatorIdealFamily D hdecomp.isometry₁ hR
  have hRaw := davisKahan1970_sylvester_of_spectrumGap
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toSymmetricOperatorIdealFamily D.X F₀ D.F₁ hX hdecomp hRaw.1
  refine ⟨hAngle.1, ?_⟩
  rw [FanDominantIdealFamily.toSymmetric_gaugeReal] at hAngle
  rw [hAngle.2]
  exact hRaw.2.trans hC.2


end ExactSinTheta
end DavisKahan
end TauCeti
