/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.Core
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.IntervalExterior
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Interval Exterior -/

open TauCeti.DavisKahan.Sylvester

/-!
# Source-shaped finite-interval unbounded sine-theta theorem

This module assembles the domain-aware residual identity, the spectral
interval/exterior Sylvester estimate, lower-frame normalization, and exact-angle
identification.  It deliberately bypasses the older abstract unbounded spectral
facade, whose ordered half-line branch still depends on spectral-cutoff work.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Generalized finite-interval unbounded sine-theta theorem at ideal-gauge
scope, using Spectra spectrum hypotheses and no ordered half-line dependency. -/
theorem generalizedSinTheta_unbounded_of_spectralIntervalExteriorGap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hF₁ : IsometricEmbedding D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : SpectralIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gaugeReal (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.gaugeReal D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N D hF₁ hR
  have hRaw : N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gaugeReal (D.X.adjoint ∘L D.F₁) ≤
        N.gaugeReal (-(D.residual.adjoint ∘L D.F₁)) := by
    rcases hgap with hgap | hgap
    · exact unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
        N hA₀ hΛ₁ hβα hδ hgap.1 hgap.2 hEq hC.1
    · exact unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
        N hA₀ hΛ₁ hβα hδ hgap.2 hgap.1 hEq hC.1
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N D.X D.F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gaugeReal (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * N.gaugeReal (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * N.gaugeReal (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gaugeReal (-(D.residual.adjoint ∘L D.F₁)) := hRaw.2
    _ ≤ N.gaugeReal D.residual := hC.2

/-- Raw partial-map form of the interval/exterior unbounded sine-theta bound.
The conversion to the historical bundle is confined to the current Spectra
Sylvester boundary. -/
theorem generalizedSinTheta_unbounded_of_intervalExteriorGap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hF₁ : IsometricEmbedding D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : SpectralIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gaugeReal (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.gaugeReal D.residual := by
  apply generalizedSinTheta_unbounded_of_spectralIntervalExteriorGap
    N D hA hA₀ hΛ₁ hF₁ hβα hδ hε hframe
  · exact hgap
  · exact hR

/-- Raw exact directed-angle form of the interval/exterior sine-theta bound. -/
theorem generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : SpectralIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.gaugeReal (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.gaugeReal D.residual := by
  have hBlock := generalizedSinTheta_unbounded_of_intervalExteriorGap
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hβα hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

/-- Raw partial-map isometric specialization of the interval/exterior
endpoint, derived from the raw lower-frame theorem at frame bound one. -/
theorem sinTheta_unbounded_exact_of_intervalExteriorGap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : SpectralIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gaugeReal
        ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gaugeReal D.residual := by
  have hGeneral := generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
    N D F₀ hA hA₀ hΛ₁ hdecomp hβα hδ zero_lt_one
      (lowerFrameBound_one_of_isometry hX) hgap hR
  rw [directedSinThetaOperator_eq_of_isometry D.X F₀ hX] at hGeneral
  simpa using hGeneral

end ExactSinTheta
end DavisKahan
end TauCeti
