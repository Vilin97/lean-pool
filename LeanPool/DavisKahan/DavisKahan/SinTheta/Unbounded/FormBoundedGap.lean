/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.Core
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.FormBoundedGap

/-! # Form Bounded Gap -/

open TauCeti.DavisKahan.Sylvester

/-!
# Sine-theta endpoints over the form-bounded gap

The source-correspondence problem records take `FormBoundedSylvesterGap`.  This
module keeps those statements intact while routing their complex proofs through
the direct spectral Sylvester engine.  It is deliberately above both the
Sylvester and sine-theta implementation layers so that the transport route does
not enter either foundational import cone.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

section Complex

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complex isometric complementary-block theorem routed through the direct
manuscript-shaped Sylvester engine. -/
theorem sinTheta_unbounded_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (_hX : IsometricEmbedding D.X)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toSymmetricOperatorIdealFamily D hF₁ hR
  have hRaw := davisKahan1970_sylvester_complex
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  exact ⟨hRaw.1, hRaw.2.trans hC.2⟩

/-- **Block form of the complex unbounded sine-theta estimate at the full
form-bounded gap.**  The right-hand side is the residual block between the two
coordinate spaces, before it is contracted back to the whole residual.  The
sharp directed residual `sin 2Theta_0` estimate needs it at this stage.

The complex mirror of `sinTheta_unbounded_real_block`.  Both route the same
block identity through their field's Sylvester engine; only the engine differs.
-/
theorem sinTheta_unbounded_complex_block
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁)
        ≤ N.gauge (D.residual.adjoint ∘L D.F₁) := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toSymmetricOperatorIdealFamily D hF₁ hR
  have hRaw := davisKahan1970_sylvester_complex
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hmem : N.Mem (D.residual.adjoint ∘L D.F₁) :=
    N.toSymmetricOperatorIdealFamily.comp_right_mem D.F₁
      (N.toSymmetricOperatorIdealFamily.adjoint_mem hR)
  refine ⟨hRaw.1, hRaw.2.trans (le_of_eq ?_)⟩
  exact N.toSymmetricOperatorIdealFamily.gaugeReal_neg hmem

/-- Exact complex isometric theorem with the directed sine operator used by
the manuscript surface. -/
theorem sinTheta_unbounded_exact_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
      ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hBlock := sinTheta_unbounded_complex
    N D hA hA₀ hΛ₁ hX hdecomp.isometry₁ hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toSymmetricOperatorIdealFamily D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [FanDominantIdealFamily.toSymmetric_gaugeReal] at hAngle
  rw [hAngle.2]
  exact hBlock.2

/-- Complex generalized complementary-block theorem for all three manuscript
gap configurations. -/
theorem generalizedSinTheta_unbounded_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gauge
          (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toSymmetricOperatorIdealFamily D hF₁ hR
  have hRaw := davisKahan1970_sylvester_complex
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

/-- Exact complex generalized theorem for all three manuscript gap
configurations. -/
theorem generalizedSinTheta_unbounded_exact_complex
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
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.gauge
          (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.gauge D.residual := by
  have hBlock := generalizedSinTheta_unbounded_complex
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N.toSymmetricOperatorIdealFamily D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [FanDominantIdealFamily.toSymmetric_gaugeReal] at hAngle
  rw [hAngle.2]
  exact hBlock.2

end Complex

end ExactSinTheta
end DavisKahan
end TauCeti
