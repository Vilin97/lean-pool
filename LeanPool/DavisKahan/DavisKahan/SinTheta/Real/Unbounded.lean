/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.Core
import LeanPool.DavisKahan.DavisKahan.Sylvester.RealUnbounded

/-! # Unbounded -/

open TauCeti.DavisKahan.Sylvester

/-!
# Real unbounded sine-theta theorem

The complementary residual identity and exact-angle geometry are already
scalar-generic.  Combining them with the real unbounded Sylvester theorem gives
the full isometric sine-theta theorem over real Hilbert spaces for all three
gap configurations and every real Ky-Fan-dominant unitarily invariant
ideal family.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real isometric complementary-block theorem for the complete unbounded gap
disjunction. -/
theorem sinTheta_unbounded_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G))
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
  have hRaw := davisKahan1970_sylvester_real
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  exact ⟨hRaw.1, hRaw.2.trans hC.2⟩

/-- **Block form of the real unbounded sine-theta estimate.**  The right-hand
side is the residual block between the two coordinate spaces, before it is
contracted back to the whole residual.  The sharp directed residual
`sin 2Theta_0` estimate needs it at this stage. -/
theorem sinTheta_unbounded_real_block
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G))
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
  have hRaw := davisKahan1970_sylvester_real
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hmem : N.Mem (D.residual.adjoint ∘L D.F₁) :=
    N.toSymmetricOperatorIdealFamily.comp_right_mem D.F₁
      (N.toSymmetricOperatorIdealFamily.adjoint_mem hR)
  refine ⟨hRaw.1, hRaw.2.trans (le_of_eq ?_)⟩
  exact N.toSymmetricOperatorIdealFamily.gaugeReal_neg hmem

/-- Exact real isometric theorem in directed sine form. -/
theorem sinTheta_unbounded_exact_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℝ] E)
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
      ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hBlock := sinTheta_unbounded_real
    N D hA hA₀ hΛ₁ hX hdecomp.isometry₁ hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toSymmetricOperatorIdealFamily D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [FanDominantIdealFamily.toSymmetric_gaugeReal] at hAngle
  rw [hAngle.2]
  exact hBlock.2

end

end ExactSinTheta
end DavisKahan
end TauCeti
