/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Unbounded
import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.FrameFactorization

/-! # Generalized -/

open TauCeti.DavisKahan.Sylvester

/-!
# Real generalized unbounded sine-theta theorem

This module combines the real unbounded Sylvester theorem with the descended
real lower-frame polar package.  The result has the same three gap
configurations, sharp product constant, and arbitrary unitarily invariant
ideal family as the complex generalized theorem.
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

/-- The selected real full directed sine operator for a lower-frame trial map. -/
noncomputable def directedSinThetaOperatorReal
    (X : F →L[ℝ] E) (F₀ : H →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[ℝ] E :=
  directedSinThetaOperatorOfPolarData
    (lowerFramePolarDataReal X hX hε) F₀

/-- Complete real generalized complementary-block theorem. -/
theorem generalizedSinTheta_unbounded_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G))
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
      (sinThetaBlockReal D.X D.F₁ hframe hε) ∧
      δ * ε * N.gauge
        (sinThetaBlockReal D.X D.F₁ hframe hε)
        ≤ N.gauge D.residual := by
  let P := lowerFramePolarDataReal D.X hframe hε
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toSymmetricOperatorIdealFamily D hF₁ hR
  have hRaw := davisKahan1970_sylvester_real
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hFrame := lowerFrame_sinThetaBlockOfPolarData_mem_and_gauge_le
    N.toSymmetricOperatorIdealFamily P D.F₁ hRaw.1
  have hBlockDef :
      sinThetaBlockReal D.X D.F₁ hframe hε =
        sinThetaBlockOfPolarData P D.F₁ := rfl
  refine ⟨hBlockDef ▸ hFrame.1, ?_⟩
  rw [hBlockDef]
  calc
    δ * ε * N.gauge (sinThetaBlockOfPolarData P D.F₁) =
        δ * (ε * N.gauge (sinThetaBlockOfPolarData P D.F₁)) := by ring
    _ ≤ δ * N.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hRaw.2
    _ ≤ N.gauge D.residual := hC.2

/-- Exact real generalized theorem in full directed sine form. -/
theorem generalizedSinTheta_unbounded_exact_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℝ] E)
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
      (directedSinThetaOperatorReal D.X F₀ hframe hε) ∧
      δ * ε * N.gauge
        (directedSinThetaOperatorReal D.X F₀ hframe hε)
        ≤ N.gauge D.residual := by
  let P := lowerFramePolarDataReal D.X hframe hε
  have hBlock := generalizedSinTheta_unbounded_real
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hBlockDef :
      sinThetaBlockReal D.X D.F₁ hframe hε =
        sinThetaBlockOfPolarData P D.F₁ := rfl
  have hAngle := sinThetaBlockOfPolarData_mem_and_gauge_eq_directed
    N.toSymmetricOperatorIdealFamily P F₀ D.F₁ hdecomp (hBlockDef ▸ hBlock.1)
  have hDirectedDef :
      directedSinThetaOperatorReal D.X F₀ hframe hε =
        directedSinThetaOperatorOfPolarData P F₀ := rfl
  refine ⟨hDirectedDef ▸ hAngle.1, ?_⟩
  simp only [FanDominantIdealFamily.toSymmetric_gaugeReal] at hAngle
  rw [hDirectedDef, hAngle.2, ← hBlockDef]
  exact hBlock.2

/-- The real selected generalized theorem specializes exactly to the direct
projection formula for an isometric trial map. -/
theorem directedSinThetaOperatorReal_eq_of_isometry
    (X : F →L[ℝ] E) (F₀ : H →L[ℝ] E)
    (hX : IsometricEmbedding X) :
    directedSinThetaOperatorReal X F₀
      (lowerFrameBound_one_of_isometry hX) zero_lt_one =
      (ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L X := by
  unfold directedSinThetaOperatorReal directedSinThetaOperatorOfPolarData
  rw [frameIsometryOfPolarData_eq_of_isometry
    (lowerFramePolarDataReal X
      (lowerFrameBound_one_of_isometry hX) zero_lt_one) hX]

end

end ExactSinTheta
end DavisKahan
end TauCeti
