/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Bounded.Core
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView

/-!
# Scalar-generic lower-frame transport from explicit polar data

The analytic existence proof for lower-frame polar data may depend on the
scalar field.  Once a `LowerFramePolarData` package is available, however, all
factorization, ideal transport, and exact-angle arguments are purely Hilbert
space algebra.  This file records that scalar-generic layer explicitly.

## `Generic` means field-independent, not stronger

**This file proves no existence theorem.** It is the third of three
frame-factorization modules and the only one that never asks what the scalar
field is:

* `DavisKahan/SinTheta/FrameFactorization.lean` declares
  `structure LowerFramePolarData` and proves it inhabited over `ℂ`;
* `DavisKahan/SinTheta/Real/FrameFactorization.lean` proves it inhabited over
  `ℝ`, by complexification and descent;
* this file takes a package as given and derives the factorization, the ideal
  transport and the exact-angle arguments — all of which are pure Hilbert-space
  algebra, hence `𝕜`-generic.

So `Generic` names the *layer*, not a stronger theorem: a reader who wants "the
general existence result" wants one of the other two, chosen by field. The name
was recorded as misleading by lane DK-FRAME (2026-07-30) and kept, because a
rename would repoint imports for a wording problem this paragraph fixes.

-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The normalized trial isometry associated with an explicit polar package. -/
def frameIsometryOfPolarData
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε) : F →L[𝕜] E :=
  X ∘L P.invSqrt

/-- The complementary overlap block associated with explicit polar data. -/
def sinThetaBlockOfPolarData
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε)
    (F₁ : G →L[𝕜] E) : G →L[𝕜] F :=
  (frameIsometryOfPolarData P).adjoint ∘L F₁

/-- The full directed sine operator associated with explicit polar data. -/
def directedSinThetaOperatorOfPolarData
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε)
    (F₀ : H →L[𝕜] E) : F →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L
    frameIsometryOfPolarData P

/-- The normalized factor from explicit polar data is an isometry. -/
theorem frameIsometryOfPolarData_isometry
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε) :
    IsometricEmbedding (frameIsometryOfPolarData P) := by
  simpa [frameIsometryOfPolarData] using P.normalized_isometry

/-- Explicit polar data factorizes the trial map. -/
theorem frameFactorizationOfPolarData
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε) :
    X = frameIsometryOfPolarData P ∘L P.sqrt := by
  simpa [frameIsometryOfPolarData] using P.factorization

/-- The normalized factor has the same range as the original trial map. -/
theorem range_frameIsometryOfPolarData_eq_range
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε) :
    LinearMap.range (frameIsometryOfPolarData P).toLinearMap =
      LinearMap.range X.toLinearMap := by
  simpa [frameIsometryOfPolarData] using P.range_normalized

/-- For isometric input, explicit polar data normalizes to the original map. -/
theorem frameIsometryOfPolarData_eq_of_isometry
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε)
    (hIso : IsometricEmbedding X) :
    frameIsometryOfPolarData P = X := by
  unfold frameIsometryOfPolarData
  rw [P.invSqrt_eq_id_of_isometry hIso]
  simp

/-- Lower-frame ideal transport requires only the explicit inverse square root
and its sharp norm estimate. -/
theorem lowerFrame_sinThetaBlockOfPolarData_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε)
    (F₁ : G →L[𝕜] E)
    (hRaw : N.Mem (X.adjoint ∘L F₁)) :
    N.Mem (sinThetaBlockOfPolarData P F₁) ∧
      ε * N.gaugeReal (sinThetaBlockOfPolarData P F₁)
        ≤ N.gaugeReal (X.adjoint ∘L F₁) := by
  have hBlock :
      sinThetaBlockOfPolarData P F₁ =
        P.invSqrt.adjoint ∘L (X.adjoint ∘L F₁) := by
    unfold sinThetaBlockOfPolarData frameIsometryOfPolarData
    rw [ContinuousLinearMap.adjoint_comp]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hMem :
      N.Mem (P.invSqrt.adjoint ∘L (X.adjoint ∘L F₁)) :=
    N.comp_left_mem P.invSqrt.adjoint hRaw
  have hnorm : ‖P.invSqrt.adjoint‖ ≤ ε⁻¹ := by
    simpa using P.invSqrt_norm_le
  have hgauge :
      N.gaugeReal (sinThetaBlockOfPolarData P F₁) ≤
        ε⁻¹ * N.gaugeReal (X.adjoint ∘L F₁) := by
    rw [hBlock]
    exact (N.gaugeReal_comp_left_le_mul P.invSqrt.adjoint hRaw).trans
      (mul_le_mul_of_nonneg_right hnorm (N.gaugeReal_nonneg hRaw))
  refine ⟨hBlock ▸ hMem, ?_⟩
  calc
    ε * N.gaugeReal (sinThetaBlockOfPolarData P F₁)
        ≤ ε * (ε⁻¹ * N.gaugeReal (X.adjoint ∘L F₁)) :=
      mul_le_mul_of_nonneg_left hgauge hε.le
    _ = N.gaugeReal (X.adjoint ∘L F₁) := by
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]

/-- Under a complete exact-space decomposition, the explicit complementary
block and explicit directed sine operator have identical ideal gauge. -/
theorem sinThetaBlockOfPolarData_mem_and_gauge_eq_directed
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    
    {X : F →L[𝕜] E} {ε : ℝ}
    {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε)
    (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hblock : N.Mem (sinThetaBlockOfPolarData P F₁)) :
    N.Mem (directedSinThetaOperatorOfPolarData P F₀) ∧
      N.gaugeReal (directedSinThetaOperatorOfPolarData P F₀) =
        N.gaugeReal (sinThetaBlockOfPolarData P F₁) := by
  have hComplement :
      ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint =
        F₁ ∘L F₁.adjoint := by
    rw [← hdecomp.projection_sum]
    abel
  have hDirected :
      directedSinThetaOperatorOfPolarData P F₀ =
        F₁ ∘L (sinThetaBlockOfPolarData P F₁).adjoint := by
    unfold directedSinThetaOperatorOfPolarData sinThetaBlockOfPolarData
    rw [hComplement, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hblockAdj : N.Mem (sinThetaBlockOfPolarData P F₁).adjoint :=
    N.adjoint_mem hblock
  have hDirectedMem :
      N.Mem (directedSinThetaOperatorOfPolarData P F₀) := by
    rw [hDirected]
    exact N.comp_left_mem F₁ hblockAdj
  have hF₁Norm : ‖F₁‖ ≤ 1 :=
    opNorm_le_one_of_isometry hdecomp.isometry₁
  have hForward :
      N.gaugeReal (directedSinThetaOperatorOfPolarData P F₀) ≤
        N.gaugeReal (sinThetaBlockOfPolarData P F₁) := by
    rw [hDirected]
    calc
      N.gaugeReal (F₁ ∘L (sinThetaBlockOfPolarData P F₁).adjoint)
          ≤ N.gaugeReal (sinThetaBlockOfPolarData P F₁).adjoint :=
        N.gaugeReal_comp_left_le F₁ hblockAdj hF₁Norm
      _ = N.gaugeReal (sinThetaBlockOfPolarData P F₁) :=
        N.gaugeReal_adjoint hblock
  have hF₁LeftInverse :
      F₁.adjoint ∘L F₁ = ContinuousLinearMap.id 𝕜 G :=
    adjoint_comp_self_eq_id_of_isometry hdecomp.isometry₁
  have hRecover :
      (sinThetaBlockOfPolarData P F₁).adjoint =
        F₁.adjoint ∘L directedSinThetaOperatorOfPolarData P F₀ := by
    calc
      (sinThetaBlockOfPolarData P F₁).adjoint =
          ContinuousLinearMap.id 𝕜 G ∘L
            (sinThetaBlockOfPolarData P F₁).adjoint := by simp
      _ = (F₁.adjoint ∘L F₁) ∘L
            (sinThetaBlockOfPolarData P F₁).adjoint := by
          rw [hF₁LeftInverse]
      _ = F₁.adjoint ∘L
            (F₁ ∘L (sinThetaBlockOfPolarData P F₁).adjoint) :=
          ContinuousLinearMap.comp_assoc _ _ _
      _ = F₁.adjoint ∘L directedSinThetaOperatorOfPolarData P F₀ := by
          rw [hDirected]
  have hF₁AdjNorm : ‖F₁.adjoint‖ ≤ 1 := by
    simpa using hF₁Norm
  have hReverse :
      N.gaugeReal (sinThetaBlockOfPolarData P F₁) ≤
        N.gaugeReal (directedSinThetaOperatorOfPolarData P F₀) := by
    rw [← N.gaugeReal_adjoint hblock, hRecover]
    exact N.gaugeReal_comp_left_le F₁.adjoint hDirectedMem hF₁AdjNorm
  exact ⟨hDirectedMem, le_antisymm hForward hReverse⟩

/-- Scalar-generic generalized complementary-block theorem once explicit polar
data and a raw Sylvester estimate are supplied. -/
theorem generalizedSinTheta_of_polarData_of_sylvesterBound
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {X : F →L[𝕜] E} {F₁ : G →L[𝕜] E} {C : G →L[𝕜] F}
    {ε δ : ℝ} {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε)
    (hδ : 0 < δ)
    (hRaw : N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gaugeReal (X.adjoint ∘L F₁) ≤ N.gaugeReal C) :
    N.Mem (sinThetaBlockOfPolarData P F₁) ∧
      δ * ε * N.gaugeReal (sinThetaBlockOfPolarData P F₁) ≤ N.gaugeReal C := by
  have hFrame := lowerFrame_sinThetaBlockOfPolarData_mem_and_gauge_le
    N P F₁ hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gaugeReal (sinThetaBlockOfPolarData P F₁) =
        δ * (ε * N.gaugeReal (sinThetaBlockOfPolarData P F₁)) := by ring
    _ ≤ δ * N.gaugeReal (X.adjoint ∘L F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gaugeReal C := hRaw.2

/-- Exact directed-angle version of the scalar-generic lower-frame transport. -/
theorem generalizedSinTheta_exact_of_polarData_of_sylvesterBound
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {X : F →L[𝕜] E} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}
    {C : G →L[𝕜] F} {ε δ : ℝ} {hX : LowerFrameBound X ε} {hε : 0 < ε}
    (P : LowerFramePolarData X ε hX hε)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hδ : 0 < δ)
    (hRaw : N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gaugeReal (X.adjoint ∘L F₁) ≤ N.gaugeReal C) :
    N.Mem (directedSinThetaOperatorOfPolarData P F₀) ∧
      δ * ε * N.gaugeReal (directedSinThetaOperatorOfPolarData P F₀) ≤
        N.gaugeReal C := by
  have hBlock := generalizedSinTheta_of_polarData_of_sylvesterBound N P hδ hRaw
  have hAngle := sinThetaBlockOfPolarData_mem_and_gauge_eq_directed
    N P F₀ F₁ hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end

end ExactSinTheta
end DavisKahan
end TauCeti
