/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.SpectralBridge
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Bounded.Core

/-! # Bounded -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded `sin Θ` endpoints resting on the legacy bridge estimate

The problem data and angle identification now live in
`DavisKahan.SinTheta.Bounded.Core`.  The endpoints below are stated through the
legacy interval/exterior estimate of the bounded spectral bridge, which is still
an open obligation.  The production route to the same endpoints is the native
bounded self-adjoint spectral calculus under `DavisKahan/SpectralTheory/`; the
vendored Spectra package this note used to name was retired on 2026-07-29.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

section Generic

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The raw complementary block obeys the sharp interval/exterior estimate. -/
theorem complementaryBlock_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hF₁ : IsometricEmbedding F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gaugeReal (X.adjoint ∘L F₁)
        ≤ N.gaugeReal (generalResidual A X A₀) := by
  have hEq := complementary_sylvester_equation
    (X := X) (F₁ := F₁) hA hA₀ hΛ₁ hIntertwine
  have hAdj : N.Mem (generalResidual A X A₀).adjoint := N.adjoint_mem hR
  have hComp : N.Mem ((generalResidual A X A₀).adjoint ∘L F₁) :=
    N.comp_right_mem F₁ hAdj
  have hC : N.Mem (-((generalResidual A X A₀).adjoint ∘L F₁)) :=
    N.neg_mem hComp
  have hRaw := sylvester_mem_and_gauge_le_of_intervalExteriorGap
    N hA₀ hΛ₁ hβα hδ hgap hEq hC
  refine ⟨hRaw.1, hRaw.2.trans ?_⟩
  calc
    N.gaugeReal (-((generalResidual A X A₀).adjoint ∘L F₁))
        = N.gaugeReal ((generalResidual A X A₀).adjoint ∘L F₁) :=
          N.gaugeReal_neg hComp
    _ ≤ N.gaugeReal (generalResidual A X A₀).adjoint :=
      N.gaugeReal_comp_right_le F₁ hAdj (opNorm_le_one_of_isometry hF₁)
    _ = N.gaugeReal (generalResidual A X A₀) := N.gaugeReal_adjoint hR

/-- Isometric complementary-block specialization of the bounded theorem. -/
theorem sinTheta_bounded
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (_hX : IsometricEmbedding X) (hF₁ : IsometricEmbedding F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gaugeReal (X.adjoint ∘L F₁)
        ≤ N.gaugeReal (generalResidual A X A₀) := by
  exact complementaryBlock_mem_and_gauge_le
    N hA hA₀ hΛ₁ hF₁ hIntertwine hβα hδ hgap hR

end Generic

section Complex

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded generalized complementary-block theorem.  This is the analytic
core of Theorem 6.1, before identifying the block with the full directed sine
of a complete exact-space decomposition. -/
theorem generalizedSinTheta_bounded
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[ℂ] E} {A₀ : F →L[ℂ] F}
    {Λ₁ : G →L[ℂ] G} {X : F →L[ℂ] E}
    {F₁ : G →L[ℂ] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hF₁ : IsometricEmbedding F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (sinThetaBlock X F₁ hframe hε) ∧
      δ * ε * N.gaugeReal (sinThetaBlock X F₁ hframe hε)
        ≤ N.gaugeReal (generalResidual A X A₀) := by
  have hRaw := complementaryBlock_mem_and_gauge_le
    N hA hA₀ hΛ₁ hF₁ hIntertwine hβα hδ hgap hR
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N X F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gaugeReal (sinThetaBlock X F₁ hframe hε)
        = δ * (ε * N.gaugeReal (sinThetaBlock X F₁ hframe hε)) := by ring
    _ ≤ δ * N.gaugeReal (X.adjoint ∘L F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gaugeReal (generalResidual A X A₀) := hRaw.2

/-- Exact bounded infinite-dimensional Davis--Kahan Theorem 6.1, expressed in
terms of the full directed sine operator rather than an arbitrary invariant
complementary block. -/
theorem generalizedSinTheta_bounded_exact
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[ℂ] E} {A₀ : F →L[ℂ] F}
    {Λ₁ : G →L[ℂ] G} {X : F →L[ℂ] E}
    {F₀ : H →L[ℂ] E} {F₁ : G →L[ℂ] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (directedSinThetaOperator X F₀ hframe hε) ∧
      δ * ε * N.gaugeReal (directedSinThetaOperator X F₀ hframe hε)
        ≤ N.gaugeReal (generalResidual A X A₀) := by
  have hBlock := generalizedSinTheta_bounded
    N hA hA₀ hΛ₁ hdecomp.isometry₁ hIntertwine
      hβα hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N X F₀ F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end Complex

section GenericExact

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Exact isometric headline specialization of the bounded theorem. -/
theorem sinTheta_bounded_exact
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hX : IsometricEmbedding X)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X) ∧
      δ * N.gaugeReal
        ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X)
        ≤ N.gaugeReal (generalResidual A X A₀) := by
  have hBlock := sinTheta_bounded
    N hA hA₀ hΛ₁ hX hdecomp.isometry₁ hIntertwine
      hβα hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N X F₀ F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end GenericExact

end ExactSinTheta
end DavisKahan
end TauCeti
