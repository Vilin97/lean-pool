/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-!
# Source-norm transport across different coordinate spaces

The paper permits `sin Theta_0` to be represented on any pair of Hilbert
coordinate spaces having the prescribed singular-value sequence.  This module
sits above both the pure approximation-number relation and the paper norm, so
that the lower singular-data layer remains independent of the norm package.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

namespace SameApproximationSingularSequence

/-- Equal complete singular data gives equal source prefix gauges. -/
theorem prefixGauge_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (N : SymmetricNormingFunction)
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) (n : ℕ) :
    N.prefixGauge n A = N.prefixGauge n B := by
  unfold SymmetricNormingFunction.prefixGauge
  congr 1
  funext i
  exact h i

/-- Equal complete singular data gives equal source extended values. -/
theorem normingExtendedGauge_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (N : SymmetricNormingFunction)
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    N.extendedGauge A = N.extendedGauge B := by
  unfold SymmetricNormingFunction.extendedGauge
  apply iSup_congr
  intro n
  rw [h.prefixGauge_eq N n]

/-- Equal complete singular data gives equivalent membership and equal source
norms, even across different coordinate spaces. -/
theorem normingMem_iff_and_gauge_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (N : SymmetricNormingFunction)
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    (N.Mem A ↔ N.Mem B) ∧ N.gauge A = N.gauge B := by
  have heq := h.normingExtendedGauge_eq N
  exact ⟨by simp [SymmetricNormingFunction.Mem, heq],
    congrArg ENNReal.toReal heq⟩

end SameApproximationSingularSequence

namespace SinThetaRepresentativeAcross

/-- Source norm membership and value transport across arbitrary coordinate
spaces. -/
theorem normingMem_iff_and_gauge_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E F E₀ F₀ : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    (N : SymmetricNormingFunction) {canonical : E →L[𝕜] F}
    (S : SinThetaRepresentativeAcross (E₀ := E₀) (F₀ := F₀) canonical) :
    (N.Mem S.operator ↔ N.Mem canonical) ∧
      N.gauge S.operator = N.gauge canonical :=
  S.same_singular_sequence.normingMem_iff_and_gauge_eq N

end SinThetaRepresentativeAcross

end ExactSinTheta
end DavisKahan
end TauCeti
