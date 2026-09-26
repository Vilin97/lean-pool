/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedEngine
public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedCutoff

/-!
# Direct genuine ordered Sylvester engine

This leaf instantiates the interface-parametric ordered cutoff proof with the
direct vendored-Spectra cutoff and bounded truncation implementations.
-/

@[expose] public section

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

namespace TauCeti
namespace DavisKahan
namespace Sylvester

universe v

/-- Direct lower-left/upper-right ordered branch. -/
theorem directOrderedSylvesterEngine_lowerUpper
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : FanDominantIdealFamily (𝕜 := ℂ))
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℂ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge R := by
  exact unbounded_sylvester_mem_and_gauge_le_direct
    (N := N) (A := A) (B := B) (X := X) (C := R) (c := c) (δ := δ)
    hA hB
    (spectraSpectralCutoffInterface A hA)
    (spectraBoundedTruncationInterface A hA)
    (spectraSpectralCutoffInterface B hB)
    (spectraBoundedTruncationInterface B hB)
    hδ hAc hBc hEq hR

/-- Direct upper-left/lower-right ordered branch. -/
theorem directOrderedSylvesterEngine_upperLower
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : FanDominantIdealFamily (𝕜 := ℂ))
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℂ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedAbove A c)
    (hBc : TauCeti.LinearPMap.SemiboundedBelow B (c + δ))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge R := by
  exact unbounded_sylvester_mem_and_gauge_le_direct_swapped
    (N := N) (A := A) (B := B) (X := X) (C := R) (c := c) (δ := δ)
    hA hB
    (spectraSpectralCutoffInterface A hA)
    (spectraBoundedTruncationInterface A hA)
    (spectraSpectralCutoffInterface B hB)
    (spectraBoundedTruncationInterface B hB)
    hδ hAc hBc hEq hR

/-- Direct implementation of both ordered orientations. -/
theorem directOrderedSylvesterEngine :
    OrderedSylvesterEngine where
  lowerUpper := directOrderedSylvesterEngine_lowerUpper
  upperLower := directOrderedSylvesterEngine_upperLower

/-- Canonical ordered engine used by the genuine all-gap capstone. -/
theorem canonicalOrderedSylvesterEngine :
    OrderedSylvesterEngine :=
  directOrderedSylvesterEngine

end Sylvester
end DavisKahan
end TauCeti
