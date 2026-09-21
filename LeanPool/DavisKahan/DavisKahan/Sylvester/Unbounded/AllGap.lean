/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.Gap
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.IntervalExterior
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.OrderedHalfLine
import LeanPool.DavisKahan.DavisKahan.Sylvester.CutoffInterface
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedEngineDirect
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Spectral all-gap unbounded Sylvester theorem

This module states the source-facing all-gap predicate entirely through the
genuine spectrum.  It covers the interval/exterior configuration and both
ordered half-line configurations.  The capstone converts the ordered spectral
containments to form bounds and then calls the direct interface-parametric
finite-Ky-Fan engine, instantiated by the native spectral cutoffs.  Those
cutoffs came from the vendored Spectra package until it was retired on
2026-07-29.

The file is intentionally independent of the continuation and Section 8 graph
selection developments.
-/

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

namespace TauCeti
namespace DavisKahan
namespace Sylvester

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- All three source gap configurations, each stated as a containment of the
Spectra spectrum -- the form Davis--Kahan 1970 uses.

`FormBoundedSylvesterGap` states the two ordered configurations as operator-form
bounds instead; it implies this predicate, and no converse is proved. -/
inductive SpectralSylvesterGap
    (A : E →ₗ.[ℂ] E) (B : F →ₗ.[ℂ] F)
    (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : SpectralIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆
        Set.Ici (c + δ))
      (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B ⊆
        Set.Iic c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆
        Set.Iic c)
      (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B ⊆
        Set.Ici (c + δ))

/-- Source-facing Theorem 5.2 wrapper with spectral hypotheses in every
branch. -/
theorem davisKahan1970_sylvester_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : SpectralSylvesterGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge C := by
  cases hgap with
  | intervalExterior hβα hgap =>
      rcases hgap with hgap | hgap
      · exact unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
          N.toSymmetricOperatorIdealFamily hA hB hβα hδ
            hgap.1 hgap.2 hEq hC
      · exact unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
          N.toSymmetricOperatorIdealFamily hA hB hβα hδ
            hgap.2 hgap.1 hEq hC
  | leftAboveRightBelow c hAspec hBspec =>
      exact OrderedSylvesterEngine.lowerUpper
        canonicalOrderedSylvesterEngine N hA hB hδ
          (semiboundedBelow_of_spectrum_subset_Ici A hA hAspec)
          (semiboundedAbove_of_spectrum_subset_Iic B hB hBspec)
          hEq hC
  | leftBelowRightAbove c hAspec hBspec =>
      exact OrderedSylvesterEngine.upperLower
        canonicalOrderedSylvesterEngine N hA hB hδ
          (semiboundedAbove_of_spectrum_subset_Iic A hA hAspec)
          (semiboundedBelow_of_spectrum_subset_Ici B hB hBspec)
          hEq hC

end Sylvester
end DavisKahan
end TauCeti
