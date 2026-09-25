/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.AllGap
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.RealSpectrum

/-!
# Form-bounded gap hypotheses discharge the spectral ones

`Sylvester/Gap.lean` states its gap over `PartialMap.realSpectrum` and
packages ordered form bounds together with interval/exterior spectral
separation.  `SpectralSylvesterGap` instead states all three configurations
spectrally, using Spectra for the spectral branch and the direct cutoff engine
for the ordered branches.  This file connects the two surfaces without importing
any theorem from the obsolete cutoff facade.

**Which direction is available, exactly.**  `formBoundedSylvesterGap_of_spectral`
transports the spectral gap to the form-bounded one in **every** configuration:
the ordered branches by `semiboundedBelow_of_spectrum_subset_Ici` and its mirror
(`SpectralTheory/OrderedHalfLine.lean`, the half-line form of the spectral
theorem), the interval branch by `realSpectrum_eq_spectraSpectrum`.  Going back,
only `SpectralSylvesterGap.intervalExterior_of_formBounded` is proved — turning a
form bound into a spectral containment is the half of the spectral theorem this
tree does not have.

So `FormBoundedSylvesterGap` is the **weaker** hypothesis and
`davisKahan1970_sylvester_complex`, stated over it, is the stronger theorem;
`davisKahan1970_sylvester_of_spectrumGap` follows from it.  Neither predicate
holds an unqualified name: they are the same mathematics stated two ways, and
each name says which way.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A `realSpectrum` interval/exterior hypothesis becomes the spectral
interval/exterior hypothesis after identifying the two spectra. -/
theorem sylvesterIntervalExteriorGap_of_realSpectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    {β α δ : ℝ}
    (hgap : RealSpectrumIntervalExteriorGap A B β α δ) :
    SpectralIntervalExteriorGap A B β α δ := by
  rcases hgap with hgap | hgap
  · left
    constructor
    · simpa only [realSpectrum_eq_spectraSpectrum] using hgap.1
    · intro lam hlam hlamSpec
      have hreal : lam ∈ TauCeti.LinearPMap.realSpectrum B := by
        simpa only [realSpectrum_eq_spectraSpectrum, Set.mem_preimage]
          using hlamSpec
      rcases hgap.2 hreal with hleft | hright
      · exact (not_lt_of_ge hleft) hlam.1
      · exact (not_lt_of_ge hright) hlam.2
  · right
    constructor
    · simpa only [realSpectrum_eq_spectraSpectrum] using hgap.1
    · intro lam hlam hlamSpec
      have hreal : lam ∈ TauCeti.LinearPMap.realSpectrum A := by
        simpa only [realSpectrum_eq_spectraSpectrum, Set.mem_preimage]
          using hlamSpec
      rcases hgap.2 hreal with hleft | hright
      · exact (not_lt_of_ge hleft) hlam.1
      · exact (not_lt_of_ge hright) hlam.2

omit [CompleteSpace E] [CompleteSpace F] in
/-- The interval/exterior constructor of the form-bounded gap embeds into the
spectral all-gap predicate.  Ordered constructors are intentionally handled by
their form bounds rather than translated into spectral containments. -/
theorem SpectralSylvesterGap.intervalExterior_of_formBounded
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    {β α δ : ℝ}
    (hβα : β ≤ α)
    (hgap : RealSpectrumIntervalExteriorGap A B β α δ) :
    SpectralSylvesterGap A B δ :=
  SpectralSylvesterGap.intervalExterior hβα
    (sylvesterIntervalExteriorGap_of_realSpectrum hgap)

/-- Admission-free complex specialization of the manuscript Section 5
Sylvester theorem.  The spectral constructor is routed through the Spectra
spectrum theorem, while the two ordered constructors retain their form-bound
hypotheses and call the direct engine verbatim. -/
theorem davisKahan1970_sylvester_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge C := by
  cases hgap with
  | intervalExterior hβα hgap =>
      exact davisKahan1970_sylvester_of_spectrumGap
        N hA hB hδ
          (SpectralSylvesterGap.intervalExterior_of_formBounded hβα hgap)
          hEq hC
  | leftAboveRightBelow c hAc hBc =>
      exact directOrderedSylvesterEngine_lowerUpper
        N hA hB hδ hAc hBc hEq hC
  | leftBelowRightAbove c hAc hBc =>
      exact directOrderedSylvesterEngine_upperLower
        N hA hB hδ hAc hBc hEq hC


omit [CompleteSpace E] [CompleteSpace F] in
/-- The spectral interval/exterior configuration is the `realSpectrum` one, since
`realSpectrum_eq_spectraSpectrum` identifies the two spectra. -/
theorem realSpectrumIntervalExteriorGap_of_spectral
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    {β α δ : ℝ}
    (hgap : SpectralIntervalExteriorGap A B β α δ) :
    RealSpectrumIntervalExteriorGap A B β α δ := by
  rcases hgap with hgap | hgap
  · left
    refine ⟨by simpa only [realSpectrum_eq_spectraSpectrum] using hgap.1, ?_⟩
    intro lam hlam
    rcases le_or_gt lam (β - δ) with h | h
    · exact Or.inl h
    rcases le_or_gt (α + δ) lam with h' | h'
    · exact Or.inr h'
    exact absurd
      (by simpa only [realSpectrum_eq_spectraSpectrum, Set.mem_preimage] using hlam)
      (hgap.2 lam ⟨h, h'⟩)
  · right
    refine ⟨by simpa only [realSpectrum_eq_spectraSpectrum] using hgap.1, ?_⟩
    intro lam hlam
    rcases le_or_gt lam (β - δ) with h | h
    · exact Or.inl h
    rcases le_or_gt (α + δ) lam with h' | h'
    · exact Or.inr h'
    exact absurd
      (by simpa only [realSpectrum_eq_spectraSpectrum, Set.mem_preimage] using hlam)
      (hgap.2 lam ⟨h, h'⟩)

/-- **The spectral gap implies the form-bounded gap, in every configuration.**

The interval/exterior branch is the spectrum identification; the two ordered
branches are `semiboundedBelow_of_spectrum_subset_Ici` and
`semiboundedAbove_of_spectrum_subset_Iic`, the half-line form of the spectral
theorem, proved in `SpectralTheory/OrderedHalfLine.lean`.

So `FormBoundedSylvesterGap` is the **weaker** hypothesis of the two, and a
theorem stated over it -- `davisKahan1970_sylvester_complex` -- is the stronger
theorem, with `davisKahan1970_sylvester_of_spectrumGap` a corollary of it.  Only
the reverse direction on the ordered branches is missing. -/
theorem formBoundedSylvesterGap_of_spectral
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ}
    (hgap : SpectralSylvesterGap A B δ) :
    FormBoundedSylvesterGap A B δ := by
  cases hgap with
  | intervalExterior hβα hgap =>
      exact .intervalExterior hβα (realSpectrumIntervalExteriorGap_of_spectral hgap)
  | leftAboveRightBelow c hAspec hBspec =>
      exact .leftAboveRightBelow c
        (semiboundedBelow_of_spectrum_subset_Ici A hA hAspec)
        (semiboundedAbove_of_spectrum_subset_Iic B hB hBspec)
  | leftBelowRightAbove c hAspec hBspec =>
      exact .leftBelowRightAbove c
        (semiboundedAbove_of_spectrum_subset_Iic A hA hAspec)
        (semiboundedBelow_of_spectrum_subset_Ici B hB hBspec)

end Sylvester
end DavisKahan
end TauCeti
