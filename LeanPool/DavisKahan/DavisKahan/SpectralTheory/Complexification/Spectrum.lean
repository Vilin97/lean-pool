/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.Spectrum
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# The spectrum survives complexification

The scalar-level spectrum transport now lives canonically in
`ForTauCeti.Analysis.InnerProductSpace.Complexification.Spectrum`.  This module keeps only the
Davis--Kahan consequences stated in terms of `Foundation.realSpectrum` and
`Foundation.SpectraSeparated`.

The local `complexify_mul` and `complexify_one` lemmas remain because this Davis--Kahan
complexification namespace has existing operator-algebra callers that use those spellings.  The
invertibility and native spectrum theorems are not repeated here.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Foundation
namespace RealComplexification

open TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Complexification is multiplicative for operator composition written as ring multiplication. -/
@[simp] theorem complexify_mul (S T : E →L[ℝ] E) :
    complexify (S * T) = complexify S * complexify T := by
  simpa only [ContinuousLinearMap.mul_def] using complexify_comp S T

/-- Complexification is unital. -/
@[simp] theorem complexify_one :
    complexify (1 : E →L[ℝ] E) = 1 :=
  complexify_id

/-- `Foundation.realSpectrum` is invariant under complexification. -/
theorem realSpectrum_complexify (T : E →L[ℝ] E) :
    realSpectrum (complexify T) = realSpectrum T := by
  ext r
  change ((r : ℂ) ∈ spectrum ℂ (complexify T)) ↔ r ∈ spectrum ℝ T
  exact TauCeti.RealComplexification.mem_spectrum_complexify_iff T r

/-- **Full-space spectral separation survives complexification.**

`SpectraSeparated _ ⊤ _ ⊤` is a statement about the two real spectra
(`spectraSeparated_top_iff`), and `realSpectrum_complexify` says complexification does not
move either of them, so the separation transports verbatim with the same gap. -/
theorem spectraSeparated_top_complexify
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : E →L[ℝ] E} {B : F →L[ℝ] F} {d : ℝ}
    (hsep : SpectraSeparated A (⊤ : Submodule ℝ E) B (⊤ : Submodule ℝ F) d) :
    SpectraSeparated (complexify A) (⊤ : Submodule ℂ (RealComplexification E))
      (complexify B) (⊤ : Submodule ℂ (RealComplexification F)) d := by
  rw [spectraSeparated_top_iff] at hsep ⊢
  intro a ha b hb
  rw [realSpectrum_complexify] at ha
  rw [realSpectrum_complexify] at hb
  exact hsep a ha b hb

end RealComplexification
end Foundation
end DavisKahan
end TauCeti
