/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedGraphAcute
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngleSpectrum
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Spectrum transport for bounded Riccati diagonalization

This leaf module records the spectral consequence of the bounded graph
rotation without yet analyzing the spectrum of a block-diagonal operator.

A pair of continuous linear maps which are two-sided inverses determines a
continuous linear equivalence.  Conjugation through that equivalence is an
algebra equivalence, so it preserves the complex spectrum.  Applying this to
the canonical bounded Riccati graph rotation shows that the original block
operator and the diagonalized block operator have exactly the same complex
spectrum.

The later block-spectrum module can therefore focus only on proving that the
spectrum of `blockDiagonalOperator D0 D1` is the union of the spectra of its
two diagonal blocks.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Two-sided continuous-linear conjugation preserves the complex spectrum.

The maps are supplied separately because the bounded Riccati diagonalization
API naturally returns the direct rotation and its inverse as continuous linear
maps together with the two composition identities. -/
theorem spectrum_eq_of_inverse_conjugation
    (T S W Winv : E →L[ℂ] E)
    (hleft : Winv ∘L W = ContinuousLinearMap.id ℂ E)
    (hright : W ∘L Winv = ContinuousLinearMap.id ℂ E)
    (hconj : Winv ∘L T ∘L W = S) :
    spectrum ℂ T = spectrum ℂ S := by
  let e : E ≃L[ℂ] E :=
    ContinuousLinearEquiv.equivOfInverse' Winv W hleft hright
  have heconj : e.conjContinuousAlgEquiv.toAlgEquiv T = S := by
    ext x
    have hx := congrArg (fun R : E →L[ℂ] E => R x) hconj
    change Winv (T (W x)) = S x
    simpa only [ContinuousLinearMap.comp_apply] using hx
  calc
    spectrum ℂ T = spectrum ℂ (e.conjContinuousAlgEquiv.toAlgEquiv T) :=
      (AlgEquiv.spectrum_eq e.conjContinuousAlgEquiv.toAlgEquiv T).symm
    _ = spectrum ℂ S := congrArg (spectrum ℂ) heconj

section ComplexRiccati

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Canonical bounded Riccati diagonalization together with exact complex
spectrum transport. -/
theorem complex_blockDiagonalization_with_spectrum_of_riccati
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X) :
    ∃ W Winv : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1),
      ∃ D0 : E0 →L[ℂ] E0, ∃ D1 : E1 →L[ℂ] E1,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ TauCeti.LinearPMap.IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id ℂ _ ∧
      W ∘L Winv = ContinuousLinearMap.id ℂ _ ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 ∧
      spectrum ℂ (blockOperator H) =
        spectrum ℂ (blockDiagonalOperator D0 D1) := by
  obtain ⟨W, Winv, D0, D1, hWunit, hWinvunit, hleft, hright, hdiag⟩ :=
    complex_blockDiagonalization_of_riccati H hX
  refine ⟨W, Winv, D0, D1, hWunit, hWinvunit, hleft, hright, hdiag, ?_⟩
  exact spectrum_eq_of_inverse_conjugation
    (blockOperator H) (blockDiagonalOperator D0 D1) W Winv
    hleft hright hdiag

/-- Existential spectral form of bounded Riccati block diagonalization. -/
theorem complex_blockOperator_spectrum_eq_blockDiagonal_of_riccati
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X) :
    ∃ D0 : E0 →L[ℂ] E0, ∃ D1 : E1 →L[ℂ] E1,
      spectrum ℂ (blockOperator H) =
        spectrum ℂ (blockDiagonalOperator D0 D1) := by
  obtain ⟨_, _, D0, D1, _, _, _, _, _, hspec⟩ :=
    complex_blockDiagonalization_with_spectrum_of_riccati H hX
  exact ⟨D0, D1, hspec⟩

end ComplexRiccati

end DavisKahanExt
end TauCeti
