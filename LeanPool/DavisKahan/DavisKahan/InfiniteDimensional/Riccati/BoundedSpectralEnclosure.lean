/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedBlockSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum


/-!
# Bounded Riccati spectral enclosures

This leaf module records the ordered real-spectrum consequences of the exact
complex block-spectrum decomposition.

The block-diagonal spectrum formula immediately implies that each effective
diagonal spectrum is contained in the spectrum of the full operator and that
a real spectral enclosure for the full diagonal operator is equivalent to the
same enclosure for both blocks.  If the first effective block lies below a cut
and the second lies above a cut, the full operator has no real spectrum in the
open gap and the two effective spectra retain the corresponding ordered
separation.

These statements deliberately take the two oriented effective-block
enclosures as hypotheses.  Proving that an off-diagonal continuation branch
satisfies those enclosures is the later spectral-repulsion input; it does not
follow from diagonalization of an arbitrary Riccati solution alone.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The real spectrum of a bounded block-diagonal operator is the union of the
real spectra of its two diagonal blocks. -/
theorem realSpectrum_blockDiagonalOperator
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) :
    realSpectrum (blockDiagonalOperator D0 D1) =
      realSpectrum D0 ∪ realSpectrum D1 := by
  ext r
  change
    ((r : ℂ) ∈ spectrum ℂ (blockDiagonalOperator D0 D1)) ↔
      ((r : ℂ) ∈ spectrum ℂ D0 ∨ (r : ℂ) ∈ spectrum ℂ D1)
  rw [spectrum_blockDiagonalOperator]
  rfl

/-- A real spectral enclosure holds for a block-diagonal operator exactly when
it holds for each diagonal block. -/
theorem realSpectrum_blockDiagonal_subset_iff
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) (s : Set ℝ) :
    realSpectrum (blockDiagonalOperator D0 D1) ⊆ s ↔
      realSpectrum D0 ⊆ s ∧ realSpectrum D1 ⊆ s := by
  rw [realSpectrum_blockDiagonalOperator]
  constructor
  · intro h
    constructor
    · intro r hr
      exact h (Or.inl hr)
    · intro r hr
      exact h (Or.inr hr)
  · rintro ⟨h0, h1⟩ r (hr0 | hr1)
    · exact h0 hr0
    · exact h1 hr1

/-- The first effective diagonal spectrum is contained in the full
block-diagonal spectrum. -/
theorem realSpectrum_block0_subset_blockDiagonal
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) :
    realSpectrum D0 ⊆ realSpectrum (blockDiagonalOperator D0 D1) := by
  rw [realSpectrum_blockDiagonalOperator]
  exact Set.subset_union_left

/-- The second effective diagonal spectrum is contained in the full
block-diagonal spectrum. -/
theorem realSpectrum_block1_subset_blockDiagonal
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) :
    realSpectrum D1 ⊆ realSpectrum (blockDiagonalOperator D0 D1) := by
  rw [realSpectrum_blockDiagonalOperator]
  exact Set.subset_union_right

/-- Oriented half-line enclosures of the two effective blocks exclude the open
gap from the full block-diagonal real spectrum. -/
theorem realSpectrum_blockDiagonal_subset_exterior
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1)
    {a b : ℝ}
    (h0 : realSpectrum D0 ⊆ Set.Iic a)
    (h1 : realSpectrum D1 ⊆ Set.Ici b) :
    realSpectrum (blockDiagonalOperator D0 D1) ⊆
      Set.Iic a ∪ Set.Ici b := by
  rw [realSpectrum_blockDiagonalOperator]
  intro r hr
  rcases hr with hr0 | hr1
  · exact Or.inl (h0 hr0)
  · exact Or.inr (h1 hr1)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Oriented half-line enclosures give the corresponding pointwise spectral
separation of the two effective blocks. -/
theorem realSpectra_blocks_separated_of_halfLines
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1)
    {a b d : ℝ} (hgap : a + d ≤ b)
    (h0 : realSpectrum D0 ⊆ Set.Iic a)
    (h1 : realSpectrum D1 ⊆ Set.Ici b) :
    ∀ x ∈ realSpectrum D0, ∀ y ∈ realSpectrum D1,
      d ≤ |x - y| := by
  intro x hx y hy
  have hxa : x ≤ a := h0 hx
  have hby : b ≤ y := h1 hy
  have hdyx : d ≤ y - x := by linarith
  calc
    d ≤ y - x := hdyx
    _ = -(x - y) := by ring
    _ ≤ |x - y| := neg_le_abs (x - y)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A complex spectrum decomposition transports directly to the corresponding
real-spectrum decomposition. -/
theorem realSpectrum_eq_union_of_spectrum_eq_union
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1)
    (hspec : spectrum ℂ T = spectrum ℂ D0 ∪ spectrum ℂ D1) :
    realSpectrum T = realSpectrum D0 ∪ realSpectrum D1 := by
  ext r
  change
    ((r : ℂ) ∈ spectrum ℂ T) ↔
      ((r : ℂ) ∈ spectrum ℂ D0 ∨ (r : ℂ) ∈ spectrum ℂ D1)
  rw [hspec]
  rfl

/-- Real-spectrum form of bounded Riccati block diagonalization, retaining the
unitary and inverse data for later branchwise spectral arguments. -/
theorem complex_blockDiagonalization_with_realSpectrum_of_riccati
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X) :
    ∃ W Winv : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1),
      ∃ D0 : E0 →L[ℂ] E0, ∃ D1 : E1 →L[ℂ] E1,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ TauCeti.LinearPMap.IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id ℂ _ ∧
      W ∘L Winv = ContinuousLinearMap.id ℂ _ ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 ∧
      realSpectrum (blockOperator H) =
        realSpectrum D0 ∪ realSpectrum D1 := by
  obtain ⟨W, Winv, D0, D1, hWunit, hWinvunit, hleft, hright,
      hdiag, hspec⟩ :=
    complex_blockDiagonalization_with_spectrum_of_riccati H hX
  refine ⟨W, Winv, D0, D1, hWunit, hWinvunit, hleft, hright,
    hdiag, ?_⟩
  exact realSpectrum_eq_union_of_spectrum_eq_union
    (blockOperator H) D0 D1
    (hspec.trans (spectrum_blockDiagonalOperator D0 D1))

/-- Any oriented effective-block enclosures produced by a Riccati
block diagonalization transfer to a real spectral gap exclusion for the
original block operator. -/
theorem realSpectrum_blockOperator_subset_exterior_of_diagonalization
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (W Winv : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1))
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1)
    (hleft : Winv ∘L W = ContinuousLinearMap.id ℂ _)
    (hright : W ∘L Winv = ContinuousLinearMap.id ℂ _)
    (hdiag : Winv ∘L blockOperator H ∘L W =
      blockDiagonalOperator D0 D1)
    {a b : ℝ}
    (h0 : realSpectrum D0 ⊆ Set.Iic a)
    (h1 : realSpectrum D1 ⊆ Set.Ici b) :
    realSpectrum (blockOperator H) ⊆ Set.Iic a ∪ Set.Ici b := by
  have hspec : spectrum ℂ (blockOperator H) =
      spectrum ℂ D0 ∪ spectrum ℂ D1 := by
    calc
      spectrum ℂ (blockOperator H) =
          spectrum ℂ (blockDiagonalOperator D0 D1) :=
        spectrum_eq_of_inverse_conjugation
          (blockOperator H) (blockDiagonalOperator D0 D1)
          W Winv hleft hright hdiag
      _ = spectrum ℂ D0 ∪ spectrum ℂ D1 :=
        spectrum_blockDiagonalOperator D0 D1
  have hreal : realSpectrum (blockOperator H) =
      realSpectrum D0 ∪ realSpectrum D1 :=
    realSpectrum_eq_union_of_spectrum_eq_union
      (blockOperator H) D0 D1 hspec
  rw [hreal]
  intro r hr
  rcases hr with hr0 | hr1
  · exact Or.inl (h0 hr0)
  · exact Or.inr (h1 hr1)

end DavisKahanExt
end TauCeti
