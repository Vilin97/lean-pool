/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedSpectralTransport
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Spectrum of a bounded block-diagonal operator

This leaf module computes the complex spectrum of the block-diagonal operator
used by the bounded Riccati diagonalization.

The proof first characterizes bijectivity of a diagonal operator on the
Hilbert direct sum in terms of bijectivity of its two diagonal blocks.  The
continuous-linear-map criterion for being a unit then translates this into an
invertibility statement.  Applying the definition of the spectrum to the
scalar resolvent operators gives the union formula

`σ (diag(D0,D1)) = σ(D0) ∪ σ(D1)`.

Combining this with the previously proved spectrum transport theorem yields
an exact spectral decomposition of every bounded complex block operator which
admits a Riccati solution.
-/

namespace TauCeti
namespace DavisKahanExt

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Pointwise action of the bounded block-diagonal operator. -/
@[simp]
theorem blockDiagonalOperator_apply
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1)
    (z : WithLp 2 (E0 × E1)) :
    blockDiagonalOperator D0 D1 z =
      WithLp.toLp 2 (D0 (WithLp.fst z), D1 (WithLp.snd z)) :=
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A block-diagonal operator is bijective exactly when both diagonal blocks
are bijective. -/
theorem blockDiagonalOperator_bijective_iff
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) :
    Function.Bijective (blockDiagonalOperator D0 D1) ↔
      Function.Bijective D0 ∧ Function.Bijective D1 := by
  constructor
  · rintro ⟨hdiag_inj, hdiag_surj⟩
    constructor
    · constructor
      · intro x y hxy
        have hdiag :
            blockDiagonalOperator D0 D1
                (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) x) =
              blockDiagonalOperator D0 D1
                (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) y) := by
          apply WithLp.ofLp_injective 2
          apply Prod.ext
          · simpa using hxy
          · simp
        have hcoord := congrArg WithLp.fst (hdiag_inj hdiag)
        simpa using hcoord
      · intro y
        obtain ⟨z, hz⟩ := hdiag_surj
          (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) y)
        refine ⟨WithLp.fst z, ?_⟩
        have hcoord := congrArg WithLp.fst hz
        simpa using hcoord
    · constructor
      · intro x y hxy
        have hdiag :
            blockDiagonalOperator D0 D1
                (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) x) =
              blockDiagonalOperator D0 D1
                (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) y) := by
          apply WithLp.ofLp_injective 2
          apply Prod.ext
          · simp
          · simpa using hxy
        have hcoord := congrArg WithLp.snd (hdiag_inj hdiag)
        simpa using hcoord
      · intro y
        obtain ⟨z, hz⟩ := hdiag_surj
          (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) y)
        refine ⟨WithLp.snd z, ?_⟩
        have hcoord := congrArg WithLp.snd hz
        simpa using hcoord
  · rintro ⟨⟨h0inj, h0surj⟩, ⟨h1inj, h1surj⟩⟩
    constructor
    · intro z w hzw
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · apply h0inj
        have hcoord := congrArg WithLp.fst hzw
        simpa using hcoord
      · apply h1inj
        have hcoord := congrArg WithLp.snd hzw
        simpa using hcoord
    · intro y
      obtain ⟨x0, hx0⟩ := h0surj (WithLp.fst y)
      obtain ⟨x1, hx1⟩ := h1surj (WithLp.snd y)
      refine ⟨WithLp.toLp 2 (x0, x1), ?_⟩
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa using hx0
      · simpa using hx1

/-- A bounded block-diagonal operator is a unit exactly when both diagonal
blocks are units. -/
theorem blockDiagonalOperator_isUnit_iff
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) :
    IsUnit (blockDiagonalOperator D0 D1) ↔ IsUnit D0 ∧ IsUnit D1 := by
  rw [ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.isUnit_iff_bijective]
  exact blockDiagonalOperator_bijective_iff D0 D1

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Scalar subtraction commutes with forming a block-diagonal operator. -/
theorem algebraMap_sub_blockDiagonalOperator
    (r : ℂ) (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) :
    algebraMap ℂ (WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) r -
        blockDiagonalOperator D0 D1 =
      blockDiagonalOperator
        (algebraMap ℂ (E0 →L[ℂ] E0) r - D0)
        (algebraMap ℂ (E1 →L[ℂ] E1) r - D1) := by
  ext z
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [blockDiagonalOperator_apply, Algebra.algebraMap_eq_smul_one]

/-- The complex spectrum of a bounded block-diagonal operator is the union of
the spectra of its two diagonal blocks. -/
theorem spectrum_blockDiagonalOperator
    (D0 : E0 →L[ℂ] E0) (D1 : E1 →L[ℂ] E1) :
    spectrum ℂ (blockDiagonalOperator D0 D1) =
      spectrum ℂ D0 ∪ spectrum ℂ D1 := by
  ext r
  rw [Set.mem_union]
  simp only [spectrum.mem_iff, algebraMap_sub_blockDiagonalOperator,
    blockDiagonalOperator_isUnit_iff, not_and_or]

/-- Exact spectral decomposition of a bounded complex block operator admitting
a Riccati solution. -/
theorem complex_blockOperator_spectrum_eq_union_of_riccati
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X) :
    ∃ D0 : E0 →L[ℂ] E0, ∃ D1 : E1 →L[ℂ] E1,
      spectrum ℂ (blockOperator H) = spectrum ℂ D0 ∪ spectrum ℂ D1 := by
  obtain ⟨D0, D1, hspec⟩ :=
    complex_blockOperator_spectrum_eq_blockDiagonal_of_riccati H hX
  refine ⟨D0, D1, ?_⟩
  calc
    spectrum ℂ (blockOperator H) =
        spectrum ℂ (blockDiagonalOperator D0 D1) := hspec
    _ = spectrum ℂ D0 ∪ spectrum ℂ D1 :=
      spectrum_blockDiagonalOperator D0 D1

end DavisKahanExt
end TauCeti
