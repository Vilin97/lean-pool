/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTheta.ContinuationWitnessAPriori
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedSpectralEnclosure
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Continuation Witness Effective Blocks -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Effective blocks of a continuation-selected Riccati branch

The witness-selected graph and its bounded Riccati coordinate are already
available.  This leaf applies the canonical bounded graph rotation and records
all of the exact information that is independent of spectral orientation:

* unitary graph rotation and inverse;
* exact block diagonalization;
* exact real-spectrum union of the two effective blocks;
* transfer of any later oriented half-line enclosures to the full selected
  block operator.

The last step is deliberately conditional on the two oriented effective-block
enclosures.  Proving those inequalities is the remaining spectral-repulsion
input; exact diagonalization and spectrum union alone do not imply them.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open Set
open scoped InnerProductSpace

universe v

section WitnessEffectiveBlocks

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

namespace SpectralContinuationWitness

/-- The continuation-selected Riccati coordinate admits canonical unitary
block diagonalization, and the real spectrum of the selected block operator is
exactly the union of the two effective-block real spectra. -/
theorem exists_selectedEffectiveBlocks_with_realSpectrum
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    ∃ W Winv :
        WithLp 2
            (C.sourceSelectedSpectralSubspace ×
              C.sourceSelectedSpectralSubspaceᗮ) →L[ℂ]
          WithLp 2
            (C.sourceSelectedSpectralSubspace ×
              C.sourceSelectedSpectralSubspaceᗮ),
      ∃ D0 : C.sourceSelectedSpectralSubspace →L[ℂ]
          C.sourceSelectedSpectralSubspace,
      ∃ D1 : C.sourceSelectedSpectralSubspaceᗮ →L[ℂ]
          C.sourceSelectedSpectralSubspaceᗮ,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ TauCeti.LinearPMap.IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id ℂ _ ∧
      W ∘L Winv = ContinuousLinearMap.id ℂ _ ∧
      Winv ∘L
          blockOperator
            (subspaceBlockOperatorData (A + V)
              C.sourceSelectedSpectralSubspace
              C.targetSeparatingContour.selfAdjoint) ∘L
          W = blockDiagonalOperator D0 D1 ∧
      realSpectrum
          (blockOperator
            (subspaceBlockOperatorData (A + V)
              C.sourceSelectedSpectralSubspace
              C.targetSeparatingContour.selfAdjoint)) =
        realSpectrum D0 ∪ realSpectrum D1 := by
  let U := C.sourceSelectedSpectralSubspace
  let X : U →L[ℂ] Uᗮ :=
    subspaceAngularCoordinate U (C.selectedEndpointAngularOperator hsmall)
  let B := subspaceBlockOperatorData (A + V) U
    C.targetSeparatingContour.selfAdjoint
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hX : SolvesRiccati B X := by
    simpa only [U, X, B] using
      C.selectedEndpointAngularCoordinate_solvesRiccati hsmall
  simpa only [U, X, B] using
    complex_blockDiagonalization_with_realSpectrum_of_riccati B hX

/-- Once the selected effective blocks have oriented half-line enclosures,
the exact diagonalization excludes the corresponding open gap from the full
selected block operator. -/
theorem selectedBlockOperator_realSpectrum_subset_exterior_of_effectiveBlocks
    (C : SpectralContinuationWitness A V s)
    (W Winv :
        WithLp 2
            (C.sourceSelectedSpectralSubspace ×
              C.sourceSelectedSpectralSubspaceᗮ) →L[ℂ]
          WithLp 2
            (C.sourceSelectedSpectralSubspace ×
              C.sourceSelectedSpectralSubspaceᗮ))
    (D0 : C.sourceSelectedSpectralSubspace →L[ℂ]
      C.sourceSelectedSpectralSubspace)
    (D1 : C.sourceSelectedSpectralSubspaceᗮ →L[ℂ]
      C.sourceSelectedSpectralSubspaceᗮ)
    (hleft : Winv ∘L W = ContinuousLinearMap.id ℂ _)
    (hright : W ∘L Winv = ContinuousLinearMap.id ℂ _)
    (hdiag :
      Winv ∘L
          blockOperator
            (subspaceBlockOperatorData (A + V)
              C.sourceSelectedSpectralSubspace
              C.targetSeparatingContour.selfAdjoint) ∘L
          W = blockDiagonalOperator D0 D1)
    {a b : ℝ}
    (h0 : realSpectrum D0 ⊆ Set.Iic a)
    (h1 : realSpectrum D1 ⊆ Set.Ici b) :
    realSpectrum
        (blockOperator
          (subspaceBlockOperatorData (A + V)
            C.sourceSelectedSpectralSubspace
            C.targetSeparatingContour.selfAdjoint)) ⊆
      Set.Iic a ∪ Set.Ici b := by
  let U := C.sourceSelectedSpectralSubspace
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact realSpectrum_blockOperator_subset_exterior_of_diagonalization
    (subspaceBlockOperatorData (A + V) U
      C.targetSeparatingContour.selfAdjoint)
    W Winv D0 D1 hleft hright hdiag h0 h1

/-- The same oriented effective-block hypotheses give the pointwise separation
between the two selected effective spectra. -/
theorem selectedEffectiveBlocks_realSpectra_separated
    (C : SpectralContinuationWitness A V s)
    (D0 : C.sourceSelectedSpectralSubspace →L[ℂ]
      C.sourceSelectedSpectralSubspace)
    (D1 : C.sourceSelectedSpectralSubspaceᗮ →L[ℂ]
      C.sourceSelectedSpectralSubspaceᗮ)
    {a b d : ℝ} (hgap : a + d ≤ b)
    (h0 : realSpectrum D0 ⊆ Set.Iic a)
    (h1 : realSpectrum D1 ⊆ Set.Ici b) :
    ∀ x ∈ realSpectrum D0, ∀ y ∈ realSpectrum D1,
      d ≤ |x - y| := by
  let U := C.sourceSelectedSpectralSubspace
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact realSpectra_blocks_separated_of_halfLines D0 D1 hgap h0 h1

end SpectralContinuationWitness

end WitnessEffectiveBlocks

end DavisKahanExt
end TauCeti
