/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpBlockPath
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Sharp Source Spectrum -/

open TauCeti.DavisKahan.Sylvester

/-!
# Source spectra for sharp off-diagonal continuation

The sharp continuation enclosure argument is formulated in block coordinates.
This leaf identifies the genuine spectra of the diagonal compressions with the
repository's restricted spectra and transports a finite-gap configuration to
the constant diagonal blocks of the affine path.

Together with the cross-block bounds from `ContinuationSharpBlockPath`, the
final theorem packages exactly the data needed by a later Schur-complement or
block-resolvent spectral-enclosure theorem.  No spectral inclusion for the full
perturbed operator is asserted here.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace

universe v

section CompressionSpectrum

variable {Hspace : Type v} [NormedAddCommGroup Hspace]
  [InnerProductSpace ℂ Hspace] [CompleteSpace Hspace]

omit [CompleteSpace Hspace] in
/-- On a reducing subspace, orthogonal compression is the actual restricted
operator. -/
theorem compressOperator_eq_restrict_of_reduces
    (A : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (hU : A.Reduces U) :
    compressOperator U A = A.restrict hU.1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change U.starProjection (A (u : Hspace)) = A (u : Hspace)
  exact Submodule.starProjection_eq_self_iff.mpr
    (hU.1 (u : Hspace) u.property)

omit [CompleteSpace Hspace] in
/-- The real spectrum of a compression to a reducing subspace is exactly the
restricted spectrum used by the theorem-facing gap predicates. -/
theorem realSpectrum_compressOperator_eq_restrictedSpectrum_of_reduces
    (A : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]

    (hU : A.Reduces U) :
    realSpectrum (compressOperator U A) = restrictedSpectrum A U := by
  have hInv : InvariantFor A U := by
    intro x hx
    exact hU.1 x hx
  have hcompress : compressOperator U A = A.restrict hInv := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change U.starProjection (A (u : Hspace)) = A (u : Hspace)
    exact Submodule.starProjection_eq_self_iff.mpr
      (hInv (u : Hspace) u.property)
  rw [hcompress]
  ext r
  change
    ((r : ℂ) ∈ spectrum ℂ (A.restrict hInv)) ↔
      ∃ hInv' : InvariantFor A U,
        (r : ℂ) ∈ spectrum ℂ (A.restrict hInv')
  constructor
  · intro hr
    exact ⟨hInv, hr⟩
  · rintro ⟨hInv', hr⟩
    simpa using hr

omit [CompleteSpace Hspace] in
/-- A finite-gap configuration places the genuine spectra of the two diagonal
compressions in the same interval and exterior sets. -/
theorem _root_.TauCeti.DavisKahan.Foundation.FiniteGapConfiguration.exists_compressOperator_enclosures
    (A : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]

    (hU : A.Reduces U) {d : ℝ}
    (hfinite : FiniteGapConfiguration A U d) :
    ∃ left right : ℝ, left ≤ right ∧
      realSpectrum (compressOperator U A) ⊆ Set.Icc left right ∧
      realSpectrum (compressOperator Uᗮ A) ⊆
        {x : ℝ | x ≤ left - d ∨ right + d ≤ x} := by
  rcases hfinite with ⟨left, right, hlr, hselected, hcomplement⟩
  refine ⟨left, right, hlr, ?_, ?_⟩
  · rw [realSpectrum_compressOperator_eq_restrictedSpectrum_of_reduces A U hU]
    exact hselected.2
  · rw [realSpectrum_compressOperator_eq_restrictedSpectrum_of_reduces A Uᗮ
      hU.orthogonalComplement]
    exact hcomplement.2

end CompressionSpectrum

section PathEnclosureData

variable {Hspace : Type v} [NormedAddCommGroup Hspace]
  [InnerProductSpace ℂ Hspace] [CompleteSpace Hspace]

/-- A finite-gap configuration, reduction of `A`, and off-diagonality of `K`
provide all diagonal-spectrum placements and cross-block norm estimates needed
for the sharp pathwise block-resolvent enclosure. -/
theorem _root_.TauCeti.DavisKahan.Foundation.FiniteGapConfiguration.exists_operatorPath_block_enclosureData
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]

    (hU : A.Reduces U) (hK : Submodule.IsOffDiagonal U K)
    {d : ℝ} (hfinite : FiniteGapConfiguration A U d) :
    ∃ left right : ℝ, left ≤ right ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ hpath : (operatorPath A K t).IsSymmetric,
        realSpectrum
            (subspaceBlockOperatorData (operatorPath A K t) U hpath).A0 ⊆
          Set.Icc left right ∧
        realSpectrum
            (subspaceBlockOperatorData (operatorPath A K t) U hpath).A1 ⊆
          {x : ℝ | x ≤ left - d ∨ right + d ≤ x} ∧
        ‖(subspaceBlockOperatorData
            (operatorPath A K t) U hpath).B01‖ ≤ t * ‖K‖ ∧
        ‖(subspaceBlockOperatorData
            (operatorPath A K t) U hpath).B10‖ ≤ t * ‖K‖ := by
  obtain ⟨left, right, hlr, hspec0, hspec1⟩ :=
    hfinite.exists_compressOperator_enclosures A U hU
  refine ⟨left, right, hlr, ?_⟩
  intro t ht hpath
  constructor
  · rw [operatorPath_subspaceBlockOperatorData_A0_eq
      A K U hU hK t hpath]
    exact hspec0
  constructor
  · rw [operatorPath_subspaceBlockOperatorData_A1_eq
      A K U hU hK t hpath]
    exact hspec1
  constructor
  · exact norm_operatorPath_subspaceBlockOperatorData_B01_le
      A K U hU t ht hpath
  · exact norm_operatorPath_subspaceBlockOperatorData_B10_le
      A K U hU t ht hpath

end PathEnclosureData

end DavisKahanExt
end TauCeti
