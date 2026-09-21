/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalRestrictionSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded Off Diagonal Spectrum Nonempty -/

open TauCeti.DavisKahan.Sylvester

/-!
# Nonempty restricted spectra for bounded self-adjoint compressions

This leaf discharges the remaining set-theoretic hypotheses in the ordered-gap
center construction for nontrivial orthogonally complemented subspaces.

The proof of spectral nonemptiness is intentionally local.  It uses the
self-adjoint spectral-radius identity: an empty spectrum would force spectral
radius zero, hence operator norm zero and the operator itself zero, contradicting
that zero belongs to the spectrum of the zero operator on a nontrivial space.
Self-adjoint spectral restriction then supplies a real spectral point.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A bounded self-adjoint operator on a nontrivial complex Hilbert space has a
nonempty native real spectrum. -/
theorem realSpectrum_nonempty_of_selfAdjoint [Nontrivial E]
    (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    (realSpectrum T).Nonempty := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hrad : spectralRadius ℂ T = ‖T‖₊ :=
    T.spectralRadius_eq_nnnorm hTsa
  obtain ⟨z, hz⟩ : (spectrum ℂ T).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hzeroRadius : spectralRadius ℂ T = 0 := by
      rw [spectralRadius_eq_of_unital, hempty]
      simp
    have hTzero : T = 0 := by
      have hnormZero : ((‖T‖₊ : ENNReal)) = 0 := by
        rw [← hrad]
        exact hzeroRadius
      rw [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hnormZero
      exact hnormZero
    have hzeroMem : (0 : ℂ) ∈ spectrum ℂ T := by
      rw [hTzero, spectrum.zero_mem_iff]
      exact not_isUnit_zero
    rw [hempty] at hzeroMem
    exact hzeroMem
  obtain ⟨lam, _hlam, rfl⟩ :=
    hTsa.spectrumRestricts.algebraMap_image.symm ▸ hz
  refine ⟨lam, ?_⟩
  change (lam : ℂ) ∈ spectrum ℂ T
  exact hz

/-- The restricted spectrum of a self-adjoint operator on a nontrivial
invariant orthogonally complemented subspace is nonempty. -/
theorem restrictedSpectrum_nonempty_of_invariant
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] [Nontrivial U]
    (hU : InvariantFor A U) :
    (restrictedSpectrum A U).Nonempty := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hcompress : (compressOperator U A).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_compressOperator hAsa U)
  rw [restrictedSpectrum_eq_realSpectrum_compressOperator A U hU]
  exact realSpectrum_nonempty_of_selfAdjoint (compressOperator U A) hcompress

/-- For nontrivial complementary subspaces, an ordered internal gap supplies one
of the two oriented restricted-spectrum half-line configurations with no extra
set-theoretic hypotheses. -/
theorem _root_.TauCeti.DavisKahan.Foundation.OrderedInternalGap.exists_oriented_halfLine_center_of_nontrivial
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    [Nontrivial U] [Nontrivial Uᗮ]
    {d : ℝ} (hgap : OrderedInternalGap A U d) :
    (∃ c : ℝ,
      restrictedSpectrum A U ⊆ Set.Iic c ∧
      restrictedSpectrum A Uᗮ ⊆ Set.Ici (c + d)) ∨
    (∃ c : ℝ,
      restrictedSpectrum A Uᗮ ⊆ Set.Iic c ∧
      restrictedSpectrum A U ⊆ Set.Ici (c + d)) := by
  rcases hgap with hforward | hreverse
  · rcases hforward with ⟨hU, hUc, hordered⟩
    exact Or.inl <| exists_halfLine_center_of_ordered_sets
      (restrictedSpectrum_nonempty_of_invariant A hA U hU)
      (restrictedSpectrum_bddAbove_of_invariant A U hU)
      hordered
  · rcases hreverse with ⟨hUc, hU, hordered⟩
    exact Or.inr <| exists_halfLine_center_of_ordered_sets
      (restrictedSpectrum_nonempty_of_invariant A hA Uᗮ hUc)
      (restrictedSpectrum_bddAbove_of_invariant A Uᗮ hUc)
      hordered

end DavisKahanExt
end TauCeti
