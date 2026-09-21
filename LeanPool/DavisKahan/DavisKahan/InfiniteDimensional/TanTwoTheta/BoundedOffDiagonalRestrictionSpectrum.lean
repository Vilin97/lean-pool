/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalOrderedSets
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded Off Diagonal Restriction Spectrum -/

open TauCeti.DavisKahan.Sylvester

/-!
# Restricted spectra and orthogonal compressions

This leaf connects the theorem-facing `restrictedSpectrum` API to the
orthogonal compressions used by the bounded Riccati argument.  On an invariant
subspace the orthogonal compression is literally the continuous-linear
restriction.  Consequently the native real spectrum of the compression is the
restricted spectrum.

The leaf also records that every restricted spectrum is bounded above and
below by the norm of the restriction.  Thus the only remaining hypothesis in
the supremum-center construction is nonemptiness, which is handled separately
for nontrivial subspaces.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan.Foundation

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The theorem-facing restricted spectrum equals the native real spectrum of
the orthogonal compression. -/
theorem restrictedSpectrum_eq_realSpectrum_compressOperator
    (A : E →L[ℂ] E) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : InvariantFor A U) :
    restrictedSpectrum A U = realSpectrum (compressOperator U A) := by
  calc
    DavisKahan.Foundation.restrictedSpectrum A U =
        {r : ℝ | (r : ℂ) ∈ spectrum ℂ (A.restrict hU)} :=
      DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum A U hU
    _ = DavisKahan.Foundation.realSpectrum (A.restrict hU) := rfl
    _ = DavisKahan.Foundation.realSpectrum (compressOperator U A) := by
      rw [compressOperator_eq_restrict_of_invariant A U hU]

/-- The real spectrum of a bounded operator is bounded above by its norm. -/
theorem realSpectrum_bddAbove [Nontrivial E] (T : E →L[ℂ] E) :
    BddAbove (realSpectrum T) := by
  refine ⟨‖T‖, ?_⟩
  intro r hr
  change (r : ℂ) ∈ spectrum ℂ T at hr
  have hnorm : ‖(r : ℂ)‖ ≤ ‖T‖ :=
    spectrum.norm_le_norm_of_mem hr
  calc
    r ≤ |r| := le_abs_self r
    _ = ‖(r : ℂ)‖ := by simp
    _ ≤ ‖T‖ := hnorm

/-- The real spectrum of a bounded operator is bounded below by minus its norm. -/
theorem realSpectrum_bddBelow [Nontrivial E] (T : E →L[ℂ] E) :
    BddBelow (realSpectrum T) := by
  refine ⟨-‖T‖, ?_⟩
  intro r hr
  change (r : ℂ) ∈ spectrum ℂ T at hr
  have hnorm : ‖(r : ℂ)‖ ≤ ‖T‖ :=
    spectrum.norm_le_norm_of_mem hr
  have habs : |r| ≤ ‖T‖ := by
    simpa using hnorm
  exact neg_le_of_abs_le habs

/-- Every restricted spectrum of an invariant orthogonally complemented
subspace is bounded above. -/
theorem restrictedSpectrum_bddAbove_of_invariant
    (A : E →L[ℂ] E) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    [Nontrivial U]
    (hU : InvariantFor A U) :
    BddAbove (restrictedSpectrum A U) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  rw [restrictedSpectrum_eq_realSpectrum_compressOperator A U hU]
  exact realSpectrum_bddAbove (compressOperator U A)

/-- Every restricted spectrum of an invariant orthogonally complemented
subspace is bounded below. -/
theorem restrictedSpectrum_bddBelow_of_invariant
    (A : E →L[ℂ] E) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    [Nontrivial U]
    (hU : InvariantFor A U) :
    BddBelow (restrictedSpectrum A U) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  rw [restrictedSpectrum_eq_realSpectrum_compressOperator A U hU]
  exact realSpectrum_bddBelow (compressOperator U A)

end DavisKahanExt
end TauCeti
