/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalSpectrumNonempty
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded Off Diagonal Ordered Gap -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Forward ordered-gap estimate for bounded off-diagonal perturbations

This leaf transports theorem-facing restricted spectral half-lines to the
real spectra used by the complex spectral-order API.  It then closes the sharp
contractive Riccati estimate in the forward ordered orientation

`restrictedSpectrum A U + d <= restrictedSpectrum A Uᗮ`.

The reverse orientation and degenerate subspaces remain separate.  Keeping the
orientation explicit avoids hiding the complementary-graph argument needed by
the final public theorem.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A half-line bound on the native real spectrum of a self-adjoint complex
operator also bounds its spectrum over the real scalar subalgebra. -/
theorem spectrum_real_subset_Iic_of_realSpectrum_subset_Iic
    (T : E →L[ℂ] E) (hT : T.IsSymmetric) {c : ℝ}
    (hspec : realSpectrum T ⊆ Set.Iic c) :
    spectrum ℝ T ⊆ Set.Iic c := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  intro r hr
  apply hspec
  change (r : ℂ) ∈ spectrum ℂ T
  rw [← hTsa.spectrumRestricts.algebraMap_image]
  exact ⟨r, hr, by simp⟩

/-- The analogous lower half-line transport. -/
theorem spectrum_real_subset_Ici_of_realSpectrum_subset_Ici
    (T : E →L[ℂ] E) (hT : T.IsSymmetric) {c : ℝ}
    (hspec : realSpectrum T ⊆ Set.Ici c) :
    spectrum ℝ T ⊆ Set.Ici c := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  intro r hr
  apply hspec
  change (r : ℂ) ∈ spectrum ℂ T
  rw [← hTsa.spectrumRestricts.algebraMap_image]
  exact ⟨r, hr, by simp⟩

/-- A restricted-spectrum upper half-line transports to the real spectrum of
the corresponding orthogonal compression. -/
theorem spectrum_real_compress_subset_Iic_of_restrictedSpectrum_subset_Iic
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : InvariantFor A U) {c : ℝ}
    (hspec : restrictedSpectrum A U ⊆ Set.Iic c) :
    spectrum ℝ (compressOperator U A) ⊆ Set.Iic c := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hcompress : (compressOperator U A).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_compressOperator hAsa U)
  apply spectrum_real_subset_Iic_of_realSpectrum_subset_Iic
    (compressOperator U A) hcompress
  rw [← restrictedSpectrum_eq_realSpectrum_compressOperator A U hU]
  exact hspec

/-- A restricted-spectrum lower half-line transports to the real spectrum of
the corresponding orthogonal compression. -/
theorem spectrum_real_compress_subset_Ici_of_restrictedSpectrum_subset_Ici
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : InvariantFor A U) {c : ℝ}
    (hspec : restrictedSpectrum A U ⊆ Set.Ici c) :
    spectrum ℝ (compressOperator U A) ⊆ Set.Ici c := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hcompress : (compressOperator U A).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_compressOperator hAsa U)
  apply spectrum_real_subset_Ici_of_realSpectrum_subset_Ici
    (compressOperator U A) hcompress
  rw [← restrictedSpectrum_eq_realSpectrum_compressOperator A U hU]
  exact hspec

/-- Sharp contractive Riccati inequality in the forward ordered orientation.
The nontriviality assumptions are exactly those needed for nonempty restricted
spectra and the supremum separating center. -/
theorem quarterAcuteAngularCoordinate_sharp_bound_of_orderedSpectraSeparated
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [Nontrivial U] 
    (hU : A.Reduces U) (hV : ContinuousLinearMap.Reduces (A + H) V)
    (hoff : Submodule.IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d)
    (hordered : OrderedSpectraSeparated A U A Uᗮ d)
    (hquarter : IsQuarterAcute U V) :
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ ≤
      ‖H‖ * (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by
  obtain ⟨c, hUhalf, hUchalf⟩ :=
    OrderedSpectraSeparated.exists_halfLine_center hordered
      (restrictedSpectrum_nonempty_of_invariant A hA U hordered.1)
      (restrictedSpectrum_bddAbove_of_invariant A U hordered.1)
  have hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Iic c :=
    spectrum_real_compress_subset_Iic_of_restrictedSpectrum_subset_Iic
      A hA U hordered.1 hUhalf
  have hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (c + d) :=
    spectrum_real_compress_subset_Ici_of_restrictedSpectrum_subset_Ici
      A hA Uᗮ hordered.2.1 hUchalf
  exact quarterAcuteAngularCoordinate_sharp_bound_of_spectral_halfLines
    A H hA hH U V hU hV hoff hd hA0spec hA1spec hquarter

end DavisKahanExt
end TauCeti
