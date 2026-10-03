/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalEstimate
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded Off Diagonal Half Line -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Spectral half-line bridge for bounded off-diagonal tangent-two-theta

This leaf converts ordered half-line inclusions for the two compressed diagonal
blocks into the centered quadratic-form hypotheses consumed by the sharp
contractive Riccati estimate.  It deliberately keeps the separating center
explicit.  The remaining `OrderedInternalGap` bridge only has to construct such
a center, including the degenerate-subspace cases and the reverse orientation.
-/

namespace TauCeti


open TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- An upper spectral half-line for a compressed self-adjoint operator gives
its centered quadratic-form upper bound. -/
theorem compressOperator_upperFormBound_of_spectrum_subset_Iic
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    {c : ℝ}
    (hspec : spectrum ℝ (compressOperator U A) ⊆ Set.Iic c) :
    ∀ z : U,
      RCLike.re ⟪compressOperator U A z, z⟫_ℂ ≤ c * ‖z‖ ^ 2 := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hcompress : IsSelfAdjoint (compressOperator U A) :=
    isSelfAdjoint_compressOperator hAsa U
  intro z
  exact TauCeti.SpectralOrder.re_inner_le_of_spectrum_subset_Iic
    (compressOperator U A) hcompress hspec z

/-- A lower spectral half-line for a compressed self-adjoint operator gives
its centered quadratic-form lower bound. -/
theorem compressOperator_lowerFormBound_of_spectrum_subset_Ici
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    {c : ℝ}
    (hspec : spectrum ℝ (compressOperator U A) ⊆ Set.Ici c) :
    ∀ z : U,
      c * ‖z‖ ^ 2 ≤ RCLike.re ⟪compressOperator U A z, z⟫_ℂ := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hcompress : IsSelfAdjoint (compressOperator U A) :=
    isSelfAdjoint_compressOperator hAsa U
  intro z
  exact TauCeti.SpectralOrder.le_re_inner_of_spectrum_subset_Ici
    (compressOperator U A) hcompress hspec z

/-- Sharp contractive Riccati inequality for a quarter-acute reducing graph
when the two unperturbed compressed spectra lie in ordered half-lines. -/
theorem quarterAcuteAngularCoordinate_sharp_bound_of_spectral_halfLines
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : ContinuousLinearMap.Reduces (A + H) V)
    (hoff : Submodule.IsOffDiagonal U H)
    {c d : ℝ} (hd : 0 < d)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Iic c)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (c + d))
    (hquarter : IsQuarterAcute U V) :
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ ≤
      ‖H‖ * (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact quarterAcuteAngularCoordinate_sharp_bound_of_form_gap
    A H hA hH U V hU hV hoff hd
    (compressOperator_upperFormBound_of_spectrum_subset_Iic A hA U hA0spec)
    (compressOperator_lowerFormBound_of_spectrum_subset_Ici A hA Uᗮ hA1spec)
    hquarter

end DavisKahanExt
end TauCeti
