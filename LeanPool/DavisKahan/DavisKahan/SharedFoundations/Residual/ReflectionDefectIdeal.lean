/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.TrialResidual
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngleSpectrum

/-!
# Ideal-gauge residual control for reflection defects

The elementary rectangular-ideal axioms give a robust factor-four estimate.
Obtaining the sharp factor two for arbitrary symmetric gauges requires an
additional off-diagonal block theorem and should not be hidden in the basic
ideal interface.
-/

namespace TauCeti
namespace DavisKahan
namespace SharedFoundations
namespace Residual

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta
open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.BoundedOperator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- A trial residual in a symmetric operator ideal family forces the associated
reflection defect into the square member of the same family. -/
theorem SymmetricOperatorIdealFamily.reflectionDefect_isometricRange_mem
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (residual A X M)) :
    letI := rangeHasOrthogonalProjection X hX
    let V : Submodule ℂ H := LinearMap.range X.toLinearMap
    N.Mem (reflectionDefect V A) := by
  let := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  change N.Mem (reflectionDefect V A)
  let T : H →L[ℂ] H := Vᗮ.starProjection ∘L A ∘L V.starProjection
  have hT : N.Mem T := by
    simpa [T, isometricRangeCrossBlock] using
      isometricRangeCrossBlock_mem
        N A X M hX hR
  have hTa : N.Mem T.adjoint := N.adjoint_mem hT
  have hblock : V.starProjection ∘L A ∘L Vᗮ.starProjection = T.adjoint := by
    change V.starProjection ∘L A ∘L Vᗮ.starProjection =
      (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint
    exact (offdiag_adjoint V hA).symm
  rw [reflectionDefect_eq_neg_two_smul_offdiag, hblock]
  exact N.smul_mem (-2 : ℂ) (N.add_mem hT hTa)

/-- The basic ideal axioms yield a factor-four reflection-defect bound through
the trial residual. -/
theorem SymmetricOperatorIdealFamily.gauge_reflectionDefect_isometricRange_le_four_mul
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (residual A X M)) :
    letI := rangeHasOrthogonalProjection X hX
    let V : Submodule ℂ H := LinearMap.range X.toLinearMap
    N.gaugeReal (reflectionDefect V A) ≤ 4 * N.gaugeReal (residual A X M) := by
  let := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  change N.gaugeReal (reflectionDefect V A) ≤
    4 * N.gaugeReal (residual A X M)
  let T : H →L[ℂ] H := Vᗮ.starProjection ∘L A ∘L V.starProjection
  have hT : N.Mem T := by
    simpa [T, isometricRangeCrossBlock] using
      isometricRangeCrossBlock_mem
        N A X M hX hR
  have hTa : N.Mem T.adjoint := N.adjoint_mem hT
  have hTg : N.gaugeReal T ≤ N.gaugeReal (residual A X M) := by
    simpa [T, isometricRangeCrossBlock] using
      gauge_isometricRangeCrossBlock_le
        N A X M hX hR
  have hblock : V.starProjection ∘L A ∘L Vᗮ.starProjection = T.adjoint := by
    change V.starProjection ∘L A ∘L Vᗮ.starProjection =
      (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint
    exact (offdiag_adjoint V hA).symm
  rw [reflectionDefect_eq_neg_two_smul_offdiag, hblock,
    N.gaugeReal_smul (-2 : ℂ) (N.add_mem hT hTa)]
  have hadd := N.gaugeReal_add_le hT hTa
  have hadj := N.gaugeReal_adjoint hT
  calc
    ‖(-2 : ℂ)‖ * N.gaugeReal (T + T.adjoint)
        ≤ 2 * (N.gaugeReal T + N.gaugeReal T.adjoint) := by
          norm_num
          gcongr
    _ = 4 * N.gaugeReal T := by rw [hadj]; ring
    _ ≤ 4 * N.gaugeReal (residual A X M) := by gcongr

end Residual
end SharedFoundations
end DavisKahan
end TauCeti
