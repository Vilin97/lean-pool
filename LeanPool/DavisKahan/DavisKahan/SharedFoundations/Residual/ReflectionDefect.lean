/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.TrialResidual
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngleSpectrum

/-!
# Reflection defect controlled by an isometric trial residual

This is the shared algebraic bridge needed by residual forms of the
`sin 2Θ` theorem.  It turns the off-diagonal reflection estimate into a
residual estimate without any spectral assumptions.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace SharedFoundations
namespace Residual

open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.BoundedOperator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Reflection defect of a self-adjoint operator at the range of an isometric
trial embedding is controlled by twice any associated residual. -/
theorem norm_reflectionDefect_isometricRange_le_two_mul_residual
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) :
    letI := rangeHasOrthogonalProjection X hX
    let V : Submodule ℂ H := LinearMap.range X.toLinearMap
    ‖reflectionDefect V A‖ ≤ 2 * ‖residual A X M‖ := by
  let := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  calc
    ‖reflectionDefect V A‖
        ≤ 2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ :=
      norm_reflectionDefect_le_two_mul_norm_cross V hA
    _ = 2 * ‖isometricRangeCrossBlock A X hX‖ := by rfl
    _ ≤ 2 * ‖residual A X M‖ := by
      gcongr
      exact norm_isometricRangeCrossBlock_le_residual A X M hX

end Residual
end SharedFoundations
end DavisKahan
end TauCeti
