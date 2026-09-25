/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus

/-!
# Sine of the operator angle

This module gives the complex Hilbert-space sine operator used by the
Davis--Kahan geometry: the modulus of the difference of two orthogonal
projections.  It is defined directly through the canonical `ContinuousLinearMap.modulus`
implementation in `ForTauCeti`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The Spectra-backed sine-angle operator, defined as the modulus of the
orthogonal-projector difference. -/
noncomputable def spectraSinAngleOperator
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  ContinuousLinearMap.modulus (U.starProjection - V.starProjection)

/-- The bridge definition is exactly the Spectra modulus of the projector
difference. -/
@[simp]
theorem spectraSinAngleOperator_eq_absoluteValue
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraSinAngleOperator U V =
      ContinuousLinearMap.modulus (U.starProjection - V.starProjection) :=
  rfl

/-- The Spectra-backed sine-angle operator is positive. -/
theorem spectraSinAngleOperator_nonneg
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ spectraSinAngleOperator U V := by
  simpa [spectraSinAngleOperator] using
    ContinuousLinearMap.modulus_nonneg (U.starProjection - V.starProjection)

/-- The Spectra-backed sine-angle operator is self-adjoint. -/
theorem spectraSinAngleOperator_isSelfAdjoint
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (spectraSinAngleOperator U V) := by
  simpa [spectraSinAngleOperator] using
    ContinuousLinearMap.modulus_isSelfAdjoint (U.starProjection - V.starProjection)

/-- Squaring the Spectra-backed sine-angle operator gives the positive product
of the projector difference with its adjoint. -/
theorem spectraSinAngleOperator_mul_self
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraSinAngleOperator U V * spectraSinAngleOperator U V =
      star (U.starProjection - V.starProjection) *
        (U.starProjection - V.starProjection) := by
  simpa [spectraSinAngleOperator] using
    ContinuousLinearMap.modulus_mul_self_eq_star_mul_self (U.starProjection - V.starProjection)

/-- Pointwise norms of the sine-angle operator and projector difference agree. -/
theorem norm_spectraSinAngleOperator_apply
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : H) :
    ‖spectraSinAngleOperator U V x‖ =
      ‖(U.starProjection - V.starProjection) x‖ := by
  simp [spectraSinAngleOperator]

/-- The operator norm of the Spectra-backed sine-angle operator is exactly the
existing DKPS symmetric subspace gap. -/
theorem norm_spectraSinAngleOperator
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖spectraSinAngleOperator U V‖ = U.projectionGap V := by
  change ‖ContinuousLinearMap.modulus
      (U.starProjection - V.starProjection)‖ =
    ‖U.starProjection - V.starProjection‖
  exact ContinuousLinearMap.norm_modulus
    (U.starProjection - V.starProjection)

end DavisKahan
end TauCeti
