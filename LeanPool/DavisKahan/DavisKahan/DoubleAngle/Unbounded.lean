/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReflectionRestriction

/-! # Unbounded -/

open TauCeti.DavisKahan.Angle


/-!
# Reflection geometry for the unbounded sine-two-theta theorem

The two norm identities that let the reflection construction be read as a statement about
the complex sine-two-angle operator: reflecting the orthogonal complement of `U` through `V`
turns the overlap block `U.starProjection ∘L (Uᗮ.map V.reflection).starProjection` — and its
`subtypeL` presentation — into `directedSinTwoAngleOperatorC U V`, up to nothing.

The theorems that use them live in `DavisKahan.DoubleAngle.UnboundedIdeal`, which is also
where the operator-norm forms now live.  They were proved here until 2026-07-28, at which
point their proofs turned out to be the ideal-gauge proofs written a second time: the two
differed only in the final estimate, over ~130 identical lines of geometric spine.  Since
`TauCeti.operatorNormFamily` has the operator norm as its gauge and every bounded operator
as a member, each operator-norm statement is its ideal-gauge counterpart read at that
family, so the copies collapsed to one — and the surviving proof has to sit *after* the
ideal one, which is downstream of this module.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient projection product for the reflected complementary subspace
has the norm of the complex sine-two-angle operator. -/
theorem norm_starProjection_reflectedComplementary_eq_sinTwoAngle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖U.starProjection ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection‖ =
      ‖directedSinTwoAngleOperatorC U V‖ := by
  let W := U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)
  have hperpProjection :
      Wᗮ.starProjection =
        boundedUnitaryConjugate V.reflection Uᗮ.starProjection := by
    ext x
    rw [Submodule.starProjection_orthogonal_apply,
      boundedUnitaryConjugate_apply,
      Submodule.starProjection_orthogonal_apply, map_sub,
      V.reflection.apply_symm_apply, Submodule.starProjection_map_apply]
  have hmapProjection :
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection =
        Wᗮ.starProjection := by
    calc
      (Uᗮ.map
          (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection =
          boundedUnitaryConjugate V.reflection Uᗮ.starProjection :=
        starProjection_map_unitary Uᗮ V.reflection
      _ = Wᗮ.starProjection := hperpProjection.symm
  rw [hmapProjection]
  calc
    ‖U.starProjection ∘L Wᗮ.starProjection‖ =
        ‖(U.starProjection ∘L Wᗮ.starProjection).adjoint‖ := by
      symm
      exact ContinuousLinearMap.adjoint.norm_map _
    _ = ‖Wᗮ.starProjection ∘L U.starProjection‖ := by
      rw [ContinuousLinearMap.adjoint_comp,
        ← ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.star_eq_adjoint,
        (isSelfAdjoint_starProjection Wᗮ).star_eq,
        (isSelfAdjoint_starProjection U).star_eq]
    _ = U.directedProjectionGap W := rfl
    _ = U.projectionGap W :=
      (subspaceGap_eq_directedGap_reflection U V).symm
    _ = ‖directedSinTwoAngleOperatorC U V‖ :=
      subspaceGap_map_reflection_eq_norm_sinTwoAngle U V

/-- The complementary overlap with the reflected complementary subspace is
exactly the norm of the sine-two-angle operator. -/
theorem norm_reflectedComplementaryOverlap_eq_sinTwoAngle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [CompleteSpace U] :
    ‖U.subtypeL.adjoint ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).subtypeL‖ =
      ‖directedSinTwoAngleOperatorC U V‖ := by
  rw [norm_adjoint_subtypeL_comp_subtypeL_eq U
    (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H))]
  exact norm_starProjection_reflectedComplementary_eq_sinTwoAngle U V


end DavisKahan
end TauCeti
