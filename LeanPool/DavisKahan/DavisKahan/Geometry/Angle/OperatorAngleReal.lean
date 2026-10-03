/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Subspace
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex

/-!
# Real operator angles through complexification

The complex operator-angle calculus is complete.  This file specializes it to real Hilbert
subspaces by applying that calculus to their
canonical complexifications.  It avoids a second Halmos decomposition and
keeps every norm, gap, acuteness threshold, and projection identity tied to
the original real subspaces.

The operators in this file act on the complexified Hilbert space.  A later,
strictly smaller descent seam may show that the conjugation-invariant
operators preserve the canonical real copy and therefore bundle as real
operators.  All norm-level and projection-geometric content is already exact
here.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan
namespace Real

open scoped InnerProductSpace

noncomputable section

open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Symmetric sine-angle operator for real subspaces, evaluated in their
canonical complexification. -/
noncomputable def sinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Directed sine-angle operator for real subspaces in the complexification. -/
noncomputable def directedSinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  directedSinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Cosine-angle operator for real subspaces in the complexification. -/
noncomputable def directedCosAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  directedCosAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Sine of twice the real operator angle in the complexification. -/
noncomputable def directedSinTwoAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  directedSinTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Tangent-angle operator for acute real subspaces, in the complexification. -/
noncomputable def directedTanAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.DavisKahan.IsUniformlyAcute U V) :
    RealComplexification E →L[ℂ] RealComplexification E :=
  directedTanAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)
    ((isUniformlyAcute_complexifySubmodule_iff U V).2 hacute)

/-- Tangent of twice the angle for quarter-acute real subspaces. -/
noncomputable def directedTanTwoAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : TauCeti.DavisKahan.IsQuarterAcute U V) :
    RealComplexification E →L[ℂ] RealComplexification E :=
  directedTanTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)
    ((isQuarterAcute_complexifySubmodule_iff U V).2 hquarter)

/-- The real-subspace sine operator is positive. -/
theorem sinAngleOperatorRC_nonneg (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinAngleOperatorRC U V :=
  sinAngleOperatorC_nonneg _ _

/-- The real-subspace sine operator is self-adjoint. -/
theorem isSelfAdjoint_sinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sinAngleOperatorRC U V) :=
  isSelfAdjoint_sinAngleOperatorC _ _

/-- The operator norm of the complexified real sine angle is exactly the
original real projection gap. -/
theorem norm_sinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorRC U V‖ = U.projectionGap V := by
  rw [sinAngleOperatorRC, norm_sinAngleOperatorC]
  exact subspaceGap_complexifySubmodule U V

/-- Pointwise real-copy form of the sine-angle norm identity. -/
theorem norm_sinAngleOperatorRC_ofReal (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    ‖sinAngleOperatorRC U V (ofReal x)‖ =
      ‖(U.starProjection - V.starProjection) x‖ := by
  rw [sinAngleOperatorRC, norm_sinAngleOperatorC_apply]
  rw [starProjection_complexifySubmodule,
    starProjection_complexifySubmodule, ← complexify_sub,
    complexify_ofReal, LinearIsometry.norm_map]

/-- The directed sine norm is the original real directed gap. -/
theorem norm_directedSinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖directedSinAngleOperatorRC U V‖ =
      U.directedProjectionGap V := by
  rw [directedSinAngleOperatorRC, norm_directedSinAngleOperatorC]
  exact directedGap_complexifySubmodule U V

/-- The cosine operator remains contractive for real subspaces. -/
theorem norm_directedCosAngleOperatorRC_le_one (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖directedCosAngleOperatorRC U V‖ ≤ 1 :=
  norm_directedCosAngleOperatorC_le_one _ _

/-- Operator Pythagoras for real subspaces, with the right side identified as
the complexification of the original real projection. -/
theorem directedSinAngleOperatorRC_sq_add_directedCosAngleOperatorRC_sq
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    directedSinAngleOperatorRC U V * directedSinAngleOperatorRC U V +
        directedCosAngleOperatorRC U V * directedCosAngleOperatorRC U V =
      complexify U.starProjection := by
  rw [directedSinAngleOperatorRC, directedCosAngleOperatorRC,
    directedSinAngleOperatorC_sq_add_directedCosAngleOperatorC_sq,
    starProjection_complexifySubmodule]

/-- The directed sine and cosine operators commute for real subspaces. -/
theorem commute_directedSinAngleOperatorRC_directedCosAngleOperatorRC
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Commute (directedSinAngleOperatorRC U V) (directedCosAngleOperatorRC U V) :=
  commute_directedSinAngleOperatorC_directedCosAngleOperatorC _ _

/-- The complexified double-angle sine satisfies the sharp available bound in
terms of the original real directed gap. -/
theorem norm_directedSinTwoAngleOperatorRC_le (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖directedSinTwoAngleOperatorRC U V‖ ≤
      2 * U.directedProjectionGap V := by
  rw [directedSinTwoAngleOperatorRC]
  have h := norm_directedSinTwoAngleOperatorC_le
    (complexifySubmodule U) (complexifySubmodule V)
  change ‖directedSinTwoAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)‖ ≤
    2 * U.directedProjectionGap V
  change ‖directedSinTwoAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)‖ ≤
    2 * Submodule.directedProjectionGap (complexifySubmodule U)
      (complexifySubmodule V) at h
  rw [directedGap_complexifySubmodule] at h
  exact h

/-- Defining tangent identity for acute real subspaces after complexification. -/
theorem directedTanAngleOperatorRC_comp_cosAngleExtended
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hacute : TauCeti.DavisKahan.IsUniformlyAcute U V) :
    directedTanAngleOperatorRC U V hacute ∘L
        cosAngleExtendedC (complexifySubmodule U) (complexifySubmodule V) =
      directedSinAngleOperatorRC U V := by
  exact directedTanAngleOperatorC_comp_cosAngleExtendedC
    (complexifySubmodule U) (complexifySubmodule V)
    ((isUniformlyAcute_complexifySubmodule_iff U V).2 hacute)

/-- Defining double-tangent identity below the real quarter-angle threshold. -/
theorem directedTanTwoAngleOperatorRC_comp_cosTwoAngleExtended
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hquarter : TauCeti.DavisKahan.IsQuarterAcute U V) :
    directedTanTwoAngleOperatorRC U V hquarter ∘L
        cosTwoAngleExtendedC (complexifySubmodule U) (complexifySubmodule V) =
      directedSinTwoAngleOperatorRC U V := by
  exact directedTanTwoAngleOperatorC_comp_cosTwoAngleExtendedC
    (complexifySubmodule U) (complexifySubmodule V)
    ((isQuarterAcute_complexifySubmodule_iff U V).2 hquarter)

end

end Real
end DavisKahan.Angle
end TauCeti
