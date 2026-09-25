/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngle
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.BlockSum
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks

/-!
# The full operator angle printed in Davis--Kahan 1970

The paper defines two directed coordinate angles and then sets
`Theta = diag(Theta_0, Theta_1)`.  This file implements that literal block
operator on the orthogonal coordinate decomposition of the first subspace.
Its sine is the corresponding block sum.  A unitary coordinate change and the
cross-block identity show that its complete singular-value sequence is exactly
that of the projector difference.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `Theta = diag(Theta_0,Theta_1)` on the source orthogonal coordinates. -/
noncomputable def fullAngleBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    WithLp 2 (U × Uᗮ) →L[ℂ] WithLp 2 (U × Uᗮ) :=
  continuousOrthogonalBlockSum
    (directedAngleBlockC U V)
    (directedAngleBlockC Uᗮ Vᗮ)

/-- The literal block-diagonal `sin Theta`. -/
noncomputable def fullSinAngleBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    WithLp 2 (U × Uᗮ) →L[ℂ] WithLp 2 (U × Uᗮ) :=
  continuousOrthogonalBlockSum
    (directedSinAngleBlockC U V)
    (directedSinAngleBlockC Uᗮ Vᗮ)

/-- The cross projection sum in coordinates of `U` and `V complement`. -/
noncomputable def crossBlockSumC
    (U V : Submodule ℂ E)
      :
    WithLp 2 (U × Uᗮ) →L[ℂ] WithLp 2 (Vᗮ × (Vᗮ)ᗮ) :=
  continuousOrthogonalBlockSum
    (sineBlockC U V)
    (sineBlockC Uᗮ Vᗮ)

/-- The literal full sine and the coordinate cross-block sum have identical
complete singular-value sequences. -/
theorem sourceFullSin_same_coordinateCrossBlockSum
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (fullSinAngleBlockC U V) (crossBlockSumC U V) := by
  exact sameApproximationSingularSequence_continuousOrthogonalBlockSum
    (directedSinAngleBlock_same_sineBlock U V)
    (directedSinAngleBlock_same_sineBlock Uᗮ Vᗮ)

/-- The coordinate cross-block sum is unitarily equivalent to the ambient
cross sum printed in the paper. -/
theorem sourceCrossBlockSum_same_ambientCrossSum
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (crossBlockSumC U V) (crossSineSum V U) := by
  let Udom : E ≃ₗᵢ[ℂ] WithLp 2 (U × Uᗮ) := U.orthogonalDecomposition
  let Vcod : E ≃ₗᵢ[ℂ] WithLp 2 (Vᗮ × (Vᗮ)ᗮ) := Vᗮ.orthogonalDecomposition
  have hfactor :
      Vcod.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          crossSineSum V U ∘L
          Udom.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        crossBlockSumC U V := by
    ext x
    apply WithLp.ofLp_injective 2
    -- `orthogonalDecomposition` carries its own `simp` lemmas for application
    -- and inverse application; unfolding the definition would defeat them and
    -- expose the raw `prodEquivOfIsCompl`.
    -- The second coordinate lies in `Uᗮ`, so its `U`-projection vanishes, and
    -- anything already in `V` has vanishing `Vᗮ`-projection.
    have hUb : U.orthogonalProjectionOnto (↑x.snd : E) = 0 :=
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal x.snd.2
    have hUbStar : U.starProjection (↑x.snd : E) = 0 := by
      rw [Submodule.starProjection_apply, hUb, Submodule.coe_zero]
    -- Anything already in `V` is annihilated by the projection onto `Vᗮ`.
    have hV1 : ∀ z : E, Vᗮ.orthogonalProjectionOnto (V.starProjection z) = 0 := by
      intro z
      refine Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal ?_
      rw [Submodule.orthogonal_orthogonal]
      exact V.starProjection_apply_mem z
    -- On `Vᗮᗮ` the `V`-projection is invisible: the discarded part lies in `Vᗮ`.
    have hV2 : ∀ z : E,
        Vᗮᗮ.orthogonalProjectionOnto (V.starProjection z) =
          Vᗮᗮ.orthogonalProjectionOnto z := by
      intro z
      have hmem : z - V.starProjection z ∈ Vᗮᗮᗮ := by
        rw [Submodule.orthogonal_orthogonal]
        exact Submodule.sub_starProjection_mem_orthogonal z
      have hzero :=
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (K := Vᗮᗮ) hmem
      rw [map_sub] at hzero
      exact (sub_eq_zero.mp hzero).symm
    simp [crossBlockSumC, sineBlockC,
      crossSineSum, Udom, Vcod, Submodule.adjoint_subtypeL,
      hUbStar, hV1, hV2]
  exact (SameApproximationSingularValues.of_isometricEquiv_comp
    Vcod Udom hfactor).symm

/-- The paper's literal full `sin Theta` has exactly the singular values of
`P_U-P_V`. -/
theorem sourceFullSin_same_projectionDifference
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (fullSinAngleBlockC U V) (U.starProjection - V.starProjection) := by
  exact (sourceFullSin_same_coordinateCrossBlockSum U V).trans
    ((sourceCrossBlockSum_same_ambientCrossSum U V).trans
      (crossSineSum_same_projectionDiff V U))

/-- Every source norm gives the same value to the literal full angle sine and
the projector difference. -/
theorem sourceFullSin_mem_iff_and_gauge_eq
    (N : SymmetricNormingFunction)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (N.Mem (fullSinAngleBlockC U V) ↔
      N.Mem (U.starProjection - V.starProjection)) ∧
    N.gauge (fullSinAngleBlockC U V) =
      N.gauge (U.starProjection - V.starProjection) :=
  (sourceFullSin_same_projectionDifference U V).normingMem_iff_and_gauge_eq N

end

end ExactSinTheta
end DavisKahan
end TauCeti
