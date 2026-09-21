/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Reflection
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReflectionRestriction
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-! # Reflected Defect Doubling -/

open TauCeti.DavisKahan.Sylvester

/-!
# The sharp factor two of the reflection proof

The `sin 2θ` proof of Davis--Kahan 1970, Section 7, would lose the printed
constant if the reflection defect `D = J_V S J_V - S` were split by a triangle
inequality into its two off-diagonal blocks: that gives four, not two.

The identity that saves the constant is a multiplicity count.  Read between an
exact subspace `U` and the mirror `J_V Uᗮ` of its complement, the two
complementary blocks of `D` have the same complete singular sequence, because
conjugating by `J_V` is isometric and `D` anticommutes with `J_V`.  So an even
Ky Fan prefix of the pinched pair is exactly twice the prefix of one block, and
the same count applied to the off-diagonal pair of `S` itself removes the second
copy.

`kyFan_reflectionDefectBlock_le_two_mul` is that statement.  It mentions no
spectral gap and no ambient operator beyond `S`, so it serves the bounded
`sin 2Θ₀` theorem, the unbounded one — where `S` is the off-diagonal part built
from the trial residual rather than a compression of the ambient operator — and
both scalar fields.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The projection onto a mirrored subspace is the conjugated projection. -/
private theorem starProjection_map_reflectionOperator
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection =
      V.reflectionOperator ∘L U.starProjection ∘L V.reflectionOperator := by
  rw [starProjection_map_unitary U V.reflection]
  unfold boundedUnitaryConjugate
  rw [Submodule.reflection_symm]
  rfl

/-- The reflection defect of a self-adjoint operator is self-adjoint. -/
private theorem isSelfAdjoint_reflectionDefect
    {S : E →L[𝕜] E} (hS : IsSelfAdjoint S) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] : IsSelfAdjoint (reflectionDefect V S) := by
  have hJ : IsSelfAdjoint (V.reflectionOperator : E →L[𝕜] E) :=
    isSelfAdjoint_reflectionOperator V
  unfold reflectionDefect
  rw [IsSelfAdjoint, star_sub, hS.star_eq]
  congr 1
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, star_mul,
    star_mul, hJ.star_eq, hS.star_eq]
  rfl

/-- The two complementary blocks of a reflection defect, read between a subspace
and the mirror of its complement, have the same complete singular sequence. -/
private theorem reflectedDefectBlocks_same
    {S : E →L[𝕜] E} (hS : IsSelfAdjoint S) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (projectionBlock (U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E))ᗮ U
        (reflectionDefect V S))
      (projectionBlock
        ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E))ᗮ)ᗮ Uᗮ
        (reflectionDefect V S)) := by
  set W := U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E) with hW
  set D := reflectionDefect V S with hD
  have hDsa : IsSelfAdjoint D := isSelfAdjoint_reflectionDefect hS V
  have hperp : Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E) = Wᗮ :=
    Submodule.map_orthogonal_equiv U V.reflection
  have hWproj : W.starProjection =
      V.reflectionOperator ∘L U.starProjection ∘L V.reflectionOperator :=
    starProjection_map_reflectionOperator U V
  have hWperpProj : Wᗮ.starProjection =
      V.reflectionOperator ∘L Uᗮ.starProjection ∘L V.reflectionOperator := by
    rw [← Submodule.starProjection_congr hperp]
    exact starProjection_map_reflectionOperator Uᗮ V
  have hB₀adj : (projectionBlock Wᗮ U D).adjoint =
      U.starProjection ∘L D ∘L Wᗮ.starProjection := by
    rw [projectionBlock, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection Wᗮ).adjoint_eq,
      hDsa.adjoint_eq, (isSelfAdjoint_starProjection U).adjoint_eq]
    rfl
  have hanti : V.reflectionOperator ∘L D = -(D ∘L V.reflectionOperator) :=
    reflectionOperator_comp_reflectionDefect V S
  have hblock : projectionBlock Wᗮᗮ Uᗮ D =
      -(V.reflectionOperator ∘L (projectionBlock Wᗮ U D).adjoint ∘L
        V.reflectionOperator) := by
    have hWW : Wᗮᗮ.starProjection = W.starProjection :=
      Submodule.starProjection_congr (Submodule.orthogonal_orthogonal W)
    rw [hB₀adj, projectionBlock, hWW, hWproj, hWperpProj]
    ext x
    simp only [ContinuousLinearMap.comp_apply, neg_apply]
    rw [reflectionOperator_apply_apply V x]
    have hanti_x := congrArg
      (fun T : E →L[𝕜] E => T (Uᗮ.starProjection x)) hanti
    simp only [ContinuousLinearMap.comp_apply, neg_apply] at hanti_x
    rw [hanti_x]
    simp only [map_neg]
  intro n
  rw [hblock, ContinuousLinearMap.approximationNumber_neg]
  have hright := sameApproximationSingularValues_comp_reflection_right V
    (V.reflectionOperator ∘L (projectionBlock Wᗮ U D).adjoint)
  have hleft := sameApproximationSingularValues_comp_reflection_left V
    (projectionBlock Wᗮ U D).adjoint
  calc
    (projectionBlock Wᗮ U D).approximationNumber n =
        (projectionBlock Wᗮ U D).adjoint.approximationNumber n :=
      (ContinuousLinearMap.approximationNumber_adjoint _ n).symm
    _ = (V.reflectionOperator ∘L
          (projectionBlock Wᗮ U D).adjoint).approximationNumber n :=
      (hleft n).symm
    _ = (V.reflectionOperator ∘L (projectionBlock Wᗮ U D).adjoint ∘L
          V.reflectionOperator).approximationNumber n :=
      (hright n).symm

/-- The two off-diagonal blocks of a self-adjoint operator have the same
complete singular sequence. -/
private theorem offDiagonalBlocks_same
    {S : E →L[𝕜] E} (hS : IsSelfAdjoint S) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (projectionBlock Vᗮ V S)
      (projectionBlock Vᗮᗮ Vᗮ S) := by
  have hadj : (projectionBlock Vᗮ V S).adjoint =
      projectionBlock V Vᗮ S := by
    rw [projectionBlock, projectionBlock,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection Vᗮ).adjoint_eq, hS.adjoint_eq,
      (isSelfAdjoint_starProjection V).adjoint_eq]
    rfl
  have hperpBlock : projectionBlock Vᗮᗮ Vᗮ S =
      projectionBlock V Vᗮ S := by
    have hp : Vᗮᗮ.starProjection = V.starProjection :=
      Submodule.starProjection_congr (Submodule.orthogonal_orthogonal V)
    unfold projectionBlock
    rw [hp]
  intro n
  calc
    (projectionBlock Vᗮ V S).approximationNumber n =
        (projectionBlock Vᗮ V S).adjoint.approximationNumber n :=
      (ContinuousLinearMap.approximationNumber_adjoint _ n).symm
    _ = (projectionBlock V Vᗮ S).approximationNumber n := by rw [hadj]
    _ = (projectionBlock Vᗮᗮ Vᗮ S).approximationNumber n := by
      rw [hperpBlock]

/-- **The sharp factor two for a reflection defect, at every Ky Fan gauge.**

Read between the subspace `U` and the mirror of its complement, the reflection
defect of a bounded self-adjoint `S` through `V` costs at most *twice* one
off-diagonal block of `S`, not four times it.

This is the geometric half of the directed residual `sin 2Θ₀` estimate. -/
theorem kyFan_reflectionDefectBlock_le_two_mul
    {S : E →L[𝕜] E} (hS : IsSelfAdjoint S) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (k : ℕ) :
    kyFanApproximationGauge k
        ((Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection ∘L
          reflectionDefect V S ∘L U.starProjection) ≤
      2 * kyFanApproximationGauge k
        (Vᗮ.starProjection ∘L S ∘L V.starProjection) := by
  set W := U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E) with hW
  set D := reflectionDefect V S with hD
  have hperp : Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E) = Wᗮ :=
    Submodule.map_orthogonal_equiv U V.reflection
  have hstart :
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection ∘L D ∘L
          U.starProjection = projectionBlock Wᗮ U D := by
    unfold projectionBlock
    rw [Submodule.starProjection_congr hperp]
  rw [hstart]
  have hpairD := diagonalPair_even_kyFan_eq_two_mul_of_same Wᗮ U D
    (reflectedDefectBlocks_same hS U V) k
  have hpinchD := diagonalPair_all_kyFan_le Wᗮ U D (2 * k)
  have hpairA := diagonalPair_even_kyFan_eq_two_mul_of_same Vᗮ V S
    (offDiagonalBlocks_same hS V) k
  have hpairAdef : diagonalPair Vᗮ V S =
      Vᗮ.starProjection ∘L S ∘L V.starProjection +
        V.starProjection ∘L S ∘L Vᗮ.starProjection := by
    have hp : Vᗮᗮ.starProjection = V.starProjection :=
      Submodule.starProjection_congr (Submodule.orthogonal_orthogonal V)
    unfold diagonalPair
    rw [hp]
  have hoffdiag : D = (-2 : 𝕜) • diagonalPair Vᗮ V S := by
    rw [hD, reflectionDefect_eq_neg_two_smul_offdiag, hpairAdef]
  have hDgauge : kyFanApproximationGauge (2 * k) D =
      4 * kyFanApproximationGauge k
        (Vᗮ.starProjection ∘L S ∘L V.starProjection) := by
    rw [hoffdiag, kyFanApproximationGauge_smul]
    have hnorm : ‖(-2 : 𝕜)‖ = 2 := by
      rw [norm_neg]
      simp
    rw [hnorm, hpairA]
    simp only [projectionBlock]
    ring_nf
  rw [hpairD] at hpinchD
  rw [hDgauge] at hpinchD
  linarith

end

end DavisKahan1970
end TauCeti
