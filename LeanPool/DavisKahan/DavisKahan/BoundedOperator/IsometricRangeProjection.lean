/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.FrameFactorization
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-!
# Range projections of isometric embeddings

An isometric embedding has closed range, Gram operator equal to the identity,
and range projection `X X*`.  These identities are shared by residual,
generalized tangent, reflection-defect, and finite-rank comparison arguments.
-/

namespace TauCeti
namespace DavisKahan
namespace BoundedOperator

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

omit [CompleteSpace E] in
/-- The range of an isometric bounded embedding is closed. -/
theorem isClosed_range_of_isometric
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    IsClosed (Set.range X) := by
  exact ExactSinTheta.LowerFrameBound.closedRange
    (ExactSinTheta.lowerFrameBound_one_of_isometry hX) zero_lt_one

/-- The range of an isometric bounded embedding has its canonical orthogonal
projection. -/
theorem rangeHasOrthogonalProjection
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    (LinearMap.range X.toLinearMap).HasOrthogonalProjection := by
  have hset : ((LinearMap.range X.toLinearMap : Submodule 𝕜 E) : Set E) =
      Set.range X := by
    ext y
    simp [LinearMap.mem_range]
  have hclosed : IsClosed
      ((LinearMap.range X.toLinearMap : Submodule 𝕜 E) : Set E) := by
    rw [hset]
    exact isClosed_range_of_isometric hX
  have : CompleteSpace (LinearMap.range X.toLinearMap) :=
    hclosed.completeSpace_coe
  infer_instance

/-- The range projection of an isometric embedding is `X X*`. -/
theorem starProjection_range_eq_comp_adjoint
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    letI := rangeHasOrthogonalProjection X hX
    (LinearMap.range X.toLinearMap).starProjection = X ∘L X.adjoint := by
  let := rangeHasOrthogonalProjection X hX
  apply ContinuousLinearMap.ext
  intro y
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨X.adjoint y, rfl⟩
  · intro w hw
    rcases hw with ⟨z, rfl⟩
    rw [inner_sub_left]
    apply sub_eq_zero.mpr
    calc
      ⟪y, X z⟫_𝕜 = ⟪X.adjoint y, z⟫_𝕜 :=
        (ContinuousLinearMap.adjoint_inner_left X z y).symm
      _ = ⟪X (X.adjoint y), X z⟫_𝕜 := by
        let U : F →ₗᵢ[𝕜] E :=
          { toLinearMap := X.toLinearMap
            norm_map' := hX }
        exact (U.inner_map_map (X.adjoint y) z).symm

/-- The Gram operator of an isometric bounded embedding is the identity. -/
theorem adjoint_comp_isometry_eq_id
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    X.adjoint ∘L X = ContinuousLinearMap.id 𝕜 F :=
  ExactSinTheta.adjoint_comp_self_eq_id_of_isometry hX

/-- The range projection fixes the embedding. -/
theorem starProjection_range_comp_isometry
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    letI := rangeHasOrthogonalProjection X hX
    (LinearMap.range X.toLinearMap).starProjection ∘L X = X := by
  let := rangeHasOrthogonalProjection X hX
  rw [starProjection_range_eq_comp_adjoint X hX,
    ContinuousLinearMap.comp_assoc, adjoint_comp_isometry_eq_id X hX,
    ContinuousLinearMap.comp_id]

/-- The complementary range projection annihilates the embedding. -/
theorem complementaryProjection_range_comp_isometry
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    letI := rangeHasOrthogonalProjection X hX
    (LinearMap.range X.toLinearMap)ᗮ.starProjection ∘L X = 0 := by
  let := rangeHasOrthogonalProjection X hX
  rw [Submodule.starProjection_orthogonal',
    ContinuousLinearMap.sub_comp,
    starProjection_range_comp_isometry X hX]
  change ContinuousLinearMap.id 𝕜 E ∘L X - X = 0
  rw [ContinuousLinearMap.id_comp, sub_self]

/-- Both an isometric embedding and its adjoint are contractions. -/
theorem isometry_and_adjoint_norm_le_one
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    ‖X‖ ≤ 1 ∧ ‖X.adjoint‖ ≤ 1 := by
  refine ⟨ExactSinTheta.opNorm_le_one_of_isometry hX, ?_⟩
  calc
    ‖X.adjoint‖ = ‖X‖ := ContinuousLinearMap.adjoint.norm_map X
    _ ≤ 1 := ExactSinTheta.opNorm_le_one_of_isometry hX

/-- The adjoint is a left inverse pointwise. -/
theorem adjoint_apply_isometry_apply
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) (x : F) :
    X.adjoint (X x) = x := by
  have h := congrArg (fun T : F →L[𝕜] F => T x)
    (adjoint_comp_isometry_eq_id X hX)
  simpa using h

end BoundedOperator
end DavisKahan
end TauCeti
