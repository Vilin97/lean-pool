/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSum

/-!
# Orthogonal block sums and finite angle functional calculus

Reusable compatibility results for orthogonal direct sums.  The projector, modulus, and finite
self-adjoint functional calculus all preserve block-diagonal decompositions, so the angle operator
of a direct sum of subspace pairs is the block sum of the two angle operators.

This is paper-independent operator geometry.  Davis--Kahan sharpness uses it to turn block-matrix
model equalities into equalities for an actual pair of direct-sum subspaces.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

private noncomputable def blockInlLinear
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] :
    E₁ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
  (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).symm.toLinearMap ∘ₗ LinearMap.inl 𝕜 E₁ E₂

private noncomputable def blockInrLinear
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] :
    E₂ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
  (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E₁ E₂

@[simp] private theorem blockInlLinear_apply
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (x : E₁) :
    blockInlLinear (𝕜 := 𝕜) (E₂ := E₂) x = WithLp.toLp 2 (x, (0 : E₂)) := rfl

@[simp] private theorem blockInrLinear_apply
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (x : E₂) :
    blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) x = WithLp.toLp 2 ((0 : E₁), x) := rfl

private theorem blockInlLinear_intertwines
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    blockInlLinear (𝕜 := 𝕜) (E₂ := E₂) ∘ₗ A =
      UnitarilyInvariantSeminorm.orthogonalBlockSum A B ∘ₗ
        blockInlLinear (𝕜 := 𝕜) (E₂ := E₂) := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [UnitarilyInvariantSeminorm.orthogonalBlockSum_apply]

private theorem blockInrLinear_intertwines
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) ∘ₗ B =
      UnitarilyInvariantSeminorm.orthogonalBlockSum A B ∘ₗ
        blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [UnitarilyInvariantSeminorm.orthogonalBlockSum_apply]

/-- **Finite self-adjoint functional calculus preserves an orthogonal block sum.** -/
theorem selfAdjointFunctionalCalculus_orthogonalBlockSum
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    {A : E₁ →ₗ[𝕜] E₁} (hA : A.IsSymmetric)
    {B : E₂ →ₗ[𝕜] E₂} (hB : B.IsSymmetric) (f : ℝ → ℝ) :
    let hAB := UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA hB
    selfAdjointFunctionalCalculus hAB f =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (selfAdjointFunctionalCalculus hA f) (selfAdjointFunctionalCalculus hB f) := by
  dsimp only
  let J₁ : E₁ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
    blockInlLinear (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂)
  let J₂ : E₂ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
    blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂)
  let T : WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum A B
  let hT : T.IsSymmetric :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA hB
  have hJ₁ : J₁ ∘ₗ A = T ∘ₗ J₁ := blockInlLinear_intertwines A B
  have hJ₂ : J₂ ∘ₗ B = T ∘ₗ J₂ := blockInrLinear_intertwines A B
  have hfc₁ := selfAdjointFunctionalCalculus_intertwines hA hT J₁ hJ₁ f
  have hfc₂ := selfAdjointFunctionalCalculus_intertwines hB hT J₂ hJ₂ f
  apply LinearMap.ext
  intro x
  have hx : x = J₁ x.ofLp.1 + J₂ x.ofLp.2 := by
    apply (WithLp.ext_iff (p := 2)).mpr
    apply Prod.ext_iff.mpr
    constructor <;> simp [J₁, J₂]
  have h₁ :
      selfAdjointFunctionalCalculus hT f (J₁ x.ofLp.1) =
        J₁ (selfAdjointFunctionalCalculus hA f x.ofLp.1) := by
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun hfc₁ x.ofLp.1).symm
  have h₂ :
      selfAdjointFunctionalCalculus hT f (J₂ x.ofLp.2) =
        J₂ (selfAdjointFunctionalCalculus hB f x.ofLp.2) := by
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun hfc₂ x.ofLp.2).symm
  calc
    selfAdjointFunctionalCalculus hT f x
        = selfAdjointFunctionalCalculus hT f (J₁ x.ofLp.1 + J₂ x.ofLp.2) := by rw [← hx]
    _ = selfAdjointFunctionalCalculus hT f (J₁ x.ofLp.1) +
          selfAdjointFunctionalCalculus hT f (J₂ x.ofLp.2) := map_add _ _ _
    _ = J₁ (selfAdjointFunctionalCalculus hA f x.ofLp.1) +
          J₂ (selfAdjointFunctionalCalculus hB f x.ofLp.2) := by rw [h₁, h₂]
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (selfAdjointFunctionalCalculus hA f) (selfAdjointFunctionalCalculus hB f) x := by
        apply WithLp.ofLp_injective 2
        simp [J₁, J₂, UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The projector onto an orthogonal block sum of subspaces is the block sum of the
projectors, in the canonical `projection` spelling used by finite angle geometry. -/
theorem projection_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂) :
    projection
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (projection U₁) (projection U₂) :=
  UnitarilyInvariantSeminorm.starProjection_orthogonalBlockSumSubmodule U₁ U₂

/-- **The sine-angle operator of an orthogonal sum of subspace pairs is block-diagonal.** -/
theorem sinAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    sinAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (sinAngleOperator U₁ V₁) (sinAngleOperator U₂ V₂) := by
  rw [sinAngleOperator_eq_operatorAbs
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂),
    sinAngleOperator_eq_operatorAbs U₁ V₁,
    sinAngleOperator_eq_operatorAbs U₂ V₂,
    projection_orthogonalBlockSumSubmodule U₁ U₂,
    projection_orthogonalBlockSumSubmodule V₁ V₂,
    ← UnitarilyInvariantSeminorm.orthogonalBlockSum_sub,
    UnitarilyInvariantSeminorm.operatorAbs_orthogonalBlockSum]

end TauCeti
