/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Core.AngleOperators
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometryBlockSum

/-!
# Finite angle operators on orthogonal block sums

The canonical finite angle operator and its totalized tangent functions preserve orthogonal direct
sums.  The sine-angle statement lives in `ForTauCeti`; this file lifts that paper-independent
operator geometry through the Davis--Kahan finite functional-calculus definitions of `Theta`,
`tan Theta`, and `tan (2 Theta)`.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical finite angle operator preserves orthogonal direct sums. -/
theorem angleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (angleOperator U₁ V₁) (angleOperator U₂ V₂) := by
  let S₁ := sinAngleOperator U₁ V₁
  let S₂ := sinAngleOperator U₂ V₂
  have hS₁ : S₁.IsSymmetric := by
    dsimp only [S₁]
    rw [TauCeti.sinAngleOperator_eq_operatorAbs]
    exact (TauCeti.isPositive_operatorAbs (projection U₁ - projection V₁)).isSymmetric
  have hS₂ : S₂.IsSymmetric := by
    dsimp only [S₂]
    rw [TauCeti.sinAngleOperator_eq_operatorAbs]
    exact (TauCeti.isPositive_operatorAbs (projection U₂ - projection V₂)).isSymmetric
  let hblock :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hS₁ hS₂
  have hsin :
      sinAngleOperator
          (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
          (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
        UnitarilyInvariantSeminorm.orthogonalBlockSum S₁ S₂ :=
    TauCeti.sinAngleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hsum : LinearMap.IsSymmetric
      (sinAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    rw [hsin]
    exact hblock
  calc
    angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      TauCeti.selfAdjointFunctionalCalculus hblock Real.arcsin := by
        unfold angleOperator
        exact TauCeti.selfAdjointFunctionalCalculus_congr_op hsum hblock hsin Real.arcsin
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (TauCeti.selfAdjointFunctionalCalculus hS₁ Real.arcsin)
          (TauCeti.selfAdjointFunctionalCalculus hS₂ Real.arcsin) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hS₁ hS₂ Real.arcsin
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (angleOperator U₁ V₁) (angleOperator U₂ V₂) := rfl

/-- The canonical finite `tan Theta` operator preserves orthogonal direct sums. -/
theorem tanAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanAngleOperator U₁ V₁) (tanAngleOperator U₂ V₂) := by
  have hangle := angleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hA₁ : (angleOperator U₁ V₁).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  have hA₂ : (angleOperator U₂ V₂).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  let hblock :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA₁ hA₂
  have hsum : LinearMap.IsSymmetric
      (angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  calc
    tanAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      TauCeti.selfAdjointFunctionalCalculus hblock safeTan := by
        unfold tanAngleOperator
        exact TauCeti.selfAdjointFunctionalCalculus_congr_op hsum hblock hangle safeTan
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (TauCeti.selfAdjointFunctionalCalculus hA₁ safeTan)
          (TauCeti.selfAdjointFunctionalCalculus hA₂ safeTan) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTan
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (tanAngleOperator U₁ V₁) (tanAngleOperator U₂ V₂) := rfl

/-- The canonical finite `tan (2 Theta)` operator preserves orthogonal direct sums. -/
theorem tanTwoAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanTwoAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanTwoAngleOperator U₁ V₁) (tanTwoAngleOperator U₂ V₂) := by
  have hangle := angleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hA₁ : (angleOperator U₁ V₁).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  have hA₂ : (angleOperator U₂ V₂).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  let hblock :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA₁ hA₂
  have hsum : LinearMap.IsSymmetric
      (angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  calc
    tanTwoAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      TauCeti.selfAdjointFunctionalCalculus hblock safeTanTwo := by
        unfold tanTwoAngleOperator
        exact TauCeti.selfAdjointFunctionalCalculus_congr_op hsum hblock hangle safeTanTwo
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (TauCeti.selfAdjointFunctionalCalculus hA₁ safeTanTwo)
          (TauCeti.selfAdjointFunctionalCalculus hA₂ safeTanTwo) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTanTwo
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (tanTwoAngleOperator U₁ V₁) (tanTwoAngleOperator U₂ V₂) := rfl

end DavisKahan.FiniteDimensional
end TauCeti
