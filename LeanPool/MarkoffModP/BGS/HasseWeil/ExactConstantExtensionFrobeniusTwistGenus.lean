/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionDifferentCoefficient
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistMultiplication
import LeanPool.MarkoffModP.RiemannRoch.CoordinateFree.AlgEquiv

/-!
# Genus of Frobenius-twist fixed fields

Extending the constants of a Frobenius-twist fixed field gives the common
exact constant extension.  Genus invariance under exact extension of finite
constants therefore identifies the genus of every twist with the genus of
the original function field.  This is Proposition 5.2.8(b) in the form used
by the uniform Stepanov estimate.
-/

namespace BGS.HasseWeil

noncomputable section


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [IsGalois (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance twistGenusBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance twistGenusBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Every canonical Frobenius-twist fixed field has the genus of the
original exact-constant Galois function field.  The equality is independent
of the auxiliary constant extension. -/
theorem genus_frobeniusTwistField_eq_original
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[RatFunc C] N) :
    let T := ExactConstantExtension C N S
    letI : Field T := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) T :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F := SubalgebraClass.toAlgebra F.toSubalgebra
    FunctionField.genus C F = FunctionField.genus C N := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  let : Algebra (RatFunc C) F := SubalgebraClass.toAlgebra F.toSubalgebra
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Algebra C F := Algebra.restrictScalars C (RatFunc C) F
  let : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hExactF : algebraicClosure C F =
      (⊥ : IntermediateField C F) :=
    exactConstantExtensionFrobeniusTwistField_algebraicClosure_eq_bot
      C (RatFunc C) N S hExact g
  let U := ExactConstantExtension C F S
  let : Field U := exactConstantExtensionField C F S hExactF
  let : Algebra S U := Algebra.TensorProduct.leftAlgebra
  let : Algebra S T := Algebra.TensorProduct.leftAlgebra
  let e : U ≃ₐ[S] T :=
    exactConstantExtensionFrobeniusTwistMultiplicationAlgEquivOverConstants
      C (RatFunc C) N S hExact g hdiv
  have hF : FunctionField.genus S U = FunctionField.genus C F :=
    exactConstantExtension_genus_eq C S F hExactF
  have hN : FunctionField.genus S T = FunctionField.genus C N :=
    exactConstantExtension_genus_eq C S N hExact
  calc
    FunctionField.genus C F = FunctionField.genus S U := hF.symm
    _ = FunctionField.genus S T := FunctionField.genus_eq_of_algEquiv e
    _ = FunctionField.genus C N := hN

end

end BGS.HasseWeil
