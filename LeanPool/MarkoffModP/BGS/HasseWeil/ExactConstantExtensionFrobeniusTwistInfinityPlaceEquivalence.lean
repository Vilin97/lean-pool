/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistInfinityPlaceDescent

/-!
# Exact Frobenius-twist descent for infinity places

This file specializes the generic infinity-place descent theory to an exact
constant extension.  It identifies rational infinity places of the
Frobenius-twist fixed field with degree-`[S : C]` infinity places upstairs
fixed by the ambient Frobenius twist.
-/

open scoped Pointwise Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


variable (C N S : Type*) [Field C] [Fintype C]
  [DecidableEq C] [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Field S] [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Finite S] [DecidableEq S] [DecidableEq (RatFunc S)]

local instance twistInfinityEquivalenceConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance twistInfinityEquivalenceConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

section FrobeniusTwistInfinitySpecialization

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))
variable (g : N ≃ₐ[RatFunc C] N)

omit [DecidableEq C] [DecidableEq (RatFunc C)]
  [DecidableEq S] [DecidableEq (RatFunc S)] in
/-- A top infinity place of degree `[S : C]` fixed by the canonical twist
descends to a rational infinity place of the Frobenius-twist fixed field. -/
theorem frobeniusTwistField_fixed_infinityPlace_under_degree_eq_one
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F :=
      SubalgebraClass.toAlgebra F.toSubalgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
    letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    letI : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module F (ExactConstantExtension C N S) := Algebra.toModule
    letI : DistribMulAction F (ExactConstantExtension C N S) :=
      Module.toDistribMulAction
    letI : MulAction F (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : IsScalarTower (RatFunc C) F
        (ExactConstantExtension C N S) := inferInstance
    letI : FiniteDimensional F (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    letI : IsGalois F (ExactConstantExtension C N S) :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    ∀ (Q : FiniteExtensionInfinityPlace C (ExactConstantExtension C N S)),
      finiteExtensionPlaceDegree C (ExactConstantExtension C N S) (.inr Q) =
          Module.finrank C S →
        infinityPlaceGalSmul C F (ExactConstantExtension C N S)
            (exactConstantExtensionFrobeniusTwistOverFixedField
              C N S hExact g) Q = Q →
          finiteExtensionPlaceDegree C F
            (.inr (infinityPlaceUnder C F
              (ExactConstantExtension C N S) Q)) = 1 := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
  letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra F T := F.toAlgebra
  letI : SMul F T := Algebra.toSMul
  letI : Module F T := Algebra.toModule
  letI : DistribMulAction F T := Module.toDistribMulAction
  letI : MulAction F T := DistribMulAction.toMulAction
  letI : IsScalarTower (RatFunc C) F T := inferInstance
  letI : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  letI : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  dsimp only
  intro Q hdegree hfixed
  apply infinityPlaceUnder_degree_eq_one_of_generator_fixed
    C F T
    (exactConstantExtensionFrobeniusTwistOverFixedField C N S hExact g)
    (exactConstantExtensionFrobeniusTwistOverFixedField_zpowers_eq_top
      C N S hExact g)
    Q hfixed
  · exact frobeniusTwistField_infinityPlace_ramificationIdx_eq_one
      C N S hExact g hdiv Q
  · calc
      finiteExtensionPlaceDegree C T (.inr Q) = Module.finrank C S := hdegree
      _ = Module.finrank F T :=
        (finrank_exactConstantExtension_over_frobeniusTwistField
          C (RatFunc C) N S hExact g hdiv).symm

omit [DecidableEq C] [DecidableEq (RatFunc C)]
  [DecidableEq S] [DecidableEq (RatFunc S)] in
/-- The canonical twist over its fixed field and the ambient twist over
`C(X)` induce the same action on infinity places. -/
theorem exactConstantExtensionFrobeniusTwist_infinityPlaceGalSmul_eq_overFixedField
    [IsGalois (RatFunc C) N] :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : IsGalois (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C (RatFunc C) N S hExact
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F :=
      SubalgebraClass.toAlgebra F.toSubalgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
    letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    letI : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module F (ExactConstantExtension C N S) := Algebra.toModule
    letI : DistribMulAction F (ExactConstantExtension C N S) :=
      Module.toDistribMulAction
    letI : MulAction F (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : IsScalarTower (RatFunc C) F
        (ExactConstantExtension C N S) := inferInstance
    letI : FiniteDimensional F (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    letI : IsGalois F (ExactConstantExtension C N S) :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    ∀ Q : FiniteExtensionInfinityPlace C (ExactConstantExtension C N S),
      infinityPlaceGalSmul C F (ExactConstantExtension C N S)
          (exactConstantExtensionFrobeniusTwistOverFixedField
            C N S hExact g) Q =
        infinityPlaceGalSmul C (RatFunc C) (ExactConstantExtension C N S)
          (exactConstantExtensionFrobeniusTwist
            C (RatFunc C) N S hExact g) Q := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
  letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra F T := F.toAlgebra
  letI : SMul F T := Algebra.toSMul
  letI : Module F T := Algebra.toModule
  letI : DistribMulAction F T := Module.toDistribMulAction
  letI : MulAction F T := DistribMulAction.toMulAction
  letI : IsScalarTower (RatFunc C) F T := inferInstance
  letI : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  letI : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  dsimp only
  intro Q
  apply infinityPlaceGalSmul_eq_of_apply_eq C F (RatFunc C) T
  intro x
  exact exactConstantExtensionFrobeniusTwistOverFixedField_apply
    C N S hExact g x

omit [DecidableEq C] [DecidableEq (RatFunc C)]
  [DecidableEq S] [DecidableEq (RatFunc S)] in
/-- Ambient fixedness by the Frobenius twist is exactly the fixedness
condition needed for infinity-place descent. -/
theorem frobeniusTwistField_ambientFixed_infinityPlace_under_degree_eq_one
    [IsGalois (RatFunc C) N]
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : IsGalois (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C (RatFunc C) N S hExact
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F :=
      SubalgebraClass.toAlgebra F.toSubalgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
    letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    letI : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module F (ExactConstantExtension C N S) := Algebra.toModule
    letI : DistribMulAction F (ExactConstantExtension C N S) :=
      Module.toDistribMulAction
    letI : MulAction F (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : IsScalarTower (RatFunc C) F
        (ExactConstantExtension C N S) := inferInstance
    letI : FiniteDimensional F (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    letI : IsGalois F (ExactConstantExtension C N S) :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    ∀ (Q : FiniteExtensionInfinityPlace C (ExactConstantExtension C N S)),
      finiteExtensionPlaceDegree C (ExactConstantExtension C N S) (.inr Q) =
          Module.finrank C S →
        infinityPlaceGalSmul C (RatFunc C) (ExactConstantExtension C N S)
            (exactConstantExtensionFrobeniusTwist
              C (RatFunc C) N S hExact g) Q = Q →
          finiteExtensionPlaceDegree C F
            (.inr (infinityPlaceUnder C F
              (ExactConstantExtension C N S) Q)) = 1 := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
  letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra F T := F.toAlgebra
  letI : SMul F T := Algebra.toSMul
  letI : Module F T := Algebra.toModule
  letI : DistribMulAction F T := Module.toDistribMulAction
  letI : MulAction F T := DistribMulAction.toMulAction
  letI : IsScalarTower (RatFunc C) F T := inferInstance
  letI : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  letI : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  dsimp only
  intro Q hdegree hfixed
  apply frobeniusTwistField_fixed_infinityPlace_under_degree_eq_one
    C N S hExact g hdiv Q hdegree
  rw [exactConstantExtensionFrobeniusTwist_infinityPlaceGalSmul_eq_overFixedField
    C N S hExact g Q]
  exact hfixed

/-- Rational infinity places of the Frobenius-twist field are exactly the
degree-`[S : C]` top infinity places fixed by the ambient Frobenius twist. -/
noncomputable def
    frobeniusTwistField_rationalInfinityPlace_equiv_ambientFixedInfinityPlace
    [IsGalois (RatFunc C) N]
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : IsGalois (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C (RatFunc C) N S hExact
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F :=
      SubalgebraClass.toAlgebra F.toSubalgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
    letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    letI : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module F (ExactConstantExtension C N S) := Algebra.toModule
    letI : DistribMulAction F (ExactConstantExtension C N S) :=
      Module.toDistribMulAction
    letI : MulAction F (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : IsScalarTower (RatFunc C) F
        (ExactConstantExtension C N S) := inferInstance
    letI : FiniteDimensional F (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    letI : IsGalois F (ExactConstantExtension C N S) :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    FiniteExtensionRationalInfinityPlace C F ≃
      {Q : FiniteExtensionInfinityPlace C (ExactConstantExtension C N S) //
        finiteExtensionPlaceDegree C (ExactConstantExtension C N S) (.inr Q) =
            Module.finrank C S ∧
          infinityPlaceGalSmul C (RatFunc C) (ExactConstantExtension C N S)
            (exactConstantExtensionFrobeniusTwist
              C (RatFunc C) N S hExact g) Q = Q} := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : DistribMulAction (RatFunc C) F := Module.toDistribMulAction
  letI : MulAction (RatFunc C) F := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra F T := F.toAlgebra
  letI : SMul F T := Algebra.toSMul
  letI : Module F T := Algebra.toModule
  letI : DistribMulAction F T := Module.toDistribMulAction
  letI : MulAction F T := DistribMulAction.toMulAction
  letI : IsScalarTower (RatFunc C) F T := inferInstance
  letI : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  letI : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  dsimp only
  have hfinrank : Module.finrank F T = Module.finrank C S :=
    finrank_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g hdiv
  have hdegree : ∀ Q : FiniteExtensionInfinityPlace C T,
      Module.finrank F T ∣ finiteExtensionPlaceDegree C T (.inr Q) := by
    intro Q
    rw [hfinrank]
    exact exactConstantExtensionInfinityPlace_finrank_constants_dvd_degree
      C N S hExact Q
  let sigmaF :=
    exactConstantExtensionFrobeniusTwistOverFixedField C N S hExact g
  let eFixed := rationalInfinityPlaceEquivGeneratorFixedPlace
    C F T hdegree sigmaF
      (exactConstantExtensionFrobeniusTwistOverFixedField_zpowers_eq_top
        C N S hExact g)
      (frobeniusTwistField_infinityPlace_ramificationIdx_eq_one
        C N S hExact g hdiv)
  let eCompare :
      {Q : FiniteExtensionInfinityPlace C T //
        finiteExtensionPlaceDegree C T (.inr Q) = Module.finrank F T ∧
          infinityPlaceGalSmul C F T sigmaF Q = Q} ≃
      {Q : FiniteExtensionInfinityPlace C T //
        finiteExtensionPlaceDegree C T (.inr Q) = Module.finrank C S ∧
          infinityPlaceGalSmul C (RatFunc C) T
            (exactConstantExtensionFrobeniusTwist
              C (RatFunc C) N S hExact g) Q = Q} :=
    { toFun := fun Q => ⟨Q.1,
        Q.2.1.trans hfinrank,
        (exactConstantExtensionFrobeniusTwist_infinityPlaceGalSmul_eq_overFixedField
          C N S hExact g Q.1).symm.trans Q.2.2⟩
      invFun := fun Q => ⟨Q.1,
        Q.2.1.trans hfinrank.symm,
        (exactConstantExtensionFrobeniusTwist_infinityPlaceGalSmul_eq_overFixedField
          C N S hExact g Q.1).trans Q.2.2⟩
      left_inv := fun Q => Subtype.ext rfl
      right_inv := fun Q => Subtype.ext rfl }
  exact eFixed.trans eCompare

end FrobeniusTwistInfinitySpecialization


end

end BGS.HasseWeil
