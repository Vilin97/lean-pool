/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.TensorProduct.Lemmas
import LeanPool.Monlib4.LinearAlgebra.LinearMapOp
import LeanPool.Monlib4.LinearAlgebra.Coalgebra.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-!
# LeanPool.Monlib4.LinearAlgebra.Coalgebra.MulOpposite

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.Coalgebra.MulOpposite`.
-/

open scoped TensorProduct

/-- The tensor product of multiplicative opposites as the opposite of a tensor product. -/
noncomputable def TensorProduct.opLinearEquiv
  {R A B : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] :
    (A ⊗[R] B)ᵐᵒᵖ ≃ₗ[R] Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv R (M := A ⊗[R] B)).symm.trans
    (LinearEquiv.TensorProduct.map
      (MulOpposite.opLinearEquiv R)
      (MulOpposite.opLinearEquiv R))

@[simp]
lemma TensorProduct.opLinearEquiv_tmul
  {R A B : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  (x : A) (y : B) :
  opLinearEquiv (MulOpposite.op (x ⊗ₜ[R] y))
    = MulOpposite.op x ⊗ₜ[R] MulOpposite.op y :=
rfl
@[simp]
lemma TensorProduct.opLinearEquiv_symm_tmul
  {R A B : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  (x : Aᵐᵒᵖ) (y : Bᵐᵒᵖ) :
  opLinearEquiv.symm (x ⊗ₜ[R] y)
    = MulOpposite.op (x.unop ⊗ₜ[R] y.unop) :=
rfl

noncomputable instance MulOpposite.coalgebraStruct
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [CoalgebraStruct R A] :
  CoalgebraStruct R Aᵐᵒᵖ where
  comul := TensorProduct.opLinearEquiv.toLinearMap ∘ₗ Coalgebra.comul.op
  counit := Coalgebra.counit ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap

lemma MulOpposite.comul_def
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [CoalgebraStruct R A] :
  (CoalgebraStruct.comul (R := R) (A := Aᵐᵒᵖ)) =
    TensorProduct.opLinearEquiv.toLinearMap ∘ₗ CoalgebraStruct.comul.op :=
rfl
lemma MulOpposite.comul_def'
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [CoalgebraStruct R A] :
  (CoalgebraStruct.comul (R := R) (A := Aᵐᵒᵖ)) =
    (TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (MulOpposite.opLinearEquiv R).toLinearMap) ∘ₗ
      CoalgebraStruct.comul ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap :=
rfl
lemma MulOpposite.counit_def
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [CoalgebraStruct R A] :
  (CoalgebraStruct.counit (R := R) (A := Aᵐᵒᵖ)) =
    CoalgebraStruct.counit ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap :=
rfl

private lemma coassoc_aux_1
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A]
  [Module R A] :
  (TensorProduct.assoc R Aᵐᵒᵖ Aᵐᵒᵖ Aᵐᵒᵖ).toLinearMap ∘ₗ
    (TensorProduct.opLinearEquiv.toLinearMap
      ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap).rTensor Aᵐᵒᵖ
  -- = 0:=
  -- ((TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
  --   (MulOpposite.opLinearEquiv R).toLinearMap)).rTensor A
  = (TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (((MulOpposite.opLinearEquiv R).toLinearMap.rTensor _)))
    ∘ₗ (TensorProduct.assoc R A A _).toLinearMap :=
  --     ∘ₗ ((CoalgebraStruct.comul (R:=R) (A:=A)).rTensor A))
  --   ∘ₗ ((MulOpposite.opLinearEquiv R).symm.rTensor Aᵐᵒᵖ).toLinearMap :=
by
    apply TensorProduct.ext_threefold
    intro x y z
    simp

private lemma coassoc_aux_2
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A]
  [Module R A] :
  (MulOpposite.opLinearEquiv R).symm.toLinearMap.rTensor _
    ∘ₗ ((TensorProduct.opLinearEquiv (A := A) (B := A)).toLinearMap)
    ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap
  = (MulOpposite.opLinearEquiv R).toLinearMap.lTensor A :=
by
    apply TensorProduct.ext'
    intro x y
    simp

private lemma coassoc_aux3
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A]
  [Module R A] :
  (TensorProduct.map (MulOpposite.opLinearEquiv R (M:=A)).toLinearMap
      (((MulOpposite.opLinearEquiv R (M:=A)).toLinearMap.rTensor Aᵐᵒᵖ)))
        ∘ₗ ((TensorProduct.assoc R A A Aᵐᵒᵖ).toLinearMap)
        ∘ₗ (MulOpposite.opLinearEquiv R (M:=A)).toLinearMap.lTensor _
    =
    TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
        ((TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (MulOpposite.opLinearEquiv R).toLinearMap))
        ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap :=
by
    apply TensorProduct.ext_threefold
    intro x y z
    simp

lemma LinearMap.op_eq
  {R A B : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
  (f : A →ₗ[R] B) :
  f.op =
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
      f ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap :=
rfl

open CoalgebraStruct in
private lemma MulOpposite_coassoc
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [Coalgebra R A] :
    (TensorProduct.assoc R Aᵐᵒᵖ Aᵐᵒᵖ Aᵐᵒᵖ) ∘ₗ
      (comul (R := R) (A := Aᵐᵒᵖ)).rTensor Aᵐᵒᵖ ∘ₗ
        (comul (R := R) (A := Aᵐᵒᵖ)) =
    (comul (R := R) (A := Aᵐᵒᵖ)).lTensor Aᵐᵒᵖ ∘ₗ
      (comul (R := R) (A := Aᵐᵒᵖ)) :=
by
  calc
    (TensorProduct.assoc R Aᵐᵒᵖ Aᵐᵒᵖ Aᵐᵒᵖ).toLinearMap ∘ₗ
      (comul (R := R) (A := Aᵐᵒᵖ)).rTensor Aᵐᵒᵖ ∘ₗ
        (comul (R := R) (A := Aᵐᵒᵖ))
      = ((TensorProduct.assoc R Aᵐᵒᵖ Aᵐᵒᵖ Aᵐᵒᵖ).toLinearMap ∘ₗ
        (TensorProduct.opLinearEquiv.toLinearMap
        ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap).rTensor _)
        ∘ₗ (comul (R := R) (A := A)).rTensor _
        ∘ₗ ((MulOpposite.opLinearEquiv R).symm.toLinearMap.rTensor _
          ∘ₗ (TensorProduct.opLinearEquiv.toLinearMap)
          ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap)
        ∘ₗ (comul (R:=R) (A:=A)) ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap := by
          simp only [comul, LinearMap.comp_assoc, LinearMap.op_eq]
          congr 1
          simp only [LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = ((TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (((MulOpposite.opLinearEquiv R).toLinearMap.rTensor _)))
        ∘ₗ (TensorProduct.assoc R A A _).toLinearMap)
        ∘ₗ ((comul (R:=R) (A:=A)).rTensor _
        ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap.lTensor A)
        ∘ₗ (comul (R:=R) (A:=A)) ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap := by
          rw [coassoc_aux_1, coassoc_aux_2]
          simp only [LinearMap.comp_assoc]
    _ = ((TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (((MulOpposite.opLinearEquiv R).toLinearMap.rTensor _)))
        ∘ₗ ((TensorProduct.assoc R A A _).toLinearMap)
        ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap.lTensor _)
        ∘ₗ (comul (R:=R) (A:=A)).rTensor _
        ∘ₗ (comul (R:=R) (A:=A)) ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap := by
          rw [rTensor_comp_lTensor']
          simp only [LinearMap.comp_assoc]
    _ = TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
        ((TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (MulOpposite.opLinearEquiv R).toLinearMap))
        ∘ₗ ((TensorProduct.assoc R _ _ _).toLinearMap
        ∘ₗ (comul (R:=R) (A:=A)).rTensor _
        ∘ₗ (comul (R:=R) (A:=A))) ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap := by
          rw [coassoc_aux3]
          simp only [LinearMap.comp_assoc]
    _ = TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
        ((TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (MulOpposite.opLinearEquiv R).toLinearMap))
        ∘ₗ (comul (R:=R) (A:=A)).lTensor A ∘ₗ (comul (R:=R) (A:=A))
        ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap := by
          rw [Coalgebra.coassoc]
          simp only [LinearMap.comp_assoc]
    _ = TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      ((comul (R := R) (A := Aᵐᵒᵖ)) ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap)
          ∘ₗ (comul (R:=R) (A:=A)) ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap := by
            nth_rw 1 [MulOpposite.comul_def]
            rw [← LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
            simp only [LinearMap.comp_assoc]
            rfl
    _ = (comul (R := R) (A := Aᵐᵒᵖ)).lTensor _
      ∘ₗ (TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      ((MulOpposite.opLinearEquiv R).toLinearMap)
          ∘ₗ (comul (R:=R) (A:=A)) ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap) := by
            simp only [← LinearMap.comp_assoc,
              LinearMap.lTensor_comp_map]
    _ = comul.lTensor _ ∘ₗ comul := rfl

@[reducible, instance]
noncomputable def MulOpposite.coalgebra
  {R A : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A]
  [Coalgebra R A] : Coalgebra R Aᵐᵒᵖ where
    coassoc := MulOpposite_coassoc
    rTensor_counit_comp_comul := by
        rw [comul_def', counit_def, ← LinearMap.comp_assoc,
          LinearMap.rTensor_comp_map, LinearMap.comp_assoc,
          LinearEquiv.symm_comp, LinearMap.comp_id,
          ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc]
        nth_rw 2 [← LinearMap.comp_assoc]
        rw [Coalgebra.rTensor_counit_comp_comul]
        rfl
    lTensor_counit_comp_comul := by
        rw [comul_def', counit_def, ← LinearMap.comp_assoc,
          LinearMap.lTensor_comp_map, LinearMap.comp_assoc,
          LinearEquiv.symm_comp, LinearMap.comp_id,
          ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc]
        nth_rw 2 [← LinearMap.comp_assoc]
        rw [Coalgebra.lTensor_counit_comp_comul]
        rfl
