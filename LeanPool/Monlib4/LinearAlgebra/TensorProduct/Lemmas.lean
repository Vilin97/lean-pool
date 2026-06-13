/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.TensorProduct.Maps
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import LeanPool.Monlib4.Preq.StarAlgEquiv

/-!
# Tensor-product map lemmas

This file contains compatibility lemmas and equivalences for tensor-product
maps used by the Monlib4 port.
-/

open scoped TensorProduct

theorem Algebra.TensorProduct.map_apply_map_apply {R : Type _} [CommSemiring R]
    {A B C D E F : Type _} [Semiring A] [Semiring B] [Semiring C] [Semiring D] [Semiring E]
    [Semiring F] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) (z : B →ₐ[R] E) (w : D →ₐ[R] F) (x : A ⊗[R] C) :
    (Algebra.TensorProduct.map z w) (Algebra.TensorProduct.map f g x) =
      Algebra.TensorProduct.map (z.comp f) (w.comp g) x :=
x.induction_on
  (map_zero _)
  (fun a b => by simp only [Algebra.TensorProduct.map_tmul]; rfl)
  (fun a b ha hb => by simp only [map_add, ha, hb])

theorem TensorProduct.map_apply_map_apply {R : Type _} [CommSemiring R] {A B C D E F : Type _}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [AddCommMonoid E]
    [AddCommMonoid F] [Module R A] [Module R B] [Module R C] [Module R D] [Module R E] [Module R F]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D) (z : B →ₗ[R] E) (w : D →ₗ[R] F) (x : A ⊗[R] C) :
    (TensorProduct.map z w) (TensorProduct.map f g x) = TensorProduct.map (z.comp f) (w.comp g) x :=
  by
  revert x
  simp_rw [← LinearMap.comp_apply, ← LinearMap.ext_iff]
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]

/-- Tensor two algebra equivalences. -/
noncomputable def AlgEquiv.TensorProduct.map {R : Type _} [CommSemiring R] {A B C D : Type _}
    [Semiring A] [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B]
    [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[R] B ⊗[R] D
    where
  toFun x := Algebra.TensorProduct.map f.toAlgHom g.toAlgHom x
  invFun x := Algebra.TensorProduct.map f.symm.toAlgHom g.symm.toAlgHom x
  left_inv x := by
    simp_rw [Algebra.TensorProduct.map_apply_map_apply, AlgEquiv.symm_comp,
      Algebra.TensorProduct.map_id, AlgHom.id_apply]
  right_inv x := by
    simp_rw [Algebra.TensorProduct.map_apply_map_apply, AlgEquiv.comp_symm,
      Algebra.TensorProduct.map_id, AlgHom.id_apply]
  map_add' x y := by simp_rw [map_add]
  map_mul' x y := by simp_rw [_root_.map_mul]
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one, _root_.map_smul, _root_.map_one]

@[simp]
lemma AlgEquiv.TensorProduct.map_tmul {R : Type _} [CommSemiring R] {A B C D : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x : A) (y : C) :
  AlgEquiv.TensorProduct.map f g (x ⊗ₜ[R] y) = f x ⊗ₜ[R] g y :=
rfl

/-- Tensor two linear equivalences. -/
@[simps!]
noncomputable def LinearEquiv.TensorProduct.map {R : Type _} [CommSemiring R] {A B C D : Type _}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A]
    [Module R B] [Module R C] [Module R D] (f : A ≃ₗ[R] B) (g : C ≃ₗ[R] D) :
    A ⊗[R] C ≃ₗ[R] B ⊗[R] D
    where
  toFun x := _root_.TensorProduct.map f.toLinearMap g.toLinearMap x
  invFun x := _root_.TensorProduct.map f.symm.toLinearMap g.symm.toLinearMap x
  left_inv x := by
    induction x using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [_root_.TensorProduct.map_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  right_inv x := by
    induction x using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [_root_.TensorProduct.map_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  map_add' x y := (_root_.TensorProduct.map f.toLinearMap g.toLinearMap).map_add x y
  map_smul' r x := (_root_.TensorProduct.map f.toLinearMap g.toLinearMap).map_smul r x


local notation
  f " ⊗ₘ " g => _root_.TensorProduct.map f g

@[simp]
lemma AlgEquiv.TensorProduct.map_toLinearMap
    {R : Type _} [CommSemiring R] {A B C D : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) :
  (AlgEquiv.TensorProduct.map f g).toLinearMap = f.toLinearMap ⊗ₘ g.toLinearMap :=
rfl
lemma AlgEquiv.TensorProduct.map_map_toLinearMap
  {R : Type _} [CommSemiring R] {A B C D E F : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Semiring E] [Semiring F]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (h : B ≃ₐ[R] E) (i : D ≃ₐ[R] F) (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x : A ⊗[R] C) :
  (AlgEquiv.TensorProduct.map h i) ((AlgEquiv.TensorProduct.map f g) x)
    = (AlgEquiv.TensorProduct.map (f.trans h) (g.trans i)) x := by
  simp only [TensorProduct.map, coe_mk, Algebra.TensorProduct.map_apply_map_apply,
    Equiv.coe_fn_mk]
  rfl

lemma AlgEquiv.TensorProduct.map_symm
  {R : Type _} [CommSemiring R] {B D E F : Type _}
    [Semiring B] [Semiring D] [Semiring E] [Semiring F]
    [Algebra R B] [Algebra R D] [Algebra R E] [Algebra R F]
    (h : B ≃ₐ[R] E) (i : D ≃ₐ[R] F) :
  (AlgEquiv.TensorProduct.map h i).symm
    = (AlgEquiv.TensorProduct.map h.symm i.symm) :=
rfl

lemma AlgEquiv.op_trans {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
  (AlgEquiv.op f).trans (AlgEquiv.op g) = AlgEquiv.op (f.trans g) :=
rfl
@[simp]
lemma AlgEquiv.op_one {R A : Type*} [CommSemiring R] [Semiring A]
  [Algebra R A] :
  AlgEquiv.op (1 : A ≃ₐ[R] A) = 1 :=
rfl

@[simp]
lemma AlgEquiv.TensorProduct.map_one {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] :
  AlgEquiv.TensorProduct.map (1 : A ≃ₐ[R] A) (1 : B ≃ₐ[R] B) = 1 := by
  rw [AlgEquiv.ext_iff]
  simp_rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
  simp only [map_toLinearMap, one_toLinearMap, _root_.TensorProduct.map_one]

lemma LinearEquiv.TensorProduct.map_tmul
  {R A B C D : Type*} [CommSemiring R] [AddCommMonoid A]
  [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A]
  [Module R B] [Module R C] [Module R D] (f : A ≃ₗ[R] B) (g : C ≃ₗ[R] D) (x : A) (y : C) :
  LinearEquiv.TensorProduct.map f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
by simp [LinearEquiv.TensorProduct.map, _root_.TensorProduct.map_tmul]

/-- Tensor an algebra equivalence on the left by a fixed algebra. -/
noncomputable def AlgEquiv.lTensor {R A B : Type*} (C : Type*) [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) :
  (C ⊗[R] A) ≃ₐ[R] (C ⊗[R] B) :=
Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
  (LinearEquiv.lTensor C f.toLinearEquiv)
  (by
    simp only [toLinearEquiv_apply, LinearEquiv.lTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.map_mul, implies_true])
  (by simp only [toLinearEquiv_apply, map_one, LinearEquiv.lTensor_tmul]; rfl)

lemma AlgEquiv.lTensor_tmul {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (x : C) (y : A) :
  (AlgEquiv.lTensor C f) (x ⊗ₜ[R] y) = x ⊗ₜ f (y) :=
rfl
lemma AlgEquiv.lTensor_symm_tmul {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (x : C) (y : B) :
  (AlgEquiv.lTensor C f).symm (x ⊗ₜ[R] y) = x ⊗ₜ f.symm (y) :=
rfl
