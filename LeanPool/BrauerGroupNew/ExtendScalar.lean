/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.RingTheory.TensorProduct.Basic

/-!
# LeanPool.BrauerGroupNew.ExtendScalar

Imported Lean Pool material for `LeanPool.BrauerGroupNew.ExtendScalar`.
-/

open scoped TensorProduct

universe u
variable (k K L A : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
  [Algebra k L] [Ring A] [Algebra k A] [IsScalarTower k K L]

/-- Additive map sending `l ⊗ a` to `l ⊗ (1 ⊗ a)` after releasing scalars through `K`. -/
def releaseAddHom : L ⊗[k] A →+ L ⊗[K] (K ⊗[k] A) :=
  TensorProduct.liftAddHom
  {
    toFun l := {
      toFun a := l ⊗ₜ[K] (1 ⊗ₜ[k] a)
      map_zero' := by simp only [TensorProduct.tmul_zero]
      map_add' _ _ := by simp_rw [TensorProduct.tmul_add]
    }
    map_zero' := by simp only [TensorProduct.zero_tmul]; rfl
    map_add' x y := by
      ext a'
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
      repeat rw [TensorProduct.add_tmul]
  } fun r l a ↦ by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.tmul_smul]; rfl
/-- Algebra homomorphism releasing an `L ⊗[k] A` tensor through `K`. -/
def release : L ⊗[k] A →ₐ[L] L ⊗[K] (K ⊗[k] A) where
  __ := releaseAddHom k K L A
  map_one' := by simp only [releaseAddHom, Algebra.TensorProduct.one_def, ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, ZeroHom.toFun_eq_coe, map_zero, AddMonoidHom.toZeroHom_coe]
    | tmul l a =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, ZeroHom.toFun_eq_coe, map_zero, AddMonoidHom.toZeroHom_coe]
      | tmul l' a' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, ZeroHom.toFun_eq_coe,
          AddMonoidHom.toZeroHom_coe]
        change (l * l') ⊗ₜ[K] (1 ⊗ₜ[k] (a * a')) = (l ⊗ₜ[K] (1 ⊗ₜ[k] a)) * (l' ⊗ₜ[K] (1 ⊗ₜ[k] a'))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      | add x y hx hy =>
        simp only [mul_add, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
        change releaseAddHom k K L A _ = releaseAddHom k K L A _ * releaseAddHom k K L A _ at hx
        change releaseAddHom k K L A _ = releaseAddHom k K L A _ * releaseAddHom k K L A _ at hy
        rw [hx, hy]
    | add z w hz hw =>
      simp only [add_mul, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe] at hw hz ⊢
      rw [hz, hw]
  commutes' := fun l ↦ by
    simp only [Algebra.TensorProduct.algebraMap_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Algebra.TensorProduct.one_def]; rfl

/-- Linear map sending `m ⊗ a` to `(m • l) ⊗ a`. -/
def absorbMap (l : L) : K ⊗[k] A →ₗ[k] L ⊗[k] A :=
  TensorProduct.lift {
    toFun := fun m ↦ {
      toFun := fun a ↦ (m • l) ⊗ₜ[k] a
      map_add' := fun _ _ ↦ by simp only [TensorProduct.tmul_add]
      map_smul' := fun _ _ ↦ by simp [TensorProduct.tmul_smul, RingHom.id_apply]
    }
    map_add' := fun _ _ ↦ by ext; simp only [add_smul, TensorProduct.add_tmul,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    map_smul' := fun _ _ ↦ by ext; simp only [smul_assoc, ← TensorProduct.smul_tmul',
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
  }

/-- Additive map absorbing the intermediate `K` tensor factor into `L`. -/
def absorbAddHom : L ⊗[K] (K ⊗[k] A) →+ L ⊗[k] A :=
  TensorProduct.liftAddHom
  {
    toFun l := absorbMap k K L A l
    map_zero' := by
      ext x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x a =>
        change (x • 0) ⊗ₜ a = 0
        simp only [smul_zero, TensorProduct.zero_tmul]
      | add x y hx hy =>
        simp_all only [AddMonoidHom.zero_apply, map_add, add_zero]
    map_add' := fun x y ↦ by
      ext z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul m a =>
        change (m • (x + y)) ⊗ₜ a = (m • x) ⊗ₜ a + (m • y) ⊗ₜ a
        simp only [smul_add, TensorProduct.add_tmul]
      | add z w hz hw =>
        simp only [AddMonoidHom.add_apply] at hz hw
        simp only [map_add, AddMonoidHom.add_apply, hz, hw]
  } (fun r l a ↦ by
    induction a using TensorProduct.induction_on with
    | zero => simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zero, smul_zero]
    | tmul m a =>
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.smul_tmul']
      change (m • (r • l)) ⊗ₜ a = ((r • m) • l) ⊗ₜ a
      rw [← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul]
    | add x y hx hy =>
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hx hy
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, hx, hy, smul_add]
    )

/-- Algebra homomorphism inverse to `release`, absorbing the intermediate `K` tensor factor. -/
def absorb : L ⊗[K] (K ⊗[k] A) →ₐ[L] L ⊗[k] A where
  __ := absorbAddHom k K L A
  map_one' := by
    simp only [Algebra.TensorProduct.one_def, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    change (1 • 1) ⊗ₜ (1 : A) = _
    rw [one_smul]
  map_mul' := fun x y ↦ by
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero]
    | add x' y' hx hy => simp only [add_mul, map_add, hx, hy]
    | tmul l ka =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
    | tmul l' ka' =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul]
    induction ka' using TensorProduct.induction_on with
    | zero => simp only [mul_zero, TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [mul_add, TensorProduct.tmul_add, map_add, hx, hy]
    | tmul k' a =>
    induction ka using TensorProduct.induction_on with
    | zero => simp only [zero_mul, TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [add_mul, TensorProduct.tmul_add, map_add, hx, hy]
    | tmul k1 a1 =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul]
    change ((k1 * k') • (l * l')) ⊗ₜ (a1 * a) = (k1 • l) ⊗ₜ a1 * (k' • l') ⊗ₜ a
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc]
    rw [← smul_assoc, smul_eq_mul, mul_comm]
  commutes' := fun l ↦ by
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def]
    change (1 • l) ⊗ₜ (1 : A) = l ⊗ₜ 1
    rw [one_smul]

/-- Algebra equivalence between direct scalar extension and extension through the intermediate
field. -/
def absorbEqv : L ⊗[k] A ≃ₐ[L] L ⊗[K] (K ⊗[k] A) where
  toFun := release k K L A
  invFun := absorb k K L A
  left_inv := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul l a =>
      change (absorb k K L A) (l ⊗ₜ[K] (1 ⊗ₜ a)) = _
      change (1 • l) ⊗ₜ _ = _
      rw [one_smul]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  right_inv := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul l ka =>
      induction ka using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul k' a =>
        change (release k K L A) ((k' • l) ⊗ₜ a) = _
        change (k' • l) ⊗ₜ[K] (1 ⊗ₜ a) = _
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := release k K L A|>.commutes

theorem absorbEqv_apply (l : L) (a : A) : absorbEqv k K L A (l ⊗ₜ a) = l ⊗ₜ[K] (1 ⊗ₜ a) :=
  rfl
