/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.SchurMul
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.TensorProduct
import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Schur Multiplication on Tensor Products

This file relates Schur multiplication on tensor-product coalgebras to the
fourfold tensor shuffle used by the Monlib4 quantum-set tensor product.
-/

open scoped TensorProduct

/-- The Mathlib tensor-product factor swap agrees with Monlib4's tensor shuffle. -/
lemma TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq_swapMiddleTensor
  {R A B C D : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] :
  (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R R R A B C D) =
    swapMiddleTensor R A B C D :=
by
  rw [← LinearEquiv.toLinearMap_inj]
  apply TensorProduct.ext_fourfold'
  simp

/-- Schur multiplication commutes with tensoring linear maps. -/
theorem TensorProduct.map_schurMul {A B C D : Type*}
  [AddCommMonoid A] [Semiring B]
  [AddCommMonoid C] [Semiring D]
  [Module ℂ A] [Module ℂ B]
  [Module ℂ C] [Module ℂ D]
  [Coalgebra ℂ A] [Coalgebra ℂ C]
  [SMulCommClass ℂ B B]
  [SMulCommClass ℂ D D]
  [IsScalarTower ℂ B B]
  [IsScalarTower ℂ D D]
  {f h : A →ₗ[ℂ] B} {g k : C →ₗ[ℂ] D} :
  (map f g) •ₛ (map h k) = map (f •ₛ h) (g •ₛ k) :=
by
  rw [schurMul_apply_apply, TensorProduct.comul_def, LinearMap.mul'_tensorProduct,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq_swapMiddleTensor]
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ _ (swapMiddleTensor _ _ _ _ _).toLinearMap]
  nth_rw 2 [← LinearMap.comp_assoc, LinearMap.comp_assoc, ← swapMiddleTensor_symm]
  rw [swapMiddleTensor_map_conj]
  simp only [← LinearMap.comp_assoc, ← TensorProduct.map_comp,
    TensorProduct.AlgebraTensorModule.map_eq]
  rfl
