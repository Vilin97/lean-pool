/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor product associator compatibility

This file restores an upstream tensor-product associator over mixed scalar towers.
-/

open scoped TensorProduct

/-- An algebra equivalence reassociating tensor products over two scalar towers. -/
def Algebra.TensorProduct.assoc' (R S R' A B C : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [Semiring A] [Semiring B] [Semiring C] [Algebra R R'] [Algebra R A]
    [Algebra R' A] [Algebra R B] [Algebra R' B] [Algebra R C]
    [IsScalarTower R R' A] [IsScalarTower R R' B] [Algebra S A] [Algebra R S] [Algebra R' S]
    [IsScalarTower R' S A] [IsScalarTower R S A] :
    (A ⊗[R'] B) ⊗[R] C ≃ₐ[S] A ⊗[R'] (B ⊗[R] C) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.assoc _ _ _ _ _ _)
    rfl (LinearMap.map_mul_iff _|>.2 <| by ext; simp)

@[simp]
lemma Algebra.TensorProduct.assoc'_apply (R S R' A B C : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [Semiring A] [Semiring B] [Semiring C] [Algebra R R'] [Algebra R A]
    [Algebra R' A] [Algebra R B] [Algebra R' B] [Algebra R C]
    [IsScalarTower R R' A] [IsScalarTower R R' B] [Algebra S A] [Algebra R S] [Algebra R' S]
    [IsScalarTower R' S A] [IsScalarTower R S A] (a : A) (b : B) (c : C) :
    (Algebra.TensorProduct.assoc' R S R' A B C) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) := rfl
