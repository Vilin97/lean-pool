/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.EuclideanDomain.Field

/-!
# Commutators of linear maps

This file defines commutators of linear operators, and proves a few useful properties of them.

## Main definitions

* `LinearMap.commutator`: The commutator `[A,B] := AB-BA` of two linear operators `A`, `B`.
* `LinearMap.commutatorBilin`: The commutator `[⬝,⬝]` as a bilinear map on the space of linear maps.

-/

namespace LinearMap



section commutator

variable {𝕜 : Type*} [Semiring 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- Commutator `[A,B] := AB-BA` of two linear operators `A`, `B`. -/
def commutator (A B : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  A * B - B * A

/-- `[A,B] = -[B,A]` -/
lemma commutator_comm (A B : V →ₗ[𝕜] V) :
    A.commutator B = - B.commutator A := by
  simp [LinearMap.commutator]

lemma mul_eq_mul_add_commutator (A B : V →ₗ[𝕜] V) :
    A * B = B * A + A.commutator B := by
  simp [LinearMap.commutator]

/-- `[AB,C] = A[B,C] + [A,C]B` -/
lemma commutator_pair (A B C : V →ₗ[𝕜] V) :
    (A * B).commutator C = A * B.commutator C + A.commutator C * B := by
  calc  A * B * C - C * (A * B)
    _ = A * B * C - A * C * B + A * C * B - C * A * B     := by simp [← mul_assoc]
    _ = A * (B * C - C * B) + (A * C - C * A) * B         := by simp [mul_sub, sub_mul, ← mul_assoc]

/-- `[A,BC] = B[A,C] + [A,B]C` -/
lemma commutator_pair' (A B C : V →ₗ[𝕜] V) :
    A.commutator (B * C) = B * A.commutator C + A.commutator B * C := by
  calc  A * (B * C) - B * C * A
    _ = A * B * C - B * A * C + B * A * C - B * C * A     := by simp [← mul_assoc]
    _ = B * (A * C - C * A) + (A * B - B * A) * C         := by simp [mul_sub, sub_mul, ← mul_assoc]

@[simp] lemma commutator_smul_one {𝕜 : Type*} [Field 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]
    (A : V →ₗ[𝕜] V) (c : 𝕜) :
    A.commutator (c • 1) = 0 := by
  simp [LinearMap.commutator]

@[simp] lemma smul_one_commutator {𝕜 : Type*} [Field 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]
    (A : V →ₗ[𝕜] V) (c : 𝕜) :
    (c • 1 : V →ₗ[𝕜] V).commutator A = 0 := by
  simp [LinearMap.commutator]

end commutator



section commutatorBilin

variable {𝕜 : Type*} [Field 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]

/-- Commutator `[⬝,⬝]` as a bilinear map on the space of linear maps. -/
noncomputable def _root_.LinearMap.commutatorBilin :
    (V →ₗ[𝕜] V) →ₗ[𝕜] (V →ₗ[𝕜] V) →ₗ[𝕜] (V →ₗ[𝕜] V) where
  toFun A :=
    { toFun := fun B ↦ A.commutator B
      map_add' B₁ B₂ := by
        simp [LinearMap.commutator, mul_add, add_mul, sub_eq_add_neg]
        ac_rfl
      map_smul' c B := by simp [LinearMap.commutator, smul_sub] }
  map_add' A₁ A₂ := by
    ext1 B
    simp [LinearMap.commutator, add_mul, mul_add, sub_eq_add_neg]
    ac_rfl
  map_smul' c A := by
    ext1 B
    simp [LinearMap.commutator, smul_sub]

variable {V}
@[simp] lemma _root_.LinearMap.commutatorBilin_apply₂ (A B : V →ₗ[𝕜] V) :
    LinearMap.commutatorBilin V A B = A.commutator B := rfl

end commutatorBilin



section algebra_commutator

variable (𝕜 : Type*) {A : Type*} [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Commutator with a fixed element in a `𝕜`-algebra as a `𝕜`-linear map. -/
def _root_.LinearMap.algebraCommutator' (a : A) : A →ₗ[𝕜] A where
  toFun b := a * b - b * a
  map_add' b₁ b₂ := by
    simp only [mul_add, add_mul, sub_eq_add_neg, neg_add_rev]
    ac_rfl
  map_smul' r b := by
    rw [smul_sub]
    congr <;> simp

lemma _root_.LinearMap.algebraCommutator'_apply (a : A) (b : A) :
    algebraCommutator' 𝕜 a b = a * b - b * a :=
  rfl

/-- Commutator in a `𝕜`-algebra as a `𝕜`-bilinear linear map. -/
def _root_.LinearMap.algebraCommutator : A →ₗ[𝕜] A →ₗ[𝕜] A where
  toFun := algebraCommutator' 𝕜
  map_add' a₁ a₂ := by
    ext b
    simp only [algebraCommutator'_apply,
               add_mul, mul_add, sub_eq_add_neg, neg_add_rev, ← add_assoc, add_apply]
    ac_rfl
  map_smul' r a := by
    ext b
    simp [algebraCommutator'_apply, smul_sub]

end algebra_commutator

end LinearMap -- namespace
