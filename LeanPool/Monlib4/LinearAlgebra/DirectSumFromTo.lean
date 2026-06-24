/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Pi
-- import Mathlib.LinearAlgebra.ProjectiveSpace.Basic
import LeanPool.Monlib4.Preq.Ites

/-!

# Direct sum from _ to _

 This file includes the definition of `direct_sum_from_to`, a linear map from `M i` to `M j`.

-/


/-- Composition of the `i`-th injection and the `j`-th projection of a dependent
direct sum, giving a linear map `M₁ i →ₗ[R] M₁ j`. -/
def directSumFromTo {R : Type*} [Semiring R] {ι₁ : Type*} [DecidableEq ι₁] {M₁ : ι₁ → Type*}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₁ : ι₁, Module R (M₁ i₁)] (i j : ι₁) : M₁ i →ₗ[R] M₁ j :=
  LinearMap.proj j ∘ₗ LinearMap.single _ _ i

theorem directSumFromTo_apply_same {R : Type _} [Semiring R] {ι₁ : Type _} [DecidableEq ι₁]
    {M₁ : ι₁ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₁ : ι₁, Module R (M₁ i₁)] (i : ι₁) :
    directSumFromTo i i = (1 : M₁ i →ₗ[R] M₁ i) := by
  ext1 x
  simp [directSumFromTo]

theorem directSumFromTo_apply_ne_same {R : Type _} [Semiring R] {ι₁ : Type _} [DecidableEq ι₁]
    {M₁ : ι₁ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₁ : ι₁, Module R (M₁ i₁)] {i j : ι₁}
    (h : j ≠ i) : directSumFromTo i j = (0 : M₁ i →ₗ[R] M₁ j) := by
  ext1 x
  simp [directSumFromTo, h]
