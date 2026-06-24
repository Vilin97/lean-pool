/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.End

/-!
 # One lemma of the spectrum of a linear map

 This file just proves that the spectrum of a linear map is commutative.
-/


theorem isUnit_comm (K E : Type _) [DivisionRing K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (x y : E →ₗ[K] E) : IsUnit (x ∘ₗ y) ↔ IsUnit (y ∘ₗ x) := by
  simp_rw [← Module.End.mul_eq_comp]
  constructor
  all_goals
    intro h
    rw [← nonempty_invertible_iff_isUnit] at h ⊢
    refine Nonempty.intro ?_
    obtain ⟨z, hz1, hz2⟩ := Nonempty.some h
    apply @invertibleMul _ _ _ _ ?_ ?_
    rw [mul_assoc, mul_eq_one_comm, mul_assoc] at hz2
    rw [← mul_assoc] at hz1
  any_goals apply Invertible.mk (z * x) hz1 hz2
  any_goals apply Invertible.mk (z * y) hz1 hz2
  all_goals
    rw [mul_eq_one_comm, mul_assoc] at hz1
    rw [mul_assoc, mul_eq_one_comm] at hz2
  · exact Invertible.mk (y * z) hz2 hz1
  · exact Invertible.mk (x * z) hz2 hz1

theorem isUnit_neg {α : Type _} [Monoid α] [HasDistribNeg α] (x : α) : IsUnit (-x) ↔ IsUnit x := by
  constructor
  all_goals
    intro h
    rw [← nonempty_invertible_iff_isUnit] at h ⊢
    refine Nonempty.intro ?_
    obtain ⟨z, hz1, hz2⟩ := Nonempty.some h
  any_goals
    rw [neg_mul_comm] at hz2
    rw [← neg_mul_comm] at hz1
    exact ⟨-z, hz1, hz2⟩
  any_goals
    rw [← neg_mul_neg] at hz2
    rw [← neg_mul_neg] at hz1
    exact ⟨-z, hz1, hz2⟩

theorem spectrum.comm {K E : Type _} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (x y : E →ₗ[K] E) : spectrum K (x ∘ₗ y) = spectrum K (y ∘ₗ x) := by
  ext1 u
  by_cases Hu : u = 0
  · simp_rw [spectrum.mem_iff, Hu, Algebra.algebraMap_eq_smul_one, zero_smul, zero_sub, isUnit_neg,
      isUnit_comm]
  simp_rw [← Module.End.hasEigenvalue_iff_mem_spectrum, ←
    Module.End.has_eigenvector_iff_hasEigenvalue, LinearMap.comp_apply]
  constructor <;> rintro ⟨v, ⟨h, hv⟩⟩
  on_goal 1 => use y v
  on_goal 2 => use x v
  all_goals
    rw [h, _root_.map_smul, eq_self_iff_true, true_and]
    intro H
    rw [H, map_zero, eq_comm, smul_eq_zero] at h
    simp_rw [Hu, hv, false_or] at h
