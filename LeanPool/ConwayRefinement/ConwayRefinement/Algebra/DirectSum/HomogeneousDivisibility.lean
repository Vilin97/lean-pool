/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.DirectSum.Ring

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Divisibility by homogeneous elements in graded direct sums

Multiplication by an element supported in grade `i` shifts every component by `i`. When addition
of grades is left-cancellative, this identifies the component at `i + j` with the product of the
homogeneous element and the component at `j`. Consequently, a homogeneous element divides a
graded sum if and only if it divides every homogeneous component.
-/

universe u v

public noncomputable section

open scoped DirectSum

namespace DirectSum

variable {ι : Type u} (A : ι → Type v)
  [DecidableEq ι] [AddCommMonoid ι] [IsLeftCancelAdd ι]
  [∀ i, AddCommMonoid (A i)] [DirectSum.GSemiring A]

theorem of_mul_apply_add {i : ι} (a : A i) (x : DirectSum ι A) (j : ι) :
    (DirectSum.of A i a * x) (i + j) =
      GradedMonoid.GMul.mul a (x j) := by
  induction x using DirectSum.induction_on with
  | zero =>
      rw [mul_zero]
      exact (DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := A) a).symm
  | of k b =>
      by_cases hkj : k = j
      · subst k
        rw [DirectSum.of_mul_of, DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [DirectSum.of_mul_of]
        rw [DirectSum.of_eq_of_ne k j b (Ne.symm hkj)]
        rw [DirectSum.GNonUnitalNonAssocSemiring.mul_zero]
        rw [DirectSum.of_eq_of_ne]
        exact fun h ↦ hkj (add_left_cancel h).symm
  | add x y hx hy =>
      rw [mul_add, add_apply, add_apply, hx, hy]
      exact (DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := A) a (x j) (y j)).symm

omit [IsLeftCancelAdd ι] in
theorem of_mul_apply_eq_zero_of_not_exists {i k : ι} (a : A i)
    (x : DirectSum ι A) (h : ¬∃ j, i + j = k) :
    (DirectSum.of A i a * x) k = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j b =>
      rw [DirectSum.of_mul_of]
      rw [DirectSum.of_eq_of_ne]
      exact fun hij ↦ h ⟨j, hij.symm⟩
  | add x y hx hy =>
      rw [mul_add, add_apply, hx, hy, add_zero]

/-- A homogeneous element divides a graded sum if and only if it divides every component. -/
theorem of_dvd_iff_dvd_components {i : ι} (a : A i) (x : DirectSum ι A) :
    DirectSum.of A i a ∣ x ↔
      ∀ k, DirectSum.of A i a ∣ DirectSum.of A k (x k) := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ k
    by_cases h : ∃ j, i + j = k
    · obtain ⟨j, rfl⟩ := h
      refine ⟨DirectSum.of A j (y j), ?_⟩
      rw [DirectSum.of_mul_of, of_mul_apply_add]
    · rw [of_mul_apply_eq_zero_of_not_exists A a y h, map_zero]
      exact dvd_zero _
  · intro h
    rw [← DirectSum.sum_support_of x]
    exact Finset.dvd_sum fun k _ ↦ h k

end DirectSum
