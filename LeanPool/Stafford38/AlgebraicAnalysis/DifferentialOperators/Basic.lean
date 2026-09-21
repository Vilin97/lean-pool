/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Finite-order differential operators

Neutral extraction of the intrinsic finite-order differential-operator algebra
from Stafford38 commit `1585e4c7`, originally
`Stafford38/DifferentialOperators.lean`.  No Weyl presentation or
application-specific hypothesis is used.
-/

namespace AlgebraicAnalysis.DifferentialOperators

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- `k`-linear endomorphisms of the `k`-algebra `R`. -/
abbrev End := Module.End k R

/-- Multiplication by an element of `R`, as a `k`-linear endomorphism. -/
def multiplication (a : R) : End (k := k) (R := R) :=
  LinearMap.mulLeft k a

@[simp]
theorem multiplication_apply (a x : R) :
    multiplication (k := k) a x = a * x := rfl

/-- The commutator of an endomorphism with multiplication by `a`. -/
def commutator (P : End (k := k) (R := R)) (a : R) : End (k := k) (R := R) :=
  P * multiplication (k := k) a - multiplication (k := k) a * P

@[simp]
theorem commutator_apply (P : End (k := k) (R := R)) (a x : R) :
    commutator P a x = P (a * x) - a * P x := rfl

/-- Differential operators of order at most `n`. -/
def order : ℕ → Submodule k (End (k := k) (R := R))
  | 0 =>
      { carrier := {P | ∀ a, commutator P a = 0}
        zero_mem' := by simp [commutator]
        add_mem' := by
          intro P Q hP hQ a
          have heq : commutator (P + Q) a = commutator P a + commutator Q a := by
            ext x
            simp [commutator_apply, mul_add, sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm]
          calc
            commutator (P + Q) a = commutator P a + commutator Q a := heq
            _ = 0 := by rw [hP a, hQ a, add_zero]
        smul_mem' := by
          intro c P hP a
          have heq : commutator (c • P) a = c • commutator P a := by
            ext x
            simp [commutator_apply, smul_sub]
          rw [heq, hP a, smul_zero] }
  | n + 1 =>
      { carrier := {P | ∀ a, commutator P a ∈ order n}
        zero_mem' := by simp [commutator]
        add_mem' := by
          intro P Q hP hQ a
          have heq : commutator (P + Q) a = commutator P a + commutator Q a := by
            ext x
            simp [commutator_apply, mul_add, sub_eq_add_neg, add_assoc, add_comm,
              add_left_comm]
          rw [heq]
          exact (order n).add_mem (hP a) (hQ a)
        smul_mem' := by
          intro c P hP a
          have heq : commutator (c • P) a = c • commutator P a := by
            ext x
            simp [commutator_apply, smul_sub]
          rw [heq]
          exact (order n).smul_mem c (hP a) }

@[simp]
theorem mem_order_zero_iff (P : End (k := k) (R := R)) :
    P ∈ order (k := k) (R := R) 0 ↔ ∀ a, commutator P a = 0 := Iff.rfl

@[simp]
theorem mem_order_succ_iff (P : End (k := k) (R := R)) (n : ℕ) :
    P ∈ order (k := k) (R := R) (n + 1) ↔
      ∀ a, commutator P a ∈ order n := by
  change (∀ a, commutator P a ∈ order n) ↔ _
  rfl

theorem mem_order_zero_iff_eq_multiplication (P : End (k := k) (R := R)) :
    P ∈ order (k := k) (R := R) 0 ↔
      P = multiplication (k := k) (P 1) := by
  constructor
  · intro h
    ext a
    have ha := LinearMap.congr_fun (h a) 1
    simpa [mul_comm] using sub_eq_zero.mp (by simpa [commutator_apply] using ha)
  · intro hP
    rw [mem_order_zero_iff]
    intro a
    rw [hP]
    ext x
    simp [commutator_apply, mul_assoc, mul_comm]

theorem order_mono_step (n : ℕ) :
    order (k := k) (R := R) n ≤ order (n + 1) := by
  induction n with
  | zero =>
      intro P hP
      rw [mem_order_succ_iff]
      intro a
      rw [hP a]
      exact (order 0).zero_mem
  | succ n ih =>
      intro P hP
      rw [mem_order_succ_iff] at hP ⊢
      intro a
      exact ih (hP a)

theorem order_mono {m n : ℕ} (h : m ≤ n) :
    order (k := k) (R := R) m ≤ order n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (order_mono_step n)

theorem commutator_mul (P Q : End (k := k) (R := R)) (a : R) :
    commutator (P * Q) a = P * commutator Q a + commutator P a * Q := by
  ext x
  simp [commutator_apply, Module.End.mul_apply]

private theorem orderZero_mul {P Q : End (k := k) (R := R)} {n : ℕ}
    (hP : P ∈ order (k := k) (R := R) 0) (hQ : Q ∈ order n) :
    P * Q ∈ order n := by
  induction n generalizing Q with
  | zero =>
      rw [mem_order_zero_iff_eq_multiplication] at hP hQ
      rw [mem_order_zero_iff]
      intro a
      rw [hP, hQ]
      ext x
      simp [commutator_apply, mul_assoc, mul_comm, mul_left_comm]
  | succ n ih =>
      rw [mem_order_succ_iff] at hQ ⊢
      intro a
      rw [commutator_mul, hP a, zero_mul, add_zero]
      exact ih (hQ a)

/-- Orders add under composition. -/
theorem mul_mem_order {P Q : End (k := k) (R := R)} {m n : ℕ}
    (hP : P ∈ order (k := k) (R := R) m) (hQ : Q ∈ order n) :
    P * Q ∈ order (m + n) := by
  induction m generalizing P n Q with
  | zero => simpa using orderZero_mul hP hQ
  | succ m ihm =>
      induction n generalizing P Q with
      | zero =>
          rw [Nat.add_zero, mem_order_succ_iff] at hP ⊢
          intro a
          rw [commutator_mul, hQ a, mul_zero, zero_add]
          simpa using ihm (hP a) hQ
      | succ n ihn =>
          have hQ' : Q ∈ order (n + 1) := hQ
          rw [mem_order_succ_iff] at hP hQ
          rw [Nat.add_succ, mem_order_succ_iff]
          intro a
          rw [commutator_mul]
          exact (order ((m + 1) + n)).add_mem
            (ihn hP (hQ a))
            (by simpa only [Nat.succ_add, Nat.add_succ] using ihm (hP a) hQ')

/-- The algebra of all finite-order `k`-linear differential operators on `R`. -/
def algebra : Subalgebra k (End (k := k) (R := R)) where
  carrier := {P | ∃ n, P ∈ order n}
  zero_mem' := ⟨0, (order 0).zero_mem⟩
  add_mem' := by
    rintro P Q ⟨m, hP⟩ ⟨n, hQ⟩
    refine ⟨max m n, (order (max m n)).add_mem ?_ ?_⟩
    · exact order_mono (Nat.le_max_left _ _) hP
    · exact order_mono (Nat.le_max_right _ _) hQ
  mul_mem' := by
    rintro P Q ⟨m, hP⟩ ⟨n, hQ⟩
    exact ⟨m + n, mul_mem_order hP hQ⟩
  one_mem' := by
    refine ⟨0, (mem_order_zero_iff_eq_multiplication _).2 ?_⟩
    ext x
    simp [multiplication_apply]
  algebraMap_mem' := by
    intro c
    refine ⟨0, (mem_order_zero_iff_eq_multiplication _).2 ?_⟩
    ext x
    simp [multiplication_apply]

@[simp]
theorem mem_algebra_iff (P : End (k := k) (R := R)) :
    P ∈ algebra (k := k) (R := R) ↔ ∃ n, P ∈ order n := Iff.rfl

/-! The two basic kinds of operators are finite-order without any geometric
assumption.  Keeping these witnesses public lets a concrete carrier expose
its coefficient and derivation generators through this neutral API. -/

/-- Multiplication by a coefficient is an intrinsic differential operator of
order zero. -/
theorem multiplication_mem_algebra (a : R) :
    multiplication (k := k) a ∈ algebra (k := k) (R := R) := by
  refine ⟨0, (mem_order_zero_iff_eq_multiplication _).2 ?_⟩
  ext x
  simp [multiplication_apply]

end AlgebraicAnalysis.DifferentialOperators
