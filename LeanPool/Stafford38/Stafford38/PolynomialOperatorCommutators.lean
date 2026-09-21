/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.PolynomialDifferentialOperators

/-! Coordinate commutators on the intrinsic polynomial endomorphism ring. -/

namespace Stafford38.PolynomialOperatorCommutators

open Stafford38.DifferentialOperators

noncomputable section

variable (k : Type*) [Field k] (n : ℕ)

/-- The polynomial coefficient algebra for the operator commutator construction. -/
abbrev PolynomialRing := MvPolynomial (Fin n) k
/-- The algebra of linear operators on the polynomial coefficient algebra. -/
abbrev Operator := Module.End k (PolynomialRing k n)
/-- Linear endomorphisms of the space of polynomial operators. -/
abbrev OperatorEnd := Module.End k (Operator k n)

/-- The linear map sending an operator to its commutator with a coordinate multiplication. -/
def coordinateCommutator (i : Fin n) : OperatorEnd k n where
  toFun P := commutator P (MvPolynomial.X i)
  map_add' P Q := by
    apply LinearMap.ext
    intro f
    simp? [commutator_apply, sub_eq_add_neg]
    noncomm_ring
  map_smul' c P := by
    apply LinearMap.ext
    intro f
    simp [commutator_apply, smul_sub]

@[simp]
theorem coordinateCommutator_apply (i : Fin n) (P : Operator k n) :
    coordinateCommutator k n i P = commutator P (MvPolynomial.X i) := rfl

theorem coordinateCommutator_comm (i j : Fin n) :
    coordinateCommutator k n i * coordinateCommutator k n j =
      coordinateCommutator k n j * coordinateCommutator k n i := by
  apply LinearMap.ext
  intro P
  apply LinearMap.ext
  intro f
  simp [coordinateCommutator, commutator_apply, Module.End.mul_apply,
    mul_add,  sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm]
  abel

/-- The composition of coordinate-commutator maps in the order specified by a list. -/
def iteratedCoordinateCommutator (l : List (Fin n)) : OperatorEnd k n :=
  l.foldr (fun i T => coordinateCommutator k n i * T) 1

@[simp]
theorem iteratedCoordinateCommutator_nil :
    iteratedCoordinateCommutator k n [] = 1 := rfl

theorem iteratedCoordinateCommutator_cons (i : Fin n) (l : List (Fin n)) :
    iteratedCoordinateCommutator k n (i :: l) =
      coordinateCommutator k n i * iteratedCoordinateCommutator k n l := rfl

theorem iteratedCoordinateCommutator_append (l₁ l₂ : List (Fin n)) :
    iteratedCoordinateCommutator k n (l₁ ++ l₂) =
      iteratedCoordinateCommutator k n l₁ * iteratedCoordinateCommutator k n l₂ := by
  induction l₁ with
  | nil => simp
  | cons i l ih =>
      change coordinateCommutator k n i * iteratedCoordinateCommutator k n (l ++ l₂) = _
      rw [ih]
      rfl

theorem iteratedCoordinateCommutator_swap (i j : Fin n) (l : List (Fin n)) :
    iteratedCoordinateCommutator k n (i :: j :: l) =
      iteratedCoordinateCommutator k n (j :: i :: l) := by
  rw [iteratedCoordinateCommutator_cons, iteratedCoordinateCommutator_cons,
    iteratedCoordinateCommutator_cons, iteratedCoordinateCommutator_cons]
  rw [← mul_assoc, ← mul_assoc, coordinateCommutator_comm k n i j, mul_assoc]

theorem coordinateCommutator_order_lower {m : ℕ} (i : Fin n)
    (P : Operator k n) (hP : P ∈ order (k := k) (R := PolynomialRing k n) (m + 1)) :
    coordinateCommutator k n i P ∈ order (k := k) (R := PolynomialRing k n) m :=
  hP (MvPolynomial.X i)

theorem coordinateCommutator_order_zero (i : Fin n) (P : Operator k n)
    (hP : P ∈ order (k := k) (R := PolynomialRing k n) 0) :
    coordinateCommutator k n i P = 0 :=
  hP (MvPolynomial.X i)

/-- An iterated coordinate commutator lowers intrinsic order by its exact
list length.  The statement avoids truncated subtraction: the input order is
written as the desired residual order plus the number of commutators. -/
theorem iteratedCoordinateCommutator_order_lower (l : List (Fin n)) {m : ℕ}
    (P : Operator k n)
    (hP : P ∈ order (k := k) (R := PolynomialRing k n) (m + l.length)) :
    iteratedCoordinateCommutator k n l P ∈
      order (k := k) (R := PolynomialRing k n) m := by
  induction l generalizing m with
  | nil => simpa using hP
  | cons i l ih =>
      rw [iteratedCoordinateCommutator_cons, Module.End.mul_apply]
      apply coordinateCommutator_order_lower k n i
      apply ih (m := m + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hP

/-- More commutators than the intrinsic order annihilate an operator. -/
theorem iteratedCoordinateCommutator_eq_zero_of_length_gt {m : ℕ}
    (l : List (Fin n)) (P : Operator k n)
    (hP : P ∈ order (k := k) (R := PolynomialRing k n) m)
    (hl : m < l.length) :
    iteratedCoordinateCommutator k n l P = 0 := by
  induction l generalizing m P with
  | nil => simp at hl
  | cons i l ih =>
      simp only [List.length_cons] at hl
      rw [iteratedCoordinateCommutator_cons, Module.End.mul_apply]
      by_cases htail : m < l.length
      · rw [ih P hP htail]
        exact map_zero _
      · have hlen : l.length = m := by omega
        apply coordinateCommutator_order_zero k n i
        apply iteratedCoordinateCommutator_order_lower (k := k) (n := n) l
        simpa [hlen] using hP

/-- Coordinate commutators depend only on the multiset of coordinates in the
iteration list.  This is the order-independent interface needed to encode a
multiindex by any list containing the prescribed multiplicities. -/
theorem iteratedCoordinateCommutator_eq_of_perm {l₁ l₂ : List (Fin n)}
    (h : l₁.Perm l₂) :
    iteratedCoordinateCommutator k n l₁ =
      iteratedCoordinateCommutator k n l₂ := by
  induction h with
  | nil => rfl
  | cons i h ih =>
      rw [iteratedCoordinateCommutator_cons, iteratedCoordinateCommutator_cons, ih]
  | swap i j l => exact (iteratedCoordinateCommutator_swap k n i j l).symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end
end Stafford38.PolynomialOperatorCommutators
