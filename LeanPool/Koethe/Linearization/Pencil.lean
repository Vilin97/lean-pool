/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic.Ring
public import LeanPool.Koethe.Linearization.Basic

/-!
# Root-row pencils and the polynomial root-column argument

A finite homogeneous-linear system becomes a shared `Pencil` by multiplying its
output row by the central polynomial variable. If that matrix is nilpotent,
`1 - T` has a polynomial right inverse. Eliminating the internal entries of its
root column gives `q = 1 + X * C(x) * q`. The coefficients of this polynomial
are `x^n`, and their eventual vanishing proves nilpotence of `x`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace KoetheCounterexample
namespace Linearization

universe u v

/-- A polynomial right resolvent forces nilpotence, also in a noncommutative
ring and without assuming that the ring is nontrivial. -/
theorem nilpotent_of_polynomial_resolvent {R : Type v} [Ring R]
    (x : R) (q : Polynomial R)
    (hq : q = 1 + Polynomial.X * (Polynomial.C x * q)) : IsNilpotent x := by
  have hc : ∀ n : ℕ, q.coeff n = x ^ n := by
    intro n
    induction n with
    | zero =>
        have h := congrArg (fun p : Polynomial R => p.coeff 0) hq
        simpa using h
    | succ n ih =>
        have h := congrArg (fun p : Polynomial R => p.coeff (n + 1)) hq
        simpa [Polynomial.coeff_add, Polynomial.coeff_X_mul,
          Polynomial.coeff_C_mul, Polynomial.coeff_one, ih, pow_succ'] using h
  refine ⟨q.natDegree + 1, ?_⟩
  rw [← hc]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)

/-- Reindexing square matrices preserves products, zero, and one. -/
def submatrixHom {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Semiring A] (e : ι ≃ κ) :
    Matrix κ κ A →*₀ Matrix ι ι A where
  toFun M := M.submatrix e e
  map_zero' := rfl
  map_one' := Matrix.submatrix_one_equiv e
  map_mul' M N := (Matrix.submatrix_mul_equiv M N e e e).symm

variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]

namespace System

/-- The root is `none`; only its row contains `X`. -/
def matrix (S : System k) (a : Fin 3 → R) :
    Matrix (Option S.State) (Option S.State) (Polynomial R) :=
  fun i j => match i, j with
    | none, none => Polynomial.X * edge a S.head
    | none, some j => Polynomial.X * edge a (S.out j)
    | some i, none => edge a (S.input i)
    | some i, some j => edge a (S.step i j)

/-- Enumeration of the states with the shared root index `0`. -/
def indexEquiv (S : System k) : Fin (Fintype.card S.State + 1) ≃ Option S.State :=
  (finSuccEquiv _).trans (Equiv.optionCongr (Fintype.equivFin S.State).symm)

@[simp] theorem indexEquiv_zero (S : System k) : S.indexEquiv 0 = none := by
  simp [indexEquiv]

/-- Exactly the shared pencil API, with no scalar/identity edges. -/
def pencil (S : System k) : Pencil k (Fintype.card S.State) where
  scalar := fun i row col => match S.indexEquiv row, S.indexEquiv col with
    | none, _ => 0
    | some row, none => S.input row i
    | some row, some col => S.step row col i
  linear := fun i row col => match S.indexEquiv row, S.indexEquiv col with
    | none, none => S.head i
    | none, some col => S.out col i
    | some _, _ => 0
  linear_off_root := by
    intro i row col hrow
    have hr : S.indexEquiv row ≠ none := by
      intro h
      apply hrow
      apply S.indexEquiv.injective
      simpa using h
    cases he : S.indexEquiv row with
    | none => exact (hr he).elim
    | some r => rfl

/-- Evaluation agrees with the system matrix, including the exact order of
scalar coefficients, generator factors, and the central variable. -/
theorem lift_pencil (S : System k) (a : Fin 3 → R) :
    S.pencil.lift a = (S.matrix a).submatrix S.indexEquiv S.indexEquiv := by
  ext row col
  cases hr : S.indexEquiv row <;> cases hc : S.indexEquiv col <;>
    simp [Pencil.lift, pencil, Matrix.submatrix_apply, matrix, hr, hc, edge]

/-- Nilpotence transfers from the shared, finitely indexed pencil to the
same matrix indexed by the root and internal states. -/
theorem matrix_nil_of_pencil_nil (S : System k) (a : Fin 3 → R)
    (h : IsNilpotent (S.pencil.lift a)) : IsNilpotent (S.matrix a) := by
  rw [S.lift_pencil a] at h
  have hm := h.map (submatrixHom (A := Polynomial R) S.indexEquiv.symm)
  change IsNilpotent (((S.matrix a).submatrix S.indexEquiv S.indexEquiv).submatrix
    S.indexEquiv.symm S.indexEquiv.symm) at hm
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] using hm

end System

/-- Eliminate the internal entries of the root column of a polynomial right
inverse. Nilpotence is only used to obtain this right inverse. -/
theorem Represents.nil_of_matrix_nil {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (hT : IsNilpotent (S.matrix a)) : IsNilpotent x := by
  obtain ⟨Q, hQ⟩ := hT.isUnit_one_sub.exists_right_inv
  have hQ' : Q - S.matrix a * Q = 1 := by
    simpa only [sub_mul, one_mul] using hQ
  have hi : ∀ i, Q (some i) none = edge a (S.input i) * Q none none +
      ∑ j, edge a (S.step i j) * Q (some j) none := by
    intro i
    have h := congrArg (fun M => M (some i) none) hQ'
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_option, System.matrix, sub_eq_zero] using h
  have he := hS (Q none none) (fun j => Q (some j) none) hi
  have hr : Q none none = 1 + Polynomial.X * (Polynomial.C x * Q none none) := by
    have h := congrArg (fun M => M none none) hQ'
    have h' : Q none none - Polynomial.X * (Polynomial.C x * Q none none) = 1 := by
      simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply,
        Fintype.sum_option, System.matrix, mul_assoc, ← Finset.mul_sum,
        ← mul_add, he] using h
    exact sub_eq_iff_eq_add.mp h'
  exact nilpotent_of_polynomial_resolvent x (Q none none) hr

/-- Each finite linearization gives a single-row pencil whose nilpotence
implies nilpotence of the represented element. -/
theorem Represents.nil_of_pencil_nil {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (hT : IsNilpotent (S.pencil.lift a)) : IsNilpotent x :=
  hS.nil_of_matrix_nil (S.matrix_nil_of_pencil_nil a hT)

end Linearization
end KoetheCounterexample

end
